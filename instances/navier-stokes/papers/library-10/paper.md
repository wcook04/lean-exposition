
<!-- passage:front -->
# Library guide 10: Breakdown/CertCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) **10** [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.CertCell.HarmonicPressureLift` to `Breakdown.CertCell.ModeFlip` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.CertCell.HarmonicPressureLift

Identifies each permitted pressure-gradient label mode with its cosine spatial mode plus i times its sine spatial mode. Cylindrical frame averaging justifies this equality almost everywhere off the axis. Appendix B: cell-system construction and finite certificate analysis.

**Rotated coordinates equal frame values.** Proved result. Under the stated hypotheses, the coordinates after inverse rotation are the cylindrical frame coordinates. (`rot_neg_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L20)).

**Rotate a meridian point.** Proved result. Under the stated hypotheses, rotating a meridian point gives its cylindrical point. (`rot_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L25)).

**Frame coordinate as an inner product.** Proved result. Under the stated hypotheses, a frame component is the inner product with the corresponding frame vector. (`frameVec_eq_inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L30)).

**Frame coordinates commute with integrals.** Proved result. Under the stated hypotheses, taking a frame component commutes with the integrable vector integral. (`frameVec_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L34)).

**Frame coordinates respect scaling.** Proved result. Under the stated hypotheses, a real scalar factors out of each frame coordinate. (`frameVec_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L39)).

**Frame coordinates respect negation.** Proved result. Under the stated hypotheses, negating a vector negates its frame coordinates. (`frameVec_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L43)).

**Frame component norm bound.** Proved result. Under the stated hypotheses, the absolute value of each frame component is bounded by the vector norm. (`abs_frameVec_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L47)).

**Frame coordinates are continuous.** Proved result. Under the stated hypotheses, frame coordinates vary continuously with angle and vector. (`continuous_frameVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L51)).

**Angular cylinder map is continuous.** Proved result. Under the stated hypotheses, the cylindrical point varies continuously with the angle. (`continuous_cylPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L58)).

**Cylinder angle is periodic.** Proved result. Under the stated hypotheses, adding two pi to the cylinder angle leaves the point unchanged. (`cylPoint_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L66)).

**Move a periodic lower integral.** Proved result. Under the stated hypotheses, the two indicated full-period angular lower integrals agree. (`setLIntegral_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L70)).

**Cylinder map is jointly continuous.** Proved result. Under the stated hypotheses, the cylindrical point depends continuously on radius, height and angle. (`continuous_cylPoint_joint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L79)).

**Cylinder norm ignores angle.** Proved result. Under the stated hypotheses, the norm of a cylindrical point equals that of its meridian point. (`norm_cylPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L88)).

**Orbit lower integral is measurable.** Proved result. Under the stated hypotheses, the time-angular lower integral is measurable as a function of the meridian point. (`measurable_orbitLIntegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L93)).

**Spacetime integral in orbit coordinates.** Proved result. Under the stated hypotheses, the spacetime lower integral equals the orbit lower integral with radial Jacobian. (`lintegral_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L104)).

**Pressure is integrable on a.e. orbit.** Proved result. Under the stated hypotheses, the pressure-gradient field is integrable on the time-angular orbit for almost every positive-radius meridian point. (`ae_integrable_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L124)).

**Negative complex exponential.** Proved result. Under the stated hypotheses, the negative imaginary exponential is cosine minus i times sine. (`exp_neg_mul_I`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L233)).

**Phase exponential has norm one.** Proved result. Under the stated hypotheses, the exponential of the stated imaginary phase has norm one. (`norm_exp_neg_mul_I`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L240)).

**Frame component of cosine pressure.** Proved result. Under the stated hypotheses, the frame component of the cosine harmonic is its weighted time integral. (`frameVec_harmonicCos_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L244)).

**Frame component of sine pressure.** Proved result. Under the stated hypotheses, the frame component of the sine harmonic is its negative sine-weighted time integral. (`frameVec_harmonicSin_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L254)).

**Split the pressure orbit harmonic.** Proved result. Under the stated hypotheses, the spacetime Fourier integral splits into the angular cosine coefficient plus i times the angular sine coefficient. (`harmonic_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L264)).

**Lift the pressure-gradient modes.** Proved result. Under the stated hypotheses, each permitted pressure-gradient label mode equals its cosine spatial mode plus i times its sine spatial mode almost everywhere off the axis. (`harmonicPressureLift_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureLift.lean#L365)).

### Breakdown.CertCell.HarmonicPressureSquare

Controls square integrals of harmonic pressure coefficients and justifies swapping the relevant averages. The resulting estimate supplies the pressure integrability required by the harmonic lift. Appendix B: cell-system construction and finite certificate analysis.

**Square of a unit-interval integral.** Proved result. Under the stated hypotheses, the square of the lower integral on the unit interval is bounded by the integral of the square. (`sq_lintegral_unit_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L18)).

**Square bound for a coefficient.** Proved result. Under the stated hypotheses, the squared norm of the weighted coefficient is bounded by the time integral of the squared norm. (`coefficient_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L37)).

**Swap pressure measurability.** Proved result. Under the stated hypotheses, the pressure field remains almost everywhere strongly measurable after swapping time and space. (`pressure_swap_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L56)).

**Restrict pressure measurability.** Proved result. Under the stated hypotheses, the swapped pressure field is measurable for the stated restricted product measure. (`pressure_swap_measurable_restrict`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L60)).

**Cosine pressure is measurable.** Proved result. Under the stated hypotheses, the cosine pressure coefficient is almost everywhere strongly measurable. (`cos_coefficient_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L66)).

**Sine pressure is measurable.** Proved result. Under the stated hypotheses, the sine pressure coefficient is almost everywhere strongly measurable. (`sin_coefficient_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L75)).

**Pressure coefficient square is finite.** Proved result. Under the stated hypotheses, the pressure coefficient has finite squared-norm integral on the closed ball. (`ball_square_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L84)).

**Pressure harmonics have local L2 bounds.** Proved result. Under the stated hypotheses, cosine and sine pressure-gradient harmonics have finite square integral on every closed ball. (`harmonicPressureSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureSquare.lean#L106)).

### Breakdown.CertCell.HarmonicProfiles

Computes the angular and time profiles of harmonic lifts in cylindrical frames. Periodicity, orthogonality and differentiation identities connect these profiles to the finite label data. Appendix B: cell-system construction and finite certificate analysis.

**Rotation is periodic.** Proved result. Under the stated hypotheses, adding two pi to the rotation angle does not change the rotated point. (`rot_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L22)).

**Rotation preserves norm.** Proved result. Under the stated hypotheses, axial rotation preserves the spatial norm. (`norm_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L25)).

**Cylinder point as a rotation.** Proved result. Under the stated hypotheses, the cylindrical point equals the rotation of its meridian point. (`cylPoint_eq_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L33)).

**Frame vectors are periodic.** Proved result. Under the stated hypotheses, the frame vector is unchanged after adding two pi. (`frameUnit_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L38)).

**Frame vectors have norm one.** Proved result. Under the stated hypotheses, each cylindrical frame vector has norm one. (`norm_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L41)).

**Coordinate vector as a scalar multiple.** Proved result. Under the stated hypotheses, a single-coordinate vector equals its coordinate value times the unit vector. (`single_eq_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L46)).

**Frame vectors are continuous.** Proved result. Under the stated hypotheses, the frame vector is continuous in angle. (`continuous_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L50)).

**Inverse rotation gives frame components.** Proved result. Under the stated hypotheses, inverse rotation has the coordinates obtained by pairing with the frame vectors. (`rot_neg_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L53)).

**Rotate the coordinate basis.** Proved result. Under the stated hypotheses, rotating a coordinate unit vector gives the corresponding cylindrical frame vector. (`rot_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L58)).

**Frame vector component formula.** Proved result. Under the stated hypotheses, a frame vector component equals its inner product with the corresponding frame vector. (`frameVec_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L63)).

**Frame matrix component formula.** Proved result. Under the stated hypotheses, a frame matrix component pairs the matrix action on one frame vector with another. (`frameMat_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L66)).

**Frame second-derivative formula.** Proved result. Under the stated hypotheses, a frame second-derivative component is the stated nested frame-vector evaluation. (`frameThird_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L71)).

**Angular exponential is periodic.** Proved result. Under the stated hypotheses, the integer-frequency angular exponential is unchanged after adding two pi. (`exp_angle_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L76)).

**Split time and angular phases.** Proved result. Under the stated hypotheses, the Fourier phase factors into its angular exponential and cosine-minus-i-sine time factor. (`expFactor_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L85)).

**Fourier phase is angularly periodic.** Proved result. Under the stated hypotheses, the time-angular Fourier phase is periodic in the angle. (`expFactor_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L99)).

**Angular exponential has norm one.** Proved result. Under the stated hypotheses, the angular phase exponential has norm one. (`norm_exp_angle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L109)).

**Weighted mode integrand is integrable.** Proved result. Under the stated hypotheses, the bounded phase and linear coordinate weighting preserve integrability. (`integrable_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L114)).

**Evaluate an averaged slice.** Proved result. Under the stated hypotheses, a linear frame functional passes through the weighted time integral. (`slice_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L128)).

**Shift a full-period integral.** Proved result. Under the stated hypotheses, the integral over zero to two pi equals the centered full-period integral. (`period_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L142)).

**Split a Fourier mode into harmonics.** Proved result. Under the stated hypotheses, the time-angular mode is the angular cosine coefficient plus i times the angular sine coefficient. (`mode_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L148)).

**Spacetime orbit is continuous.** Proved result. Under the stated hypotheses, the time and rotated meridian-point map is continuous. (`continuous_orbitTime`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L229)).

**Spacetime cylindrical integration.** Proved result. Under the stated hypotheses, the spacetime lower integral becomes a radius-weighted cylindrical lower integral. (`lintegral_cyl_time`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L239)).

**Almost every orbit is integrable.** Proved result. Under the stated hypotheses, the field is integrable over time and angle for almost every positive-radius meridian point. (`ae_integrable_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L259)).

**Restricted time product measure.** Proved result. Under the stated hypotheses, restricting time before taking the product equals restricting the spacetime measure to that time slab. (`prod_restrict_univ`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L371)).

**Local integral below period integral.** Proved result. Under the stated hypotheses, the lower integral over a time-ball box is bounded by the full period lower integral. (`setLIntegral_le_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L375)).

**Time-ball boxes have finite volume.** Proved result. Under the stated hypotheses, the product of a unit time interval and a closed ball has finite volume. (`volume_box_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L384)).

**Operator norm from columns.** Proved result. Under the stated hypotheses, the operator norm is bounded by the sum of the coordinate-column norms. (`opNorm_le_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L389)).

**Finite sum by one plus squares.** Proved result. Under the stated hypotheses, the sum of three values is bounded by one plus three times their square sum. (`sum_le_one_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L405)).

**Operator norm by matrix square.** Proved result. Under the stated hypotheses, the operator norm is bounded by one plus three times the matrix square. (`norm_le_one_add_columnSquares`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L412)).

**Second-derivative norm by entries.** Proved result. Under the stated hypotheses, the bilinear operator norm is bounded by one plus nine times the sum of its squared basis entries. (`norm_le_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L415)).

**Column squares are nonnegative.** Proved result. Under the stated hypotheses, the matrix column-square sum is nonnegative. (`columnSquares_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L431)).

**Extended norm from a real bound.** Proved result. Under the stated hypotheses, the stated real norm estimate gives the corresponding extended nonnegative bound. (`enorm_le_ofReal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L435)).

**Local spacetime integral is finite.** Proved result. Under the stated hypotheses, the field's norm has finite lower integral over the stated time-ball box. (`lintegral_box_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L441)).

**Velocity is locally integrable.** Proved result. Under the stated hypotheses, the velocity norm has finite lower integral over the time-ball box. (`box_velocity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L461)).

**Gradient is locally integrable.** Proved result. Under the stated hypotheses, the gradient norm has finite lower integral over the time-ball box. (`box_gradient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L505)).

**Second derivative is locally integrable.** Proved result. Under the stated hypotheses, the second-derivative norm has finite lower integral over the time-ball box. (`box_secondDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L515)).

**Velocity frame functional.** Definition. This defines the continuous linear functional taking a velocity frame component. (`velFun`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L526)).

**Gradient frame functional.** Definition. This defines the continuous linear functional taking a gradient frame component. (`gradFun`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L528)).

**Second-derivative frame functional.** Definition. This defines the continuous linear functional taking a second-derivative frame component. (`slopeFun`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L531)).

**Velocity functional is continuous.** Proved result. Under the stated hypotheses, the velocity frame functional is continuous in angle. (`continuous_velFun`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L534)).

**Gradient functional is continuous.** Proved result. Under the stated hypotheses, the gradient frame functional is continuous in angle. (`continuous_gradFun`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L537)).

**Second functional is continuous.** Proved result. Under the stated hypotheses, the second-derivative frame functional is continuous in angle. (`continuous_slopeFun`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L540)).

**Velocity functional norm bound.** Proved result. Under the stated hypotheses, a velocity frame component is bounded by the vector norm. (`velFun_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L544)).

**Gradient functional norm bound.** Proved result. Under the stated hypotheses, a gradient frame component is bounded by the operator norm. (`gradFun_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L548)).

**Second functional norm bound.** Proved result. Under the stated hypotheses, a second-derivative frame component is bounded by the bilinear operator norm. (`slopeFun_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L553)).

**Velocity functional is periodic.** Proved result. Under the stated hypotheses, the velocity frame functional is periodic in angle. (`velFun_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L559)).

**Gradient functional is periodic.** Proved result. Under the stated hypotheses, the gradient frame functional is periodic in angle. (`gradFun_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L562)).

**Second functional is periodic.** Proved result. Under the stated hypotheses, the second-derivative frame functional is periodic in angle. (`slopeFun_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L565)).

**Harmonic constructor gives frequency.** Proved result. Under the stated hypotheses, the label constructed from time and azimuthal indices has the stated harmonic frequency. (`labelHarmonic_harmonicMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L568)).

**Harmonic profiles reproduce modes.** Proved result. Under the stated hypotheses, the cosine and sine local profiles reproduce velocity, gradient and second-derivative modes almost everywhere off the axis. (`harmonic_profiles`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L581)).

**Harmonic lifts preserve weak data.** Proved result. Under the stated hypotheses, cosine and sine harmonic lifts form local second-order fields and recover the velocity, gradient and second-derivative modes almost everywhere off the axis. (`harmonicLift_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicProfiles.lean#L625)).

### Breakdown.CertCell.HarmonicSideData

Commutes harmonic averaging with radial and height side-trace integrals. It identifies the velocity, gradient and pressure side data of a harmonic lift. Appendix B: cell-system construction and finite certificate analysis.

**The radial axis is null.** Proved result. Under the stated hypotheses, the radial coordinate is nonzero almost everywhere. (`ae_fst_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L19)).

**Restrict a positive-radius a.e. fact.** Proved result. Under the stated hypotheses, the stated property holds almost everywhere on the nonnegative-radius set. (`ae_on_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L26)).

**Split a complex integral.** Proved result. Under the stated hypotheses, the combined integral is the first integral plus i times the second. (`integral_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L32)).

**Split a radial strip moment.** Proved result. Under the stated hypotheses, the combined radial moment is the first moment plus i times the second. (`radial_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L37)).

**Split a height strip moment.** Proved result. Under the stated hypotheses, the combined height moment is the first moment plus i times the second. (`height_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L56)).

**Segment test is continuous.** Proved result. For each face segment and integer d ≥ 0, its test function ∑ᵢ₌₀ᵈ aᵢsⁱ is continuous on R. (`test_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L86)).

**Split a segment moment.** Proved result. Under the stated hypotheses, the combined segment moment is the first moment plus i times the second. (`moment_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L90)).

**Two-term integrand is integrable.** Proved result. Under the stated hypotheses, the indicated two-term combination is integrable on the set. (`two_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L120)).

**Cell rectangles are compact.** Proved result. Under the stated hypotheses, the cell rectangle is compact. (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L125)).

**Cell rectangles are measurable.** Proved result. Under the stated hypotheses, the cell rectangle is measurable. (`rect_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L127)).

**Select a single second-mode entry.** Proved result. Under the stated hypotheses, a one-entry coefficient array selects the corresponding second-derivative mode. (`third_oneHot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L129)).

**Field profiles are integrable.** Proved result. Under the stated hypotheses, the velocity, gradient and radius-weighted second-derivative modes are integrable on the cell. (`field_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L134)).

**Radial velocity strip is integrable.** Proved result. Under the stated hypotheses, the affine velocity and radial-derivative strip expression is integrable. (`radial_plain_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L160)).

**Radial gradient strip is integrable.** Proved result. Under the stated hypotheses, the affine gradient and second-derivative strip expression is integrable. (`radial_weighted_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L168)).

**Height velocity strip is integrable.** Proved result. Under the stated hypotheses, the weighted affine velocity and height-derivative strip expression is integrable. (`height_plain_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L188)).

**Height gradient strip is integrable.** Proved result. Under the stated hypotheses, the radius-weighted gradient and second-derivative strip expression is integrable. (`height_weighted_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L200)).

**Endpoint reflection gives the interval.** Proved result. Under the stated hypotheses, the interval between a cell endpoint and its reflected endpoint is the cell interval. (`pair_Icc`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L211)).

**Radial strip lies in the cell.** Proved result. Under the stated hypotheses, the radial strip rectangle is contained in the cell rectangle. (`radial_strip_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L217)).

**Height strip lies in the cell.** Proved result. Under the stated hypotheses, the height strip rectangle is contained in the cell rectangle. (`height_strip_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L225)).

**Opposite radial side case.** Proved result. Under the stated hypotheses, the opposite radial side is the axis or the cell has positive inner radius. (`radial_other_case`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L233)).

**Radius is nonnegative in the rectangle.** Proved result. Under the stated hypotheses, every point in the stated rectangle has nonnegative radius. (`rect_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L246)).

**Harmonic side data equal side moments.** Proved result. Under the stated hypotheses, harmonic velocity and normal-gradient side data equal the analytic side moments for the permitted polynomial degrees and parities. (`harmonicSideData_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicSideData.lean#L253)).

### Breakdown.CertCell.HeightStripTrace

Uses product-measure integration to derive the height-strip trace identity. This links the weak height derivative to the difference between the two height-face traces. Appendix B: cell-system construction and finite certificate analysis.

**Iterate a rectangle integral.** Proved result. Under the stated hypotheses, the set integral over a product set equals the iterated set integral. (`restrict_prod_iterate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HeightStripTrace.lean#L17)).

**Height strips integrate side traces.** Proved result. Under the stated hypotheses, the height-strip moment equals the radial integral of the side trace against the same continuous radial weight and test. (`heightStripTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HeightStripTrace.lean#L29)).

### Breakdown.CertCell.InstanceBasic

Establishes reflection, rotational symmetry, support and normalization facts for the concrete chart weights and fields. These elementary identities feed the later instance construction. Appendix B: cell-system construction and finite certificate analysis.

**Reflection negates height.** Proved result. Under the stated hypotheses, the third coordinate changes sign under reflection. (`flipPoint_third`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L19)).

**Reflection preserves norm.** Proved result. Under the stated hypotheses, spatial reflection preserves the norm. (`flipPoint_norm_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L22)).

**Rotation fixes height.** Proved result. Under the stated hypotheses, axial rotation preserves the third coordinate. (`axialRot_third`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L27)).

**Rotation preserves norm.** Proved result. Under the stated hypotheses, axial rotation preserves the norm. (`axialRot_norm_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L30)).

**Radial chart is rotation invariant.** Proved result. Under the stated hypotheses, the compactified radial chart coordinate is invariant under axial rotation. (`chartT_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L37)).

**Height ratio is rotation invariant.** Proved result. Under the stated hypotheses, the normalized height is invariant under axial rotation. (`heightRatio_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L41)).

**Radial chart is reflection invariant.** Proved result. Under the stated hypotheses, the compactified radial chart coordinate is invariant under reflection. (`chartT_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L45)).

**Height ratio changes sign.** Proved result. Under the stated hypotheses, reflection negates the normalized height. (`heightRatio_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L49)).

**Radial chart is nonnegative.** Proved result. Under the stated hypotheses, the radial chart coordinate is nonnegative. (`chartT_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L53)).

**Radial chart is below one.** Proved result. Under the stated hypotheses, the radial chart coordinate is strictly below one. (`chartT_lt_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L58)).

**Height bounded by spatial norm.** Proved result. Under the stated hypotheses, the absolute height coordinate is at most the spatial norm. (`abs_third_le_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L64)).

**Upper height ratio is nonnegative.** Proved result. Under the stated hypotheses, the normalized height is nonnegative in the stated upper-half case. (`heightRatio_nonneg_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L68)).

**Height ratio is at most one.** Proved result. Under the stated hypotheses, the normalized height is at most one. (`heightRatio_le_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L72)).

**Lower height ratio becomes nonnegative.** Proved result. Under the stated hypotheses, the negative normalized height is nonnegative in the stated lower-half case. (`neg_heightRatio_nonneg_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L80)).

**Negative height ratio is at most one.** Proved result. Under the stated hypotheses, the negative normalized height is at most one. (`neg_heightRatio_le_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L85)).

**Cell index stays in range.** Proved result. Under the stated hypotheses, the selected cell index is smaller than the cell count. (`index_lt_count`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L94)).

**Cell index at zero.** Proved result. If the cell breakpoints are strictly increasing and begin at zero, the point zero is assigned to the first cell. (`index_at_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L106)).

**Substitution at zero preserves value.** Proved result. Under the stated hypotheses, substituting zero into the second polynomial variable preserves evaluation on that axis. (`eval_atSecond_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L120)).

**Spline halves agree on the plane.** Proved result. Under the stated hypotheses, the upper and lower spline values agree at normalized height zero. (`halves_agree_on_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L130)).

**Radial chart is measurable.** Proved result. Under the stated hypotheses, the compactified radial coordinate is measurable. (`chartT_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L140)).

**Height ratio is measurable.** Proved result. Under the stated hypotheses, the normalized height is measurable. (`heightRatio_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L144)).

**Half-spline evaluation is measurable.** Proved result. Under the stated hypotheses, the chart half-spline evaluation is measurable. (`half_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L148)).

**Cell-index values are measurable.** Proved result. Under the stated hypotheses, the function selected by the two chart cell indices is measurable. (`values_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L154)).

**Scalar evaluation is regular.** Proved result. Under the stated hypotheses, scalar evaluation is measurable and axisymmetric, and nonnegative stored values give nonnegative evaluation. (`scalarBasicFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L166)).

**Step evaluation is regular.** Proved result. Under the stated hypotheses, step evaluation is measurable and axisymmetric, and positive step data give strictly positive evaluation. (`stepBasicFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L189)).

**Mirrored evaluation respects reflection.** Proved result. Under the stated hypotheses, mirrored scalar and step data reproduce the original values after reflection, with the stated plane exception for steps. (`mirrorEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceBasic.lean#L220)).

### Breakdown.CertCell.InstanceChartGlue

Develops derivatives of piecewise polynomial chart profiles and proves their matching conditions at breakpoints. The resulting gluing lemmas give the stated differentiability of joined scalar profiles. Appendix B: cell-system construction and finite certificate analysis.

**Evaluate a two-variable polynomial.** Definition. `Breakdown.CertCell.Instance.polyAt` evaluates the complex polynomial at the two real coordinates. (`polyAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L15)).

**Derivative of a chart polynomial.** Definition. This defines the continuous linear derivative from the two polynomial partial derivatives. (`polyDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L18)).

**Polynomial derivative applied.** Proved result. Under the stated hypotheses, the polynomial derivative is the sum of the two directional components times the corresponding partial evaluations. (`polyDiff_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L22)).

**Polynomial evaluation preserves negation.** Proved result. Under the stated hypotheses, evaluating the negative polynomial negates its value. (`polyAt_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L27)).

**Chart polynomial is differentiable.** Proved result. Under the stated hypotheses, the two-variable polynomial has the explicitly defined Fréchet derivative. (`polyAt_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L30)).

**Chart polynomial is continuous.** Proved result. Under the stated hypotheses, the two-variable polynomial evaluation is continuous. (`polyAt_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L56)).

**Polynomial derivative is continuous.** Proved result. Under the stated hypotheses, the explicit polynomial derivative is continuous. (`polyDiff_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L59)).

**Tangential derivative along height join.** Proved result. Under the stated hypotheses, polynomials agreeing along a height join have equal radial-chart derivatives there. (`deriv_along_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L65)).

**Tangential derivative along radial join.** Proved result. Under the stated hypotheses, polynomials agreeing along a radial-chart join have equal height derivatives there. (`deriv_along_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L75)).

**Polynomial partials commute.** Proved result. Under the stated hypotheses, the two polynomial partial-derivative operators commute. (`pderiv_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L85)).

**Evaluate a polynomial substitution.** Proved result. Under the stated hypotheses, evaluation of a substituted polynomial equals evaluation at the substituted variable values. (`polyAt_bind`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L92)).

**Fix the first polynomial variable.** Proved result. Under the stated hypotheses, evaluating the first-variable substitution fixes the first coordinate to the chosen value. (`polyAt_atFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L100)).

**Fix the second polynomial variable.** Proved result. Under the stated hypotheses, evaluating the second-variable substitution fixes the second coordinate to the chosen value. (`polyAt_atSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L107)).

**Equality after first-variable fixing.** Proved result. Under the stated hypotheses, the stated substitution equality gives equal evaluations on the fixed first-coordinate line. (`value_of_atFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L114)).

**Equality after second-variable fixing.** Proved result. Under the stated hypotheses, the stated substitution equality gives equal evaluations on the fixed second-coordinate line. (`value_of_atSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L119)).

**Slot selected by ordered breaks.** Definition. `Breakdown.CertCell.Instance.slot` counts the listed breakpoints that are at most the coordinate. (`slot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L124)).

**Slot lies within the break list.** Proved result. Under the stated hypotheses, the slot index is at most the number of breakpoints. (`slot_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L126)).

**Slot across the first breakpoint.** Proved result. Under the stated hypotheses, the slot is zero before the first break and one plus the remaining slot after it. (`slot_cons`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L128)).

**Slot below all breaks.** Proved result. Under the stated hypotheses, a coordinate below all breakpoints has slot zero. (`slot_of_below`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L139)).

**Glue differentiable pieces.** Proved result. Under the stated hypotheses, matching values and derivatives across the join give a differentiable piecewise function with continuous derivative. (`glue_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L145)).

**Glue a chain of pieces.** Proved result. Under the stated hypotheses, an ordered chain of matching differentiable pieces has the stated piecewise derivative and continuous derivative. (`glue_chain`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L177)).

**Matching polynomial half-grid.** Proposition structure. The interface requires that adjacent polynomial pieces match in value and normal derivative along both grid directions. (`HalfJoined`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L210)).

**Piecewise half-grid value.** Definition. `Breakdown.CertCell.Instance.halfF` selects the polynomial piece by the two slot indices and evaluates it. (`halfF`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L218)).

**Piecewise half-grid derivative.** Definition. `Breakdown.CertCell.Instance.halfD` selects the derivative of the polynomial piece at the two slot indices. (`halfD`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L221)).

**Glue a polynomial half-grid.** Proved result. Under the stated hypotheses, the matching half-grid gives the stated derivative and its continuity. (`half_glue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L224)).

**Matching upper and lower grids.** Proposition structure. The interface requires that both half-grids are joined and their values and signed normal derivatives match on the central plane. (`BothJoined`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L257)).

**Negate the second coordinate.** Definition. This defines the continuous linear map that negates the second coordinate. (`flipSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L263)).

**Second-coordinate reflection formula.** Proved result. Under the stated hypotheses, the linear reflection sends the pair to its first coordinate and negative second coordinate. (`flipSecond_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L265)).

**Joined upper and lower value.** Definition. `Breakdown.CertCell.Instance.bothF` uses the upper grid above the plane and the reflected lower grid below it. (`bothF`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L267)).

**Joined upper and lower derivative.** Definition. `Breakdown.CertCell.Instance.bothD` uses the derivative of the selected half-grid with the reflection chain rule below the plane. (`bothD`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L270)).

**Ordered chart grid conditions.** Proposition structure. The interface requires that the radial and two height breakpoint lists are ordered and the height breaks are positive. (`Grid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L273)).

**Glue upper and lower grids.** Proved result. Under the stated hypotheses, the joined grids give a differentiable function with the specified continuous derivative. (`both_glue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L280)).

**First derivative of the joined grid.** Proved result. Under the stated hypotheses, the first-coordinate derivative equals the joined evaluation of the first polynomial partials. (`bothD_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L310)).

**Second derivative of the joined grid.** Proved result. Under the stated hypotheses, the second-coordinate derivative uses the upper partial and the negative lower partial. (`bothD_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L316)).

**Joined grid is twice differentiable.** Proved result. Under the stated hypotheses, the joined piecewise polynomial function is twice continuously differentiable. (`both_contDiff_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L322)).

**Evaluate a constant polynomial factor.** Proved result. Under the stated hypotheses, a constant polynomial factor comes out of evaluation. (`polyAt_C_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L353)).

**Interior breakpoints.** Definition. `Breakdown.CertCell.Instance.inner` removes the first and last entries of the breakpoint list. (`inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L357)).

**Interior breakpoint facts.** Proved result. Under the stated hypotheses, the interior breaks are positive and ordered, with the stated count and indexing relation. (`inner_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L359)).

**Match derivatives at a radial break.** Proved result. Under the stated hypotheses, the stated polynomial partial derivatives match at the radial-chart breakpoint. (`t_join`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L379)).

**Match derivatives at a height break.** Proved result. Under the stated hypotheses, the stated polynomial partial derivatives match at the height-chart breakpoint. (`x_join`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L390)).

**Original half-grid joins.** Proved result. Under the stated hypotheses, the original polynomial half-grid satisfies the matching conditions. (`joined_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L401)).

**First partial half-grid joins.** Proved result. Under the stated hypotheses, the first-coordinate partial polynomials satisfy the matching conditions. (`joined_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L406)).

**Second partial half-grid joins.** Proved result. Under the stated hypotheses, the second-coordinate partial polynomials satisfy the matching conditions. (`joined_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L413)).

**Negated half-grid joins.** Proved result. Under the stated hypotheses, negating every polynomial preserves the half-grid matching conditions. (`joined_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L420)).

**Signed derivatives match on the plane.** Proved result. Under the stated hypotheses, the normal partials of the upper and lower pieces differ by the prescribed parity sign at the plane. (`plane_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L425)).

**Chart scalar is twice smooth.** Proved result. Under the stated hypotheses, the joined scalar in chart coordinates is twice continuously differentiable on the stated strip. (`chartScalar_halves_contDiffOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceChartGlue.lean#L440)).

### Breakdown.CertCell.InstanceClassForm

Computes conjugation and quadratic values of the class Gram matrices and their inverse blocks. The identities connect finite class coordinates with the analytic pairing form. Appendix B: cell-system construction and finite certificate analysis.

**Conjugation commutes with matrix inverse.** Proved result. Under the stated hypotheses, entrywise conjugation commutes with matrix inversion. (`map_conj_inv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L24)).

**Conjugate an inverse matrix action.** Proved result. Under the stated hypotheses, conjugating the inverse-matrix action conjugates the inverse matrix and input vector. (`conj_inv_mulVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L32)).

**Inverse quadratic form conjugates.** Proved result. Under the stated hypotheses, conjugating the matrix and vector preserves the real inverse quadratic value. (`quad_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L38)).

**Transport a conjugate inverse form.** Proved result. Under the stated hypotheses, the stated conjugate data have equal real inverse quadratic values. (`quad_conj_cast`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L47)).

**Zero vector gives zero inverse form.** Proved result. Under the stated hypotheses, the inverse quadratic pairing vanishes for the specified zero vector. (`quad_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L61)).

**Real inverse action stays real.** Proved result. Under the stated hypotheses, the indicated inverse-matrix image has zero imaginary coordinates. (`inv_mulVec_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L66)).

**Sum over a unique satisfying index.** Proved result. Under the stated hypotheses, a finite conditional sum equals the common value if a unique satisfying index exists and zero otherwise. (`sum_ite_unique`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L77)).

**Integral of real data is real.** Proved result. Under the stated hypotheses, the stated set integral is fixed by complex conjugation. (`conj_setIntegral_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L91)).

**Label harmonics preserve negation.** Proved result. Under the stated hypotheses, the harmonic of a negated label is the negative harmonic. (`labelHarmonic_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L98)).

**Negative-label velocity conjugates.** Proved result. Under the stated hypotheses, negating a label conjugates the corresponding velocity mode. (`labelVel_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L102)).

**Reflected label frequency.** Proved result. Under the stated hypotheses, reflecting the label negates the angular frequency while preserving the stated time frequency. (`labelHarmonic_labelFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L108)).

**Reflected velocity label.** Proved result. Under the stated hypotheses, the reflected label at reflected height gives the frame sign times the original velocity coefficient. (`labelVel_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L113)).

**Frame signs cancel under conjugation.** Proved result. Under the stated hypotheses, the two identical frame signs cancel around complex conjugation. (`frameSign_mul_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L120)).

**Lower and upper moments agree.** Proved result. Under the stated hypotheses, the reflected field conditions make the lower moment equal the upper moment. (`lowerMoment_eq_upper`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L124)).

**Row moment integrand is integrable.** Proved result. Under the stated hypotheses, the radius-weighted label velocity paired with the row test is integrable on its cell. (`momentIntegrand_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L132)).

**Padded cell moment.** Definition. `Breakdown.CertCell.Instance.Internal.ClassForm.momentAt` uses the indexed cell moment inside the test range and zero outside it. (`momentAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L158)).

**Block inverse solution.** Definition. This defines the scaled inverse test block applied to the cell-moment vector. (`solutionVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L161)).

**Padded inverse solution.** Definition. `Breakdown.CertCell.Instance.Internal.ClassForm.solutionAt` uses the block solution inside its coordinate range and zero outside it. (`solutionAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L164)).

**Real row solution.** Definition. `Breakdown.CertCell.Instance.Internal.ClassForm.solution` takes the selected real component of the block solution with its row phase factor. (`solution`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L167)).

**Weighted sum within a block.** Definition. This defines the weighted row sum restricted to one cell and label block. (`blockSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L171)).

**Inverse block quadratic form.** Definition. This defines the weighted inverse test-block form of the cell-moment vector. (`blockForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L175)).

**Upper moment from a padded moment.** Proved result. Under the stated hypotheses, the upper moment is two pi times the specified real part of the padded cell moment. (`upperMoment_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L184)).

**Generator pairing from a cell moment.** Proved result. Under the stated hypotheses, the generator pairing is four pi times the specified real component of the cell moment. (`pairing_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L197)).

**Find a row for a test coordinate.** Proved result. Under the stated hypotheses, the requested test coordinate and real-part choice have a matching row. (`exists_row_part`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L210)).

**Row reconstruction gives the solution.** Proved result. Under the stated hypotheses, reconstructing the complex row vector from the real solution gives the block inverse solution. (`rowVec_solution`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L224)).

**Block matrix solves the moment system.** Proved result. Under the stated hypotheses, the test block applied to its solution gives the prescribed multiple of the moment vector. (`blockMatrix_mulVec_solution`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L261)).

**Expand a conjugate row-vector pairing.** Proved result. Under the stated hypotheses, the conjugate row-vector sum expands into the corresponding sum over real row indices. (`sum_conj_rowVec_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L270)).

**Expand a row-vector pairing.** Proved result. Under the stated hypotheses, the row-vector sum expands into its real row-coordinate contributions. (`sum_rowVec_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L290)).

**Pairing matrix action by blocks.** Proved result. Under the stated hypotheses, the test-pairing matrix action is given by the stated block-entry formula. (`pairingMatrix_mulVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L310)).

**Real block solution.** Proved result. Under the stated hypotheses, the specified block solution coordinate has zero imaginary part. (`solutionVec_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L332)).

**Pairing matrix solves the row system.** Proved result. Under the stated hypotheses, applying the pairing matrix to the constructed solution gives the generator-pairing vector. (`pairingMatrix_mulVec_solution`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L361)).

**Inverse pairing solution.** Proved result. Under the stated hypotheses, the inverse pairing matrix applied to the pairing vector equals the constructed solution. (`inv_mulVec_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L391)).

**Block sum as a moment pairing.** Proved result. Under the stated hypotheses, the weighted block sum is four pi times its row-vector and moment pairing. (`blockSum_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L401)).

**Block sum from the inverse form.** Proved result. Under the stated hypotheses, the block sum is the stated factor times the inverse block form. (`blockSum_of_row`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L421)).

**Empty block contributes zero.** Proved result. Under the stated hypotheses, a block with no contributing rows has zero block sum. (`blockSum_of_empty`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L447)).

**Inverse block form is even in labels.** Proved result. Under the stated hypotheses, negating the label preserves the inverse block form. (`blockForm_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L451)).

**Untested block form vanishes.** Proved result. Under the stated hypotheses, the indicated absent block has zero inverse form. (`blockForm_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L469)).

**Opposite-label row sums.** Proved result. Under the stated hypotheses, the opposite-label block sums equal four pi times the sum of their inverse forms. (`pair_of_row`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L475)).

**Opposite-label block identity.** Proved result. Under the stated hypotheses, the combined pair of opposite-label block sums has the stated inverse-form value. (`pair_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L496)).

**Tested labels give the block identity.** Proved result. Under the stated hypotheses, summing over tested labels gives four pi times the sum of inverse block forms. (`tested_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L519)).

**Partition rows by cell and label.** Proved result. Under the stated hypotheses, the full row sum is the sum of the contributions grouped by cell and tested label. (`sum_by_block`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L533)).

**Weighted inverse form by blocks.** Proved result. Under the stated hypotheses, the weighted inverse pairing-matrix form equals the sum of inverse cell-block forms. (`weighted_form_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L553)).

**Row norm as cell block forms.** Proved result. Under the stated hypotheses, the weighted row norm equals four pi times the weighted inverse cell-moment forms. (`classForm_of_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L571)).

**Weighted modes on bounded sets.** Proposition definition. The interface requires that radius-weighted label velocity components are integrable on bounded measurable nonnegative-radius sets for finite-energy fields. (`LabelVelIntegrableOnBounded`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L594)).

**Rows equal the inverse moment form.** Proved result. Under the stated hypotheses, the scaled squared row norm equals four pi times the sum of weighted inverse cell-moment forms. (`rowsClassForm_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClassForm.lean#L601)).

### Breakdown.CertCell.InstanceClauseSplit

Separates the shape-dependent instance requirements from the remaining admissibility and reflection clauses. The assembly lemmas rebuild the full interfaces from those component conditions. Appendix B: cell-system construction and finite certificate analysis.

**Shape admissibility conditions.** Proposition structure. The interface requires that the period, weight lower bound and finite harmonic reconstruction meet the shape admissibility conditions. (`ShapeAdmissibleClauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClauseSplit.lean#L17)).

**Assemble remaining admissibility.** Proved result. Under the stated hypotheses, the split shape and amplitude conditions give the remaining admissibility clauses. (`otherAdmissibleClauses_of_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClauseSplit.lean#L28)).

**Shape reflection conditions.** Proposition structure. The interface requires that the scalar weight and harmonic set are invariant under reflection. (`ShapeFlipClauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClauseSplit.lean#L57)).

**Assemble remaining reflection facts.** Proved result. Under the stated hypotheses, the split reflection facts give the remaining reflection clauses. (`otherFlipClauses_of_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClauseSplit.lean#L61)).

**Constant weight respects reflection.** Proved result. Under the stated hypotheses, the constant weight supplies the shape reflection condition for the stated harmonics. (`constantWeight_shapeFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceClauseSplit.lean#L72)).

### Breakdown.CertCell.InstanceDecay

Shows that compactified piecewise polynomial profiles have the required derivative decay. It propagates the estimates through the chart construction to the instance's weighted fields. Appendix B: cell-system construction and finite certificate analysis.

**Joined chart-scalar value.** Definition. `Breakdown.CertCell.Instance.glued` selects the real upper spline value or the reflected real lower spline value. (`glued`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L16)).

**Joined scalar is twice smooth.** Proved result. Under the stated hypotheses, the joined chart scalar is twice continuously differentiable on the specified strip. (`glued_contDiffOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L19)).

**Interior chart breaks are below one.** Proved result. Under the stated hypotheses, every interior chart breakpoint is strictly below one. (`breaks_lt_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L23)).

**A common threshold below one.** Proved result. Under the stated hypotheses, the finite break list has a common upper threshold between one half and one. (`exists_upper`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L32)).

**Index beyond the last breakpoint.** Proved result. Under the stated hypotheses, a coordinate beyond the interior breaks selects the last cell index. (`cellIndex_of_ge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L44)).

**Cell index is bounded.** Proved result. Under the stated hypotheses, the cell index is at most the number of interior breakpoints. (`cellIndex_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L51)).

**Fix one variable of a polynomial.** Proved result. Under the stated hypotheses, two-variable evaluation agrees with the associated one-variable polynomial evaluation. (`eval_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L54)).

**Degree after fixing a variable.** Proved result. Under the stated hypotheses, the resulting one-variable polynomial degree is at most the original degree in that variable. (`natDegree_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L59)).

**Last-cell polynomial description.** Proved result. Under the stated hypotheses, beyond a common threshold the joined spline is polynomial in the radial chart coordinate with a uniform degree bound. (`glued_last_cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L64)).

**Interpolation node basis.** Definition. This defines the Lagrange basis polynomial for the selected interpolation node. (`nodeBasis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L100)).

**Interpolation basis is smooth.** Proved result. Under the stated hypotheses, the interpolation node basis is twice continuously differentiable. (`nodeBasis_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L103)).

**Real polynomial interpolation.** Proved result. Under the stated hypotheses, the real part of a polynomial equals the sum of its node values times the real interpolation basis. (`interp_re`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L106)).

**Smooth extension at infinity.** Proved result. Under the stated hypotheses, the last-cell representation admits the stated twice continuously differentiable extension. (`glued_far_extension`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L125)).

**Inverse-radius chart pair.** Definition. This defines inverse radius and normalized height as a coordinate pair. (`chartPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L161)).

**Inverse-radius chart is smooth.** Proved result. Under the stated hypotheses, the inverse-radius chart pair is twice continuously differentiable away from the origin. (`chartPair_contDiffOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L163)).

**Scale the first chart coordinate.** Definition. This defines the continuous linear map scaling only the first coordinate. (`scaleFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L172)).

**Coordinate scaling is a contraction.** Proved result. Under the stated hypotheses, the stated first-coordinate scaling map has operator norm at most one. (`scaleFirst_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L175)).

**Spatial scaling rescales the chart.** Proved result. Under the stated hypotheses, scaling space by a positive factor and scaling the chart’s first coordinate by the same factor recovers the original inverse-radius chart. (`chartPair_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L184)).

**Chart derivatives decay.** Proved result. Under the stated hypotheses, first and second derivatives of the inverse-radius chart satisfy the stated inverse-radius bounds. (`chartPair_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L196)).

**Far part of a scalar chart.** Definition. `Breakdown.CertCell.Instance.farPart` composes the extension with the compactifying radial coordinate. (`farPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L266)).

**Far part is twice smooth.** Proved result. Under the stated hypotheses, the far chart part is twice continuously differentiable where its denominator is positive. (`farPart_contDiffOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L268)).

**Far-part derivatives are bounded.** Proved result. Under the stated hypotheses, the derivatives through order two are uniformly bounded on the stated chart rectangle. (`farPart_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L274)).

**Scalar equals joined chart evaluation.** Proved result. Under the stated hypotheses, the scalar evaluation equals the joined scalar evaluated at its two chart coordinates. (`eval_eq_glued`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L298)).

**Height ratio lies in the unit interval.** Proved result. Under the stated hypotheses, the normalized height lies between minus one and one. (`heightRatio_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L309)).

**Derivatives decay by their order.** Proved result. Under the stated hypotheses, derivatives of orders zero through two are uniformly bounded after multiplication by one plus spatial norm raised to the derivative order. (`scalarDerivativeDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceDecay.lean#L318)).

### Breakdown.CertCell.InstanceGeneratorForm

Relates reflected labels and scaled cell polynomials to generator evaluations. These identities establish the finite generator-form conditions for the concrete instance. Appendix B: cell-system construction and finite certificate analysis.

**Label reflection is involutive.** Proved result. Under the stated hypotheses, reflecting a label twice restores it. (`labelFlip_labelFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceGeneratorForm.lean#L13)).

**Move a label reflection across equality.** Proved result. Under the stated hypotheses, equality to a reflected label is equivalent to the reflected opposite equality. (`labelFlip_eq_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceGeneratorForm.lean#L17)).

**Zero cell polynomial evaluates to zero.** Proved result. Under the stated hypotheses, the zero cell polynomial has zero value. (`cellPoly_eval_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceGeneratorForm.lean#L24)).

**Cell polynomial scaling.** Proved result. Under the stated hypotheses, scaling a cell polynomial scales its evaluation. (`cellPoly_eval_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceGeneratorForm.lean#L27)).

**Generator plane-value formula.** Proved result. Under the stated hypotheses, the generator coefficient is the selected row test above the plane and its reflected signed coefficient below it. (`generator_planeValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceGeneratorForm.lean#L33)).

**Generator as a supported mode sum.** Proved result. Under the stated hypotheses, the generator field equals its finite frame expansion restricted to the owning cell solid. (`generatorField_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceGeneratorForm.lean#L66)).

### Breakdown.CertCell.InstanceLinkActuators

Verifies the actuator construction's rotational and reflection laws together with its support and admissibility clauses. The result links the concrete actuator fields to the abstract instance interface. Appendix B: cell-system construction and finite certificate analysis.

**Compose axial rotations.** Proved result. Under the stated hypotheses, two successive axial rotations add their angles. (`axialRot_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L17)).

**Zero-angle rotation.** Proved result. Under the stated hypotheses, rotation by angle zero is the identity. (`axialRot_zero_angle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L21)).

**Linear reflection map.** Definition. `Breakdown.CertCell.Instance.Internal.ActuatorSymmetry.flipMap` packages spatial reflection as a real linear map. (`flipMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L25)).

**Spatial reflection is involutive.** Proved result. Under the stated hypotheses, spatial reflection applied twice is the identity. (`flipPoint_involutive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L34)).

**Reflection preserves the norm.** Proved result. Under the stated hypotheses, reflection preserves the spatial norm. (`norm_flipPoint_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L38)).

**Reflection as a linear isometry.** Definition. `Breakdown.CertCell.Instance.Internal.ActuatorSymmetry.flipIso` packages reflection as an invertible real linear isometry. (`flipIso`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L43)).

**Reflection preserves volume.** Proved result. Under the stated hypotheses, spatial reflection preserves volume. (`measurePreserving_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L47)).

**Shift and rotation preserve null sets.** Proved result. Under the stated hypotheses, time translation combined with spatial rotation is quasi-measure-preserving. (`quasi_shift_rotate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L52)).

**Spacetime reflection preserves null sets.** Proved result. Under the stated hypotheses, spatial reflection in spacetime is quasi-measure-preserving. (`quasi_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L59)).

**Integer time shifts preserve a period.** Proved result. Under the stated hypotheses, a time-periodic field is unchanged by every integer time shift. (`periodic_int_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L65)).

**Iterate the half-turn symmetry.** Proved result. Under the stated hypotheses, the half-turn symmetry iterates to the stated integer multiple of time shift and rotation. (`rotate_iterate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L83)).

**Actuators obey the symmetry group.** Proved result. Under the stated hypotheses, the shape conditions imply almost-everywhere equivariance of each actuator under every specified symmetry. (`actuatorInvariant_of_shape_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L108)).

**Actuator conditions follow from data.** Proved result. Under the stated hypotheses, the actuator instance gives the required analytic actuator facts. (`actuatorFacts_of_instance_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L130)).

**Pin fields meet analytic conditions.** Proved result. Under the stated hypotheses, the pin instance gives measurable pin fields with finite period matrix-square integral. (`pinInstance_clauses_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkActuators.lean#L180)).

### Breakdown.CertCell.InstanceLinkRows

Uses pointwise majorants to prove the row fields' integral regularity. It then assembles the row-instance clauses and their consequences for valid certificate entries. Appendix B: cell-system construction and finite certificate analysis.

**Finite period integral by domination.** Proved result. Under the stated hypotheses, domination by a finite-integral function makes the period lower integral finite. (`periodLIntegral_lt_top_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkRows.lean#L18)).

**Row fields are regular.** Proved result. Under the stated hypotheses, row fields are measurable, time-periodic and have finite period square integral. (`rowField_regular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkRows.lean#L42)).

**Row instance gives row conditions.** Proved result. Under the stated hypotheses, the row instance supplies regularity, orthonormality and the nonnegative bounded row weights. (`rowInstance_clauses_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkRows.lean#L80)).

**Assemble the analytic instance.** Proved result. Under the stated hypotheses, the row fields, weights, actuators and pins satisfy the required orthonormality, boundedness, regularity, symmetry and class-form conditions. (`instanceConsequences_of_entry_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkRows.lean#L99)).

**Valid entries give analytic data.** Proved result. Under the stated hypotheses, a valid instance entry with actuator shape facts gives the required row, weight, actuator and pin conditions. (`instanceConsequences_of_entry_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkRows.lean#L131)).

### Breakdown.CertCell.InstanceLinkWeights

Derives lower-order spline matching from higher-order joins and bounds joined scalar profiles. These facts assemble the concrete weight clauses required by the instance. Appendix B: cell-system construction and finite certificate analysis.

**Lower the required join order.** Proved result. Under the stated hypotheses, spline joins of the stated higher order imply joins of the lower order. (`splineJoins_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkWeights.lean#L15)).

**Twice-joined scalar is joined at zero.** Proved result. Under the stated hypotheses, join conditions through order two imply the order-zero joins. (`joinedScalar_zero_of_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkWeights.lean#L21)).

**Entry bounded by absolute sum.** Proved result. Under the stated hypotheses, one indexed value is at most the sum of the absolute values. (`le_sum_abs_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkWeights.lean#L27)).

**Weight values give admissibility.** Proved result. Under the stated hypotheses, the weight data imply the admissible-weight clauses. (`weightClauses_of_values_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkWeights.lean#L31)).

**Weight values give reflection laws.** Proved result. Under the stated hypotheses, the weight data imply the required reflection clauses. (`weightsFlip_of_values_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkWeights.lean#L109)).

**Weight instance gives all clauses.** Proved result. Under the stated hypotheses, each admissible parameter supplies the weight admissibility, reflection and coercivity identity. (`weightInstance_clauses_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceLinkWeights.lean#L159)).

### Breakdown.CertCell.InstanceModeMean

Computes the mean of complex exponentials and products of real harmonic modes over one period. The resulting orthogonality formulas identify the time-averaged mode contributions. Appendix B: cell-system construction and finite certificate analysis.

**Integrate a full-period exponential.** Proved result. Under the stated hypotheses, the phase integral is the interval length at zero frequency and zero for the permitted nonzero frequencies. (`integral_exp_full_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L15)).

**Real part of a phase integral.** Proved result. Under the stated hypotheses, the full-period real phase integral retains only the zero-frequency coefficient. (`integral_re_exp_full_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L36)).

**Product of real parts.** Proved result. Under the stated hypotheses, the product of real parts splits into the conjugate and unconjugated complex products. (`re_mul_re_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L48)).

**Exponential of a phase sum.** Proved result. Under the stated hypotheses, adding real phases multiplies their complex exponentials. (`exp_phase_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L52)).

**Product with a conjugate phase.** Proved result. Under the stated hypotheses, multiplying by the conjugate phase subtracts the phase angles. (`phase_mul_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L60)).

**Product of two phases.** Proved result. Under the stated hypotheses, multiplying phase-weighted coefficients adds the phase angles. (`phase_mul_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L68)).

**Angular average of two real modes.** Proved result. Under the stated hypotheses, the angular average keeps only equal or opposite angular frequencies. (`angle_mean`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L74)).

**Time average selects full labels.** Proved result. Under the stated hypotheses, the frequency tests reduce to equality or negation of the full harmonic labels. (`mean_of_components`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L118)).

**Mean product of real modes.** Proved result. Under the stated hypotheses, the time-angular mean keeps exactly the equal-frequency and opposite-frequency terms. (`modeProduct_mean`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceModeMean.lean#L139)).

### Breakdown.CertCell.InstanceMomentLower

Expresses a localized lower moment using an indicator and a continuous coefficient. Integrability and support identities justify the resulting lower-moment evaluation. Appendix B: cell-system construction and finite certificate analysis.

**Reflected lower cell set.** Definition. This defines negative-height points whose reflected meridian coordinates lie in the cell. (`lowerSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L15)).

**Lower generator coefficient.** Definition. This defines the signed reflected row-test coefficient for the lower half. (`lowerCoef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L17)).

**Generator restricted to the lower half.** Proved result. Under the stated hypotheses, the lower generator equals the stated reflected meridian mode expansion. (`lower_indicator_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L21)).

**Continuous lower generator coefficient.** Proved result. For fixed row data, cell boxes and a vector component, the coefficient of the lower moment generator is continuous in the meridian coordinates. (`continuous_lowerCoef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L44)).

**Height-flip measurable equivalence.** Definition. `Breakdown.CertCell.Instance.Internal.MomentLower.heightFlip` constructs the measurable equivalence negating meridian height. (`heightFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L49)).

**Height-flip action.** Proved result. Under the stated hypotheses, the height-flip map fixes radius and negates height. (`heightFlip_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L51)).

**Height flip preserves volume.** Proved result. Under the stated hypotheses, the meridian height flip preserves plane volume. (`heightFlip_mp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L53)).

**Lower cell lies in reflected cell.** Proved result. Under the stated hypotheses, the negative-height cell set is contained in the reflected original rectangle. (`lowerSet_sub_image`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L58)).

**Reflected cell is compact.** Proved result. Under the stated hypotheses, the image of the cell rectangle under height reflection is compact. (`isCompact_image`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L62)).

**Lower cell is measurable.** Proved result. Under the stated hypotheses, the reflected lower cell set is measurable. (`measurableSet_lowerSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L68)).

**Height-zero line is null.** Proved result. Under the stated hypotheses, the height-zero line has plane volume zero. (`null_height_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L74)).

**Lower-cell preimage agrees a.e..** Proved result. Under the stated hypotheses, reflecting the lower cell back gives the original rectangle almost everywhere. (`preimage_ae_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L79)).

**Lower generator pairing.** Proved result. Under the stated hypotheses, the lower-half generator pairing equals the lower moment. (`lower_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L93)).

**Lower moment formula holds.** Proved result. Under the stated hypotheses, the lower moment evaluates the indicated restricted generator pairing. (`generator_lower_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentLower.lean#L134)).

### Breakdown.CertCell.InstanceMomentUpper

Proves integrability of the upper-moment pairing in the half-plane and rotational-orbit formulations. It then identifies the upper moment with its orbit average. Appendix B: cell-system construction and finite certificate analysis.

**Supported norm is integrable.** Proved result. Under the stated hypotheses, the field norm restricted to the bounded cylindrical support is integrable over a period. (`integrable_normPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L15)).

**Plane-field pairing is integrable.** Proved result. Under the stated hypotheses, the pairing of the field with the supported plane field is period-integrable. (`integrable_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L31)).

**Plane field along an orbit.** Proved result. Under the stated hypotheses, along a rotated meridian orbit the plane field is its stated finite frame sum. (`planeField_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L45)).

**Orbit phase integrand is integrable.** Proved result. Under the stated hypotheses, the phase times the frame component is integrable on the time-angular slice. (`integrable_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L62)).

**Label velocity as a slice integral.** Proved result. Under the stated hypotheses, the label velocity coefficient is the normalized phase-weighted orbit integral. (`labelVel_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L78)).

**Orbit slice evaluates the mode pairing.** Proved result. Under the stated hypotheses, the time-angular slice integral equals two pi times the label-coefficient pairing. (`slice_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L95)).

**Plane support pairing formula.** Proved result. Under the stated hypotheses, the pairing with the supported plane field equals the radius-weighted meridian mode integral. (`pairing_planeSet_moment`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L145)).

**Weighted label velocity is integrable.** Proved result. Under the stated hypotheses, the radius-weighted label velocity is integrable on the stated bounded meridian set. (`labelVel_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L207)).

**Row test is continuous.** Proved result. Under the stated hypotheses, the row test value is continuous. (`continuous_testValue'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L299)).

**Upper generator shape.** Proved result. Under the stated hypotheses, the upper-half generator equals the mode expansion on its owning rectangle. (`upper_generator_shape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L303)).

**Upper generator pairing.** Proved result. Under the stated hypotheses, the upper-half generator pairing equals the upper moment. (`generator_upper_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpper.lean#L331)).

### Breakdown.CertCell.InstanceMomentUpperOrbit

Builds the measure and coordinate changes for upper-half-plane rotational orbits. Periodicity and integration identities reduce the spatial moment to the weighted orbit integral. Appendix B: cell-system construction and finite certificate analysis.

**Positive-radius meridian.** Definition. This defines the full meridian half-plane with strictly positive radius. (`openHalf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L17)).

**Orbit-coordinate measure.** Definition. This defines the product measure on meridian radius-height, unit time and one angular period. (`orbitMeasure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L19)).

**Orbit-coordinate map.** Definition. `Breakdown.CertCell.Instance.Internal.MomentUpper.orbit` maps meridian, time and angle to time and the rotated spatial point. (`orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L22)).

**Period spacetime measure.** Definition. This defines volume in space times volume restricted to one time period. (`periodMeasure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L24)).

**Orbit map is measurable.** Proved result. Under the stated hypotheses, the orbit-coordinate map is measurable. (`measurable_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L26)).

**Positive meridian is measurable.** Proved result. Under the stated hypotheses, the positive-radius meridian domain is measurable. (`measurableSet_openHalf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L29)).

**Rotations repeat after two pi.** Proved result. Under the stated hypotheses, the rotation map repeats after one angular period. (`axialRot_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L31)).

**Lower integral in orbit coordinates.** Proved result. Under the stated hypotheses, the period lower integral equals the orbit integral with the radial Jacobian. (`lintegral_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L34)).

**Orbit radial density.** Definition. This defines the nonnegative radial density of the orbit coordinates. (`orbitDensity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L64)).

**Radial density is measurable.** Proved result. Under the stated hypotheses, the orbit radial density is measurable. (`measurable_orbitDensity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L66)).

**Push forward the orbit measure.** Proved result. Under the stated hypotheses, the radius-weighted orbit measure pushes forward to the period measure. (`map_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L69)).

**Orbit radius is positive a.e..** Proved result. Under the stated hypotheses, the orbit measure is supported almost everywhere at positive radius. (`ae_orbit_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L83)).

**Orbit measure is absolutely continuous.** Proved result. Under the stated hypotheses, the orbit measure is absolutely continuous with respect to its radial-density weighting. (`orbitMeasure_ac`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L90)).

**Bochner integral in orbit coordinates.** Proved result. Under the stated hypotheses, the integrable period function transforms to the radius-weighted orbit integral. (`integral_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L96)).

**Orbit pullback is measurable a.e..** Proved result. Under the stated hypotheses, the pulled-back period function is almost everywhere strongly measurable on orbit space. (`aestronglyMeasurable_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L113)).

**First cylindrical coordinate.** Proved result. Under the stated hypotheses, the first coordinate of the orbit point is radius times cosine. (`orbit_coord0`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L122)).

**Second cylindrical coordinate.** Proved result. Under the stated hypotheses, the second coordinate of the orbit point is radius times sine. (`orbit_coord1`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L125)).

**Third cylindrical coordinate.** Proved result. Under the stated hypotheses, the third coordinate of the orbit point is the meridian height. (`orbit_coord2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L128)).

**Orbit has the original meridian.** Proved result. Under the stated hypotheses, the meridian coordinates of the rotated point equal the original pair. (`pointPlane_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L131)).

**Orbit angle modulo a full turn.** Proved result. Under the stated hypotheses, the principal angle of the orbit differs from its parameter by an integer multiple of two pi. (`pointAngle_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L138)).

**Frame ignores integer full turns.** Proved result. Under the stated hypotheses, subtracting an integer number of full turns leaves the frame unchanged. (`frameUnit_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L148)).

**Phase ignores integer full turns.** Proved result. Under the stated hypotheses, subtracting an integer number of full turns leaves the label phase unchanged. (`labelPhase_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L152)).

**Inverse rotation as a frame pairing.** Proved result. Under the stated hypotheses, an inverse-rotated coordinate equals the corresponding frame inner product. (`rot_neg_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L161)).

**Frame norm equals one.** Proved result. Under the stated hypotheses, each cylindrical frame vector has norm one. (`norm_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L167)).

**Label phase norm equals one.** Proved result. Under the stated hypotheses, every label phase has complex norm one. (`norm_labelPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L173)).

**Conjugate label phase.** Proved result. Under the stated hypotheses, the conjugate label phase is the negative frequency exponential. (`conj_labelPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L176)).

**Meridian map is continuous.** Proved result. Under the stated hypotheses, the meridian-coordinate map is continuous. (`continuous_pointPlane'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L182)).

**Principal angle is measurable.** Proved result. Under the stated hypotheses, the principal-angle map is measurable. (`measurable_pointAngle'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L185)).

**Single coordinate as a unit multiple.** Proved result. Under the stated hypotheses, a single-coordinate spatial vector is the corresponding scalar multiple of the unit vector. (`single_smul_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L188)).

**Frame varies continuously.** Proved result. Under the stated hypotheses, each cylindrical frame vector is continuous in angle. (`continuous_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L192)).

**Phase varies continuously.** Proved result. Under the stated hypotheses, the label phase is continuous jointly in time and angle. (`continuous_labelPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L195)).

**Time-angular slice measure.** Definition. This defines the product of unit-time volume and one-period angular volume. (`sliceMeasure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L202)).

**Slice measure is s-finite.** Instance. This installs an s-finite measure instance for the finite time-angular slice. (`unnamed instance at line 204`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L204)).

**Period measure as a restriction.** Proved result. Under the stated hypotheses, the period product measure equals spacetime volume restricted to the unit time slab. (`periodMeasure_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L206)).

**Restrict to period measurability.** Proved result. Under the stated hypotheses, the indicated function is almost everywhere strongly measurable for the period measure. (`aesm_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L210)).

**Finite energy gives square integrability.** Proved result. Under the stated hypotheses, the squared field norm is integrable for the period measure. (`integrable_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L214)).

**Spatial norm in meridian coordinates.** Proved result. Under the stated hypotheses, the squared spatial norm is radial coordinate squared plus height squared. (`norm_sq_pointPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L226)).

**Bounded cylindrical support is finite.** Proved result. Under the stated hypotheses, the spatial preimage of the bounded meridian set has finite volume. (`volume_planeSet_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L231)).

**Cylindrical support is measurable.** Proved result. Under the stated hypotheses, the spatial preimage of the measurable meridian set is measurable. (`measurableSet_planeSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L252)).

**Cylindrical indicator is integrable.** Proved result. Under the stated hypotheses, the cylindrical support indicator is integrable over a period. (`integrable_planeSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L256)).

**Field from a plane coefficient.** Definition. This defines the supported real field from one harmonic label and its frame coefficients. (`planeField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L267)).

**Plane field is measurable.** Proved result. Under the stated hypotheses, the supported plane field is jointly measurable in time and space. (`measurable_planeField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L271)).

**Plane field norm bound.** Proved result. Under the stated hypotheses, the plane field norm is bounded by three times the coefficient bound on its support. (`norm_planeField_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMomentUpperOrbit.lean#L283)).

### Breakdown.CertCell.InstanceMoments

Proves compactness and continuity properties of the solid support and test profiles. These yield existence and formulas for the upper and lower moment functionals. Appendix B: cell-system construction and finite certificate analysis.

**Spatial coordinates are continuous.** Proved result. Under the stated hypotheses, each spatial coordinate projection is continuous. (`coord_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L16)).

**Cell solid is closed.** Proved result. Under the stated hypotheses, the solid associated with the cell rectangle is closed. (`solid_isClosed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L19)).

**Cell solid is bounded.** Proved result. Under the stated hypotheses, the solid associated with the cell rectangle is bounded. (`solid_isBounded`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L29)).

**Test values are continuous.** Proved result. Under the stated hypotheses, the row test values are continuous. (`testValue_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L49)).

**Label phase is continuous.** Proved result. Under the stated hypotheses, the label phase is jointly continuous in time and angle. (`labelPhase_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L55)).

**Label phase has norm one.** Proved result. For every temporal and angular label and all real σ and θ, the factor exp(i(2πkσ+nθ)) has complex modulus one. (`labelPhase_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L60)).

**Row phase factor has norm one.** Proved result. Under the stated hypotheses, the real-or-imaginary row factor has norm one. (`rowPartFactor_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L64)).

**Frame sign has norm one.** Proved result. Under the stated hypotheses, the complex embedding of a frame sign has norm one. (`frameSign_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L68)).

**Frame norm is bounded.** Proved result. Under the stated hypotheses, the frame vector norm is at most two. (`frameUnit_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L72)).

**Coordinate vector as a scalar multiple.** Proved result. Under the stated hypotheses, a single-coordinate vector is its coordinate times the corresponding unit vector. (`single_eq_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L89)).

**Single-coordinate map is continuous.** Proved result. Under the stated hypotheses, inserting a continuous scalar in one coordinate gives a continuous vector function. (`single_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L95)).

**Frame map is continuous.** Proved result. Under the stated hypotheses, the cylindrical frame vector varies continuously with angle. (`frameUnit_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L102)).

**Angle map is measurable.** Proved result. Under the stated hypotheses, the spatial angle is measurable. (`pointAngle_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L112)).

**One mode term is bounded.** Proved result. Under the stated hypotheses, the phase-weighted real coefficient times a frame vector is bounded by twice the coefficient norm. (`term_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L117)).

**Generator has a support bound.** Proved result. Under the stated hypotheses, the generator norm is uniformly bounded on its cell solid and zero outside it. (`generatorField_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L124)).

**Generator is measurable.** Proved result. Under the stated hypotheses, the generator field is jointly measurable in time and space. (`generatorField_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L174)).

**Period pairing is integrable.** Proved result. Under the stated hypotheses, the pointwise inner product is integrable over a period. (`pairing_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L220)).

**Period pairing as one integral.** Proved result. Under the stated hypotheses, the iterated period pairing equals the single spacetime product-measure integral. (`periodPairing_eq_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L270)).

**Split generator pairing by height.** Proved result. Under the stated hypotheses, the generator pairing is the sum of its upper-half and lower-half pairings. (`periodPairing_generator_halves`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L278)).

**Pairing splits into two moments.** Proved result. Under the stated hypotheses, the period pairing with a generator is the sum of its upper and lower half-space moments. (`generatorPairingMoments_of_halves`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceMoments.lean#L323)).

### Breakdown.CertCell.InstanceNormIdentity

Proves measurability and finite square integral for generator fields, then evaluates their pairings. The resulting norm identity relates analytic field norms to the finite generator Gram matrix. Appendix B: cell-system construction and finite certificate analysis.

**Single-coordinate vectors are continuous.** Proved result. Under the stated hypotheses, the vector with a scalar in one coordinate depends continuously on that scalar. (`continuous_single_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L20)).

**Frame vectors are continuous.** Proved result. Under the stated hypotheses, the cylindrical frame vector is continuous in angle. (`continuous_frame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L28)).

**Generator field is measurable.** Proved result. Under the stated hypotheses, the generator field is jointly measurable in time and space. (`generator_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L40)).

**Generator square integral is finite.** Proved result. Under the stated hypotheses, the generator has finite period squared-norm integral. (`generator_square_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L57)).

**Pairing with a linear combination.** Proved result. Under the stated hypotheses, pairing with a finite real linear combination equals the same combination of pairings. (`pairing_combination_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L76)).

**Normalizer squared is the inverse.** Proved result. Under the stated hypotheses, the inverse-square-root normalizer multiplied by itself is the matrix inverse. (`normalizer_square`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L95)).

**Normalized coordinates give inverse form.** Proved result. Under the stated hypotheses, the weighted sum of normalized coordinate squares equals the weighted inverse-matrix quadratic expression. (`quadratic_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L108)).

**Nonzero entries have equal weights.** Proved result. Under the stated hypotheses, the indicated pairing-matrix entry forces equality of the two row weights. (`weight_eq_of_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L148)).

**Row norm is an inverse Gram form.** Proved result. Under the stated hypotheses, the scaled squared row norm equals the generator-pairing quadratic expression weighted by the inverse Gram matrix. (`rowNormIdentity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceNormIdentity.lean#L165)).

### Breakdown.CertCell.InstanceOrthonormal

Uses a normalizing matrix that conjugates the Gram matrix to the identity. It proves that the corresponding linear combinations of generator fields have the prescribed orthonormal pairings. Appendix B: cell-system construction and finite certificate analysis.

**Normalizer makes the Gram matrix unit.** Proved result. Under the stated hypotheses, the inverse-square-root normalizer sandwiches the Gram matrix to the identity. (`normalizer_sandwich`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceOrthonormal.lean#L19)).

**Pairing two finite combinations.** Proved result. Under the stated hypotheses, the pairing of two finite linear combinations is the corresponding double weighted sum of pairings. (`pairing_of_combinations`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceOrthonormal.lean#L52)).

### Breakdown.CertCell.InstancePairByParts

Applies local integration by parts to actuator and row modes after controlling slice integrals and support. The resulting identity connects the analytic actuator pairing to the finite row data. Appendix B: cell-system construction and finite certificate analysis.

**Time slices have finite energy a.e..** Proved result. Under the stated hypotheses, the spatial lower integral is finite for almost every time in the period. (`slice_lintegral_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByParts.lean#L19)).

**A missing piece has zero sign.** Proved result. Under the stated hypotheses, a frequency outside the selected mode piece has piece sign zero. (`sgn_eq_zero_of_not_inPiece`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByParts.lean#L32)).

**Label exclusion removes piece membership.** Proved result. Under the stated hypotheses, the stated label exclusion implies that the harmonic is outside the mode piece. (`not_inPiece_of_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByParts.lean#L38)).

**Actuator integration by parts holds.** Proved result. Under the stated hypotheses, the multiplier pairing with the actuator equals the gradient pairing. (`actuatorPairingByParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByParts.lean#L50)).

### Breakdown.CertCell.InstancePairByPartsModes

Computes reflected velocity and gradient modes and transfers their integrals through the label involution. These identities provide the mode-level signs needed by the actuator integration-by-parts formula. Appendix B: cell-system construction and finite certificate analysis.

**Reflection reverses angular phase.** Proved result. Under the stated hypotheses, the reflected harmonic's phase at an angle equals the original phase at the negative angle. (`expFactor_flipLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L28)).

**Reflected gradient-mode pairing.** Proved result. Under the stated hypotheses, the gradient modes of the reflected fields transform with the product of their two frame signs. (`modeGrad_flip_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L32)).

**Reflected velocity-mode pairing.** Proved result. Under the stated hypotheses, the velocity modes of the reflected fields transform with the component frame sign. (`modeVel_flip_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L60)).

**Spatial reflection isometry.** Definition. `Breakdown.CertCell.InstancePair.Internal.ByPartsModes.flipEquiv` uses the established spatial reflection as a real linear isometry. (`flipEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L86)).

**Continuous linear reflection.** Definition. `Breakdown.CertCell.InstancePair.Internal.ByPartsModes.flipCLM` views the reflection isometry as a continuous linear map. (`flipCLM`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L88)).

**Isometric reflection evaluates.** Proved result. Under the stated hypotheses, the reflection isometry acts as the pointwise reflection. (`flipEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L90)).

**Continuous reflection evaluates.** Proved result. Under the stated hypotheses, the continuous linear reflection acts as the pointwise reflection. (`flipCLM_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L92)).

**Double reflection is identity.** Proved result. Under the stated hypotheses, reflecting a point twice returns the point. (`flipPoint_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L94)).

**Reflection preserves norm.** Proved result. Under the stated hypotheses, reflection leaves the spatial norm unchanged. (`norm_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L97)).

**Reflected vector field.** Definition. This defines the field by reflecting both its spatial argument and output. (`flippedField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L99)).

**Recover the original reflected field.** Proved result. Under the stated hypotheses, the original field at the reflected point is the reflection of the transformed field. (`flippedField_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L101)).

**Gradient of a reflected field.** Proved result. Under the stated hypotheses, the gradient of the reflected field is the original gradient conjugated by the reflection map. (`gradField_flipped`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L105)).

**Gradient reflection relation.** Proved result. Under the stated hypotheses, the original gradient on reflected arguments equals the reflected gradient action. (`gradField_flip_rel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L113)).

**Frame sign has absolute value one.** Proved result. Under the stated hypotheses, every frame sign has absolute value one. (`abs_frameSign`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L118)).

**Reflection preserves matrix squares.** Proved result. Under the stated hypotheses, conjugating a linear map by reflection preserves its column-square sum. (`entrySquareSum_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L122)).

**Reflect a spatial lower integral.** Proved result. Under the stated hypotheses, the lower integral is unchanged by spatial reflection. (`lintegral_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L128)).

**Spacetime reflection preserves measure.** Proved result. Under the stated hypotheses, reflection of the spatial component preserves spacetime volume. (`measurePreserving_flipSnd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L131)).

**Harmonic of a reflected label.** Proved result. Replacing a lattice label (a,b) by (−a,b−a) leaves its temporal frequency unchanged and reverses its azimuthal frequency. (`labelHarmonic_labelFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L135)).

**Frequency reflection is involutive.** Proved result. Under the stated hypotheses, reflecting a frequency twice returns it. (`flipLabel_flipLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L140)).

**Frequency reflection preserves negation.** Proved result. Under the stated hypotheses, reflecting a negative frequency negates the reflected frequency. (`flipLabel_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L143)).

**Reflection preserves cylindrical radius.** Proved result. Under the stated hypotheses, reflection preserves the radial meridian coordinate. (`pointPlane_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L146)).

**Frame signs are nonzero.** Proved result. Under the stated hypotheses, the complex embedding of each frame sign is nonzero. (`frameSign_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L151)).

**Reflected actuator has shape facts.** Proved result. Under the stated hypotheses, reflection transfers the actuator shape facts to the reflected label set. (`flipped_shape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L155)).

**Absent actuator modes have zero gradient.** Proved result. Under the stated hypotheses, the excluded actuator gradient mode vanishes almost everywhere. (`modeGrad_gradField_ae_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsModes.lean#L241)).

### Breakdown.CertCell.InstancePairByPartsMollify

Approximates weak gradient data by smooth fields in the square-integrable setting. Convergence of inner-product integrals justifies passing the integration-by-parts identity to the original field. Appendix B: cell-system construction and finite certificate analysis.

**Finite square integral gives L2.** Proved result. Under the stated hypotheses, the finite lower square integral gives membership in L2. (`memLp_two_of_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L18)).

**Gradient columns lie in L2.** Proved result. Under the stated hypotheses, each indicated gradient column lies in L2. (`column_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L24)).

**L2 convergence preserves pairing limits.** Proved result. Under the stated hypotheses, the pairings against a fixed L2 field converge under the stated L2 convergence. (`tendsto_integral_inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L33)).

**Pairing L2 fields is integrable.** Proved result. Under the stated hypotheses, the inner product of the two L2 fields is integrable. (`integrable_inner_of_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L54)).

**Derivative of a coordinate.** Proved result. Under the stated hypotheses, taking a coordinate commutes with the indicated directional derivative. (`fderiv_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L60)).

**Coordinates preserve smoothness.** Proved result. Under the stated hypotheses, each coordinate of the smooth vector test is smooth. (`coord_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L68)).

**Coordinates preserve compact support.** Proved result. Under the stated hypotheses, each coordinate of the compactly supported vector test has compact support. (`coord_hasCompactSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L72)).

**Coordinate test product is integrable.** Proved result. Under the stated hypotheses, the scalar test times the selected field coordinate is integrable. (`integrable_coord_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L76)).

**Coordinate integration by parts.** Proved result. Under the stated hypotheses, the second-derivative coordinate pairing equals the negative first-derivative pairing. (`coord_by_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L84)).

**Second columns are locally integrable.** Proved result. Under the stated hypotheses, the indicated diagonal second-derivative column is locally integrable. (`second_column_locallyIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L112)).

**Trace paired with a test.** Proved result. Under the stated hypotheses, the second-derivative trace pairing equals the negative sum of gradient-column pairings. (`trace_pairing_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L118)).

**Negative trace gives gradient pairing.** Proved result. Under the stated hypotheses, integration by parts identifies the negative second-derivative trace pairing with the matrix gradient pairing. (`trace_pairing_by_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairByPartsMollify.lean#L152)).

### Breakdown.CertCell.InstancePairGradModes

Establishes local integrability and weak gradient identities for cylindrical harmonic modes. These are the derivative hypotheses used in mode integration by parts. Appendix B: cell-system construction and finite certificate analysis.

**The spatial axis is null.** Proved result. Under the stated hypotheses, the cylindrical radius is nonzero almost everywhere in space. (`off_axis_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L27)).

**Actuator is locally integrable.** Proved result. Under the stated hypotheses, the actuator field is locally integrable in spacetime. (`field_locallyIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L42)).

**Actuator gradient is locally integrable.** Proved result. Under the stated hypotheses, the actuator gradient is locally integrable in spacetime. (`gradient_locallyIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L48)).

**Mode gradient is a weak gradient.** Proved result. Under the stated hypotheses, the real and imaginary velocity modes have the corresponding real and imaginary weak gradients. (`mode_weak_gradient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L59)).

**A zero field has zero weak gradient.** Proved result. Under the stated hypotheses, the indicated weak gradient of the zero field vanishes almost everywhere. (`gradient_ae_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L101)).

**Zero entries give a zero array.** Proved result. Under the stated hypotheses, the array is zero when all its indicated entries vanish. (`entries_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L115)).

**Gradient columns integrate along orbits.** Proved result. Under the stated hypotheses, the rotated gradient columns are integrable along time-angular orbits almost everywhere. (`column_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L124)).

**Rotate a vanishing gradient mode.** Proved result. Under the stated hypotheses, the vanishing gradient mode remains zero at the rotated point. (`rotated_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L158)).

**Actuator modes vanish off support.** Proved result. Under the stated hypotheses, an actuator gradient mode vanishes almost everywhere when both signs of its frequency are absent from the shape labels. (`actuatorGradientModes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairGradModes.lean#L172)).

### Breakdown.CertCell.InstancePairHalfPlane

Proves the reflection law for the pairing density and controls its integrability. It then reduces the full-space actuator pairing to twice the weighted upper-half-plane integral. Appendix B: cell-system construction and finite certificate analysis.

**Gradient-mode reflection condition.** Proposition definition. The interface requires that every reflected gradient mode agrees almost everywhere with the signed original mode. (`FlipModes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L24)).

**Field reflection gives mode reflection.** Proved result. Under the stated hypotheses, the almost-everywhere field reflection law implies the gradient-mode reflection condition. (`flipModes_of_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L28)).

**Perturbations have reflected modes.** Proved result. Under the stated hypotheses, an admitted perturbation supplies the gradient-mode reflection condition. (`flipModes_of_perturbation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L35)).

**Pair density respects reflection.** Proved result. Under the stated hypotheses, the reflected-frequency pair density agrees almost everywhere with the original density at the reflected point. (`ae_pairDensity_flip_modes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L41)).

**Squared complex norm is nonnegative.** Proved result. Under the stated hypotheses, the finite complex squared norm is nonnegative. (`cnormSq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L49)).

**Self-pairing density is a square.** Proved result. Under the stated hypotheses, the self-pairing density equals the squared gradient-mode norm. (`pairDensity_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L52)).

**Bound the matrix pairing.** Proved result. Under the stated hypotheses, the norm of the complex matrix pairing is bounded by the sum of the two squared norms. (`norm_cdotMat_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L59)).

**Gradient mode has finite half-plane norm.** Proved result. Under the stated hypotheses, the radius-weighted gradient-mode square has finite half-plane lower integral. (`halfPlane_modeNorm_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L66)).

**Label gradient is measurable a.e..** Proved result. Under the stated hypotheses, the label-gradient profile is almost everywhere strongly measurable on the half-plane. (`aesm_labelGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L95)).

**Squared mode norm is measurable a.e..** Proved result. Under the stated hypotheses, the squared norm of the measurable finite complex array is almost everywhere strongly measurable. (`aesm_cnormSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L108)).

**Fold a rotated meridian point.** Proved result. Under the stated hypotheses, radius and absolute height of the orbit point give the stated meridian point. (`rot_plane_coords`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L114)).

**Gradient modes vanish outside support.** Proved result. Under the stated hypotheses, the indicated label-gradient mode is zero outside its support. (`labelGrad_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L127)).

**Reduce pairing to the half-plane.** Proved result. Under the stated hypotheses, the period gradient pairing equals four pi times the finite supported half-plane mode pairing. (`halfPlanePairing_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L147)).

**Half-plane pairing formula.** Proved result. Under the stated hypotheses, the period gradient pairing equals four pi times the finite supported half-plane mode pairing. (`halfPlanePairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairHalfPlane.lean#L254)).

### Breakdown.CertCell.InstancePairShares

Turns the actuator input formula and exact local profiles into the prescribed pairing shares. This is the exact-profile route from analytic pairings to finite share data. Appendix B: cell-system construction and finite certificate analysis.

**Actuator supplies pairing input.** Proved result. Under the stated hypotheses, the actuator gradient satisfies the pairing-input conditions. (`actuator_input`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairShares.lean#L20)).

**Exact profiles bound pairing shares.** Proved result. Under the stated hypotheses, exact actuator and pin profiles bound the total pairing share by the multiplier and pin pairings plus the allowed quadratic error. (`pairSharesFromExactProfiles`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairShares.lean#L72)).

### Breakdown.CertCell.InstancePairSharesCut

Partitions a cell cover into disjoint first-cover pieces and cuts fields onto those pieces. It proves that the piecewise pairings sum to the covered pairing with the stated boundary and null-set conditions. Appendix B: cell-system construction and finite certificate analysis.

**Fold space to radius and height.** Definition. `Breakdown.CertCell.InstancePair.Internal.cylFold` maps space to cylindrical radius and absolute height. (`cylFold`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L21)).

**First cell in a finite cover.** Definition. This defines the part of a rectangle left after removing all earlier rectangles. (`firstCover`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L23)).

**Field restricted to its first cover.** Definition. `Breakdown.CertCell.InstancePair.Internal.cutField` restricts the field to points assigned to the specified first-cover cell. (`cutField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L26)).

**Pairing within a rectangle.** Definition. This defines the sum of radius-weighted gradient-mode pairings over a rectangle. (`rectPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L30)).

**Period gradient pairing.** Definition. This defines the time-period integral of the matrix inner product. (`pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L34)).

**Input conditions for cell pairings.** Proposition structure. The interface requires that the matrix field is measurable, periodic, square-integrable, reflection-compatible and supported in the stated cells and modes. (`PairInput`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L37)).

**Cylindrical folding is continuous.** Proved result. Under the stated hypotheses, the radius and absolute-height folding map is continuous. (`continuous_cylFold`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L47)).

**Folding ignores axial rotation.** Proved result. Under the stated hypotheses, axial rotation leaves the folded coordinates unchanged. (`cylFold_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L51)).

**Reflection coordinate signs.** Proved result. Under the stated hypotheses, reflection fixes the first coordinate and negates the other two. (`flipPoint_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L58)).

**Folding ignores reflection.** Proved result. Under the stated hypotheses, spatial reflection leaves the folded coordinates unchanged. (`cylFold_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L61)).

**Reflection fixes zero.** Proved result. Under the stated hypotheses, the origin is fixed by spatial reflection. (`flipPoint_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L65)).

**Rotation fixes zero.** Proved result. Under the stated hypotheses, the origin is fixed by axial rotation. (`axialRot_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L68)).

**Fold a half-plane point.** Proved result. Under the stated hypotheses, folding the stated meridian point gives the original half-plane coordinates. (`cylFold_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L71)).

**First-cover cells are measurable.** Proved result. Under the stated hypotheses, subtracting earlier rectangles leaves a measurable first-cover set. (`measurableSet_firstCover`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L82)).

**First cover stays in its rectangle.** Proved result. Under the stated hypotheses, each first-cover cell is contained in its original rectangle. (`firstCover_subset`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L86)).

**First-cover pieces are disjoint.** Proved result. Under the stated hypotheses, membership in two distinct first-cover pieces contradicts the first-cover definition. (`firstCover_disjoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L89)).

**Covered points have a first owner.** Proved result. Under the stated hypotheses, a point belonging to the finite cover belongs to some first-cover piece. (`exists_firstCover`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L95)).

**Cut fields reconstruct the field.** Proved result. Under the stated hypotheses, summing the first-cover restricted fields reconstructs the original field. (`sum_cutField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L106)).

**Modes of an invariant indicator.** Proved result. Under the stated hypotheses, an invariant support indicator pulls through the gradient-mode average as the corresponding membership test. (`modeGrad_indicator`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L129)).

**Matrix square is nonnegative.** Proved result. Under the stated hypotheses, the matrix column-square sum is nonnegative. (`matSq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L144)).

**Zero matrix has zero square.** Proved result. Under the stated hypotheses, the zero linear map has zero column-square sum. (`matSq_zero'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L147)).

**Matrix square is continuous.** Proved result. Under the stated hypotheses, the matrix column-square function is continuous. (`continuous_matSq''`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L150)).

**Matrix inner product is continuous.** Proved result. Under the stated hypotheses, the matrix inner product is jointly continuous in its two inputs. (`continuous_matInner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L153)).

**Matrix pairing distributes over sums.** Proved result. Under the stated hypotheses, the matrix inner product with a finite sum equals the sum of the inner products. (`matInner_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L158)).

**Matrix pairing by square sums.** Proved result. Under the stated hypotheses, the absolute matrix pairing is bounded by the sum of the two matrix squares. (`abs_matInner_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L164)).

**Period measure as a time restriction.** Proved result. Under the stated hypotheses, the product of restricted time and space volume is volume restricted to the time slab. (`periodMeasure_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L173)).

**Matrix pairing is period-integrable.** Proved result. Under the stated hypotheses, the matrix inner product of the stated fields is integrable over a period. (`integrable_matInner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L178)).

**Period pairing distributes over sums.** Proved result. Under the stated hypotheses, the period pairing with a finite sum is the sum of period pairings. (`pairing_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L207)).

**Radius-zero line has zero volume.** Proved result. Under the stated hypotheses, the radius-zero line has plane volume zero. (`null_fst_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L227)).

**Height-zero line has zero volume.** Proved result. Under the stated hypotheses, the height-zero line has plane volume zero. (`null_snd_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L234)).

**Half-plane is measurable.** Proved result. Under the stated hypotheses, the chosen half-plane is a measurable set. (`measurableSet_halfPlane'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L241)).

**First-cover cell equals its cell a.e..** Proved result. Under the stated hypotheses, the stated geometric conditions make each first-cover cell agree with its rectangle almost everywhere. (`firstCover_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L244)).

**Pairing is the sum of cell integrals.** Proved result. Under the stated hypotheses, the period pairing equals four pi times the sum of the rectangle mode pairings. (`pairing_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesCut.lean#L261)).

### Breakdown.CertCell.InstancePairSharesPin

Verifies reflection and pinning identities for cylindrical frame modes and exact profile shares. These calculations show that the constructed shares satisfy the finite pin constraints. Appendix B: cell-system construction and finite certificate analysis.

**Linear spatial reflection.** Definition. `Breakdown.CertCell.InstancePair.Internal.flipLin` packages the spatial reflection as a linear map. (`flipLin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L21)).

**Linear reflection action.** Proved result. Under the stated hypotheses, the linear reflection has the pointwise reflection action. (`flipLin_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L29)).

**Reflecting a label twice.** Proved result. Under the stated hypotheses, two successive label reflections give the original label. (`labelFlip_labelFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L31)).

**Frame ignores integer angle periods.** Proved result. Under the stated hypotheses, adding an integer multiple of two pi preserves the frame vectors. (`frameUnit_add_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L34)).

**Frame matrix ignores full turns.** Proved result. Under the stated hypotheses, adding an integer multiple of two pi preserves the frame reconstruction map. (`frameMap_add_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L42)).

**Frame reflection rule.** Proved result. Under the stated hypotheses, reflection gives the frame sign times the vector at the negative angle. (`flipPoint_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L46)).

**Move reflection across an inner product.** Proved result. Under the stated hypotheses, reflection can be moved from one argument of the real inner product to the other. (`inner_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L54)).

**Frame reconstruction formula.** Proved result. Under the stated hypotheses, the frame matrix map is the double sum of coefficient-weighted frame projections. (`frameMap_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L59)).

**Frame reconstruction preserves sums.** Proved result. Under the stated hypotheses, the frame reconstruction of a finite sum is the sum of the reconstructed maps. (`frameMap_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L65)).

**Reflect a frame matrix.** Proved result. Under the stated hypotheses, conjugating the frame map by reflection changes angle sign and multiplies entries by their frame signs. (`flip_frameMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L72)).

**Reindex by reflected labels.** Proved result. Under the stated hypotheses, summing over the reflection-invariant label set is unchanged by label reflection. (`sum_labelFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L85)).

**Angle of a reflected point.** Proved result. Under the stated hypotheses, the reflected principal angle is the negative original angle plus an integer full turn. (`pointAngle_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L90)).

**Label phase at a reflected angle.** Proved result. Under the stated hypotheses, negating angle and adding full turns has the same phase as reflecting the label. (`labelPhase_flip_angle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L102)).

**Meridian point under reflection.** Proved result. Under the stated hypotheses, reflection preserves the meridian radius and negates its height. (`pointPlane_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L114)).

**Cell solid via folded coordinates.** Proved result. Under the stated hypotheses, a point belongs to the cell solid exactly when its folded coordinates belong to the cell rectangle. (`mem_solid_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L118)).

**Reflected matrix coefficients.** Proved result. Under the stated hypotheses, the reflected phase-coefficient sum acquires the two frame signs. (`planeValue_sum_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L125)).

**Pin field reflection law.** Proved result. Under the stated hypotheses, the cell matrix field transforms by reflection on both its input and output. (`pin_field_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L177)).

**Pin field is supported in cells.** Proved result. Under the stated hypotheses, a nonzero cell matrix field value has folded coordinates in one of its cell rectangles. (`pin_field_support`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L202)).

**Meridian point coordinates.** Proved result. Under the stated hypotheses, the meridian point has coordinates radius, zero and height. (`planePoint_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L213)).

**Rotate the unit basis.** Proved result. Under the stated hypotheses, rotating a unit basis vector gives the corresponding frame vector. (`axialRot_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L216)).

**Inverse-rotated coordinate.** Proved result. Under the stated hypotheses, an inverse-rotated coordinate is the corresponding frame inner product. (`axialRot_neg_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L222)).

**Frame vectors are orthonormal.** Proved result. Under the stated hypotheses, the frame-vector inner product is one on equal indices and zero otherwise. (`frameUnit_orth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L232)).

**Read a frame matrix entry.** Proved result. Under the stated hypotheses, pairing the frame-map image of a basis frame vector with another recovers the corresponding matrix entry. (`inner_frameMap_frame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L240)).

**Label phase ignores full turns.** Proved result. Under the stated hypotheses, integer angular full turns preserve the label phase. (`labelPhase_add_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L246)).

**Coordinates of a rotated meridian.** Proved result. Under the stated hypotheses, the rotated meridian point has the stated cosine, sine and height coordinates. (`rot_planePoint_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L257)).

**Orbit angle modulo full turns.** Proved result. Under the stated hypotheses, the principal angle of a positive-radius rotated point differs by an integer full turn. (`pointAngle_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L264)).

**Orbit preserves meridian coordinates.** Proved result. Under the stated hypotheses, the meridian coordinates of a rotated meridian point are the original coordinates. (`pointPlane_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L278)).

**Pin field in rotating coordinates.** Proved result. Under the stated hypotheses, the rotating-frame pin field is the finite sum of its cell-supported phase coefficients. (`pin_field_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L289)).

**Time-angular plane wave.** Definition. This defines the complex exponential with the given time and angular frequencies. (`planeWave`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L310)).

**Angular plane-wave mean.** Definition. This defines the angular average, which vanishes unless the angular frequency is zero. (`waveMean`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L313)).

**Plane-wave product.** Proved result. Under the stated hypotheses, multiplying plane waves adds their frequency pairs. (`planeWave_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L316)).

**Plane-wave conjugation.** Proved result. Under the stated hypotheses, complex conjugation negates the plane-wave frequency. (`planeWave_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L324)).

**Fourier factor is a negative wave.** Proved result. Under the stated hypotheses, the mode-extraction factor equals the plane wave with negated frequency. (`expFactor_planeWave`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L332)).

**Label phase is its plane wave.** Proved result. Under the stated hypotheses, the label phase equals the plane wave at the label's harmonic frequency. (`labelPhase_planeWave`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L340)).

**Label harmonics preserve negation.** Proved result. Under the stated hypotheses, negating a label negates its harmonic frequency. (`labelHarmonic_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L343)).

**Plane waves are continuous in angle.** Proved result. Under the stated hypotheses, a plane wave is continuous in its angular argument. (`continuous_planeWave_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L351)).

**Wave mean is continuous in time.** Proved result. Under the stated hypotheses, the angular wave mean is continuous in time. (`continuous_waveMean`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L355)).

**Angular integral of a plane wave.** Proved result. Under the stated hypotheses, the angular integral equals the scalar coefficient times the defined angular mean. (`planeWave_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L359)).

**Nonzero wave mean integrates to zero.** Proved result. Under the stated hypotheses, the permitted nonzero harmonic has zero time integral after angular averaging. (`waveMean_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L375)).

**Excluded finite modes average to zero.** Proved result. Under the stated hypotheses, the extraction integral vanishes when the requested frequency is absent from the finite mode sum. (`modeSum_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L385)).

**Pin modes vanish outside their labels.** Proved result. Under the stated hypotheses, the pin-field mode is zero outside the specified harmonic support. (`pin_modes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L424)).

**Spatial height-zero plane is null.** Proved result. Under the stated hypotheses, the spatial height-zero plane has volume zero. (`plane_two_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L452)).

**Height is nonzero a.e. in spacetime.** Proved result. Under the stated hypotheses, the spatial height coordinate is nonzero almost everywhere in spacetime. (`ae_height_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L464)).

**Pin field supplies pairing input.** Proved result. Under the stated hypotheses, the pin field satisfies the cell pairing-input conditions. (`pin_input`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSharesPin.lean#L472)).

### Breakdown.CertCell.InstancePairStatements

Defines the admissible pairing entries, actuator support condition and exact or surrogate profile-share interfaces. It specifies the obligations needed to reconstruct a global pairing from local shares. Appendix B: cell-system construction and finite certificate analysis.

**Exact cell pairing profiles.** Proposition structure. The interface requires that actuator and pin labels are included and their stored profiles equal the actual gradient modes on each cell. (`IsPairEntry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairStatements.lean#L18)).

**Actuators are supported in cells.** Proposition definition. The interface requires that every nonzero actuator value has folded coordinates in a cell rectangle. (`ActuatorSupportInCells`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairStatements.lean#L27)).

**Exact pair-share interface.** Proposition definition. The interface requires that exact actuator and pin profiles bound the total pairing share by the multiplier and pin pairings plus the allowed quadratic error. (`PairSharesFromExactProfiles`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairStatements.lean#L30)).

**Surrogate pair-share interface.** Proposition definition. The interface requires that surrogate profiles bound the total pairing share by exact pairings, the quadratic error and the cell strain slack. (`PairSharesFromSurrogateProfiles`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairStatements.lean#L42)).

**Actuator integration-by-parts interface.** Proposition definition. The interface requires that the actuator multiplier equals its period gradient pairing under the actuator and perturbation conditions. (`ActuatorPairingByParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairStatements.lean#L55)).

**Actuator gradient support interface.** Proposition definition. The interface requires that an actuator gradient mode vanishes almost everywhere when both frequency signs are absent from the shape labels. (`ActuatorGradientModes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairStatements.lean#L62)).

**Half-plane pairing interface.** Proposition definition. The interface requires that the period gradient pairing reduces to four pi times the finite supported half-plane mode pairing. (`HalfPlanePairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairStatements.lean#L67)).

### Breakdown.CertCell.InstancePairSurrogate

Bounds the difference between exact and surrogate profile pairings by weighted square errors. Young-type inequalities then yield the enclosure used by the surrogate-share interface. Appendix B: cell-system construction and finite certificate analysis.

**Weighted square-integrability condition.** Proposition definition. The interface requires that the scalar profile is measurable and its radius-weighted squared norm is integrable. (`SqWeighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L21)).

**Young bound for a surrogate entry.** Proved result. Under the stated hypotheses, the coefficient-weighted real cross term is at most the positive weight times the field amplitude squared plus the coefficient and error square sums divided by four times that weight. (`surr_entry_young`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L24)).

**Young bound for a surrogate matrix.** Proved result. Under the stated hypotheses, the matrix cross term is bounded by the gradient square and the coefficient-weighted profile error square. (`surr_point_young`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L51)).

**Weighted scalar pairing is integrable.** Proved result. Under the stated hypotheses, the radius-weighted product of one profile and the conjugate of another is integrable. (`surr_integrable_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L71)).

**Weighted matrix pairing is integrable.** Proved result. Under the stated hypotheses, the finite radius-weighted matrix pairing sum is integrable. (`surr_integrable_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L83)).

**Real weighted pairing is integrable.** Proved result. Under the stated hypotheses, the real part of the radius-weighted matrix pairing is integrable. (`surr_integrable_re`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L94)).

**Real part passes through the integral.** Proved result. Under the stated hypotheses, the real part of the complex weighted pairing integral equals the integral of its real part. (`surr_re_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L100)).

**Weighted matrix square is integrable.** Proved result. Under the stated hypotheses, the radius-weighted sum of entry squared norms is integrable. (`surr_integrable_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L110)).

**Subtract weighted square profiles.** Proved result. Under the stated hypotheses, subtracting the profiles preserves weighted square integrability. (`surr_sqw_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L120)).

**One-label surrogate bound.** Proved result. Under the stated hypotheses, replacing the exact profile by its surrogate costs the stated strain term and profile error square. (`surr_label_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L133)).

**Restrict a cell to the half-plane.** Proved result. Under the stated hypotheses, the stated cell has the same restricted measure as its intersection with the half-plane. (`surr_ae_eq_halfPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L202)).

**Gradient mode is weighted square.** Proved result. Under the stated hypotheses, the gradient-mode component satisfies the weighted square-integrability condition on the cell. (`surr_sqw_gradAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L221)).

**Bounded profile is weighted square.** Proved result. Under the stated hypotheses, the bounded measurable profile has integrable radius-weighted square on the stated set. (`surr_sqw_bounded`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L257)).

**Cell pairing term.** Definition. This defines the radius-weighted pairing of a perturbation gradient mode with the chosen profile. (`cellPairTerm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L271)).

**Split the pairing share by inputs.** Proved result. Under the stated hypotheses, the cell pairing share splits into actuator terms weighted by κ and pin terms weighted by twice ζ. (`surr_share_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L277)).

**One-cell surrogate estimate.** Proved result. Under the stated hypotheses, the surrogate cell share is bounded by the exact share, the strain slack and the stated profile error. (`surr_cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L287)).

**Exact actuator and pin profiles.** Definition. This defines the profiles using actual actuator gradients and pin fields. (`exactPairProfiles`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L357)).

**Surrogate shares from error control.** Proved result. Under the stated hypotheses, surrogate profile shares are bounded by the exact multiplier and pin pairings, the quadratic error and the cell strain slack. (`pairSharesFromSurrogateProfiles_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L366)).

**Surrogate profiles bound shares.** Proved result. Under the stated hypotheses, surrogate profile shares are bounded by the exact multiplier and pin pairings, the quadratic error and the cell strain slack. (`pairSharesFromSurrogateProfiles`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairSurrogate.lean#L416)).

### Breakdown.CertCell.InstancePairingFormula

Computes harmonic orthogonality, reflected generator pairings and the finite block pairing matrix. These formulas identify the analytic pairings of the constructed basis fields. Appendix B: cell-system construction and finite certificate analysis.

**Harmonics preserve label negation.** Proved result. Under the stated hypotheses, the harmonic of a negative label is the negative harmonic. (`harm_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L17)).

**Harmonic equality detects label equality.** Proved result. Under the stated hypotheses, equal harmonic frequencies are equivalent to equal labels under the stated order condition. (`harm_eq_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L20)).

**Opposite harmonics and opposite labels.** Proved result. Under the stated hypotheses, opposite harmonic frequencies are equivalent to opposite labels. (`harm_eq_neg_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L28)).

**Label reflection is involutive.** Proved result. Under the stated hypotheses, reflecting a label twice gives the original label. (`flip_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L32)).

**Label reflection preserves negation.** Proved result. Under the stated hypotheses, reflection of a negative label is the negative reflected label. (`flip_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L35)).

**Reflected-label equality.** Proved result. Under the stated hypotheses, equality of reflected labels is equivalent to equality of the original labels. (`flip_eq_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L38)).

**Reflected harmonic equality.** Proved result. Under the stated hypotheses, equality of the reflected harmonic frequencies is equivalent to label equality. (`harm_flip_eq_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L41)).

**Opposite reflected harmonics.** Proved result. Under the stated hypotheses, opposite reflected harmonic frequencies are equivalent to opposite labels. (`harm_flip_eq_neg_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L45)).

**Identify the cylindrical frame.** Proved result. Under the stated hypotheses, the cell frame vector equals the spectral-block frame vector. (`frameUnit_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L49)).

**Frame vectors are orthonormal.** Proved result. Under the stated hypotheses, the real inner product of frame vectors is the Kronecker delta. (`frameUnit_inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L53)).

**Inner product of frame sums.** Proved result. Under the stated hypotheses, the inner product of two frame expansions is the sum of coordinate products. (`inner_frame_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L58)).

**Unit indicator.** Definition. This defines one on the chosen set and zero elsewhere. (`unitOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L66)).

**Real generator coefficient.** Definition. This defines the phase-weighted real test coefficient with the appropriate upper or reflected lower label. (`coefAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L70)).

**Generator shape condition.** Proposition definition. The interface requires that the generator equals the finite frame expansion restricted to its cell solid. (`GenShape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L77)).

**Inner product of generators.** Proved result. Under the stated hypotheses, the generator inner product is the product of support indicators times the coefficient dot product. (`inner_gen`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L81)).

**Angle is measurable.** Proved result. Under the stated hypotheses, the spatial angle map is measurable. (`measurable_pointAngle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L91)).

**Meridian coordinates are continuous.** Proved result. Under the stated hypotheses, the meridian-coordinate map is continuous. (`continuous_pointPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L94)).

**Test coefficient is continuous.** Proved result. Under the stated hypotheses, the row test coefficient is continuous. (`continuous_testValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L97)).

**Cell solid is measurable.** Proved result. The three-dimensional solid obtained by revolving a closed meridian cell rectangle is a measurable subset of R³. (`measurableSet_solid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L101)).

**Unit indicator is measurable.** Proved result. Under the stated hypotheses, the unit indicator of a measurable set is measurable. (`measurable_unitOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L107)).

**Split generator coefficients by height.** Proved result. Under the stated hypotheses, the generator coefficient is the upper expression above the plane and the signed reflected expression below it. (`coefAt_eq_ite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L112)).

**Generator coefficient is measurable.** Proved result. Under the stated hypotheses, the real generator coefficient is jointly measurable in time and space. (`measurable_coefAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L121)).

**Row factor has norm one.** Proved result. Under the stated hypotheses, the row-part factor has norm one. (`norm_rowPartFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L132)).

**Frame sign has norm one.** Proved result. Under the stated hypotheses, the complex frame sign has norm one. (`norm_frameSign`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L135)).

**Frame signs cancel in pairs.** Proved result. Under the stated hypotheses, multiplying a frame sign by itself gives one. (`frameSign_mul_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L138)).

**Cancel paired frame signs.** Proved result. Under the stated hypotheses, the two frame signs cancel in the indicated product. (`frameSign_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L141)).

**Label phase has norm one.** Proved result. For every temporal and angular label and all real σ and θ, the factor exp(i(2πkσ+nθ)) has complex modulus one. (`norm_labelPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L145)).

**Uniform bound for cell tests.** Proved result. Under the stated hypotheses, all components of the row test have a common nonnegative bound on the cell rectangle. (`exists_testBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L148)).

**Bound a generator coefficient.** Proved result. Under the stated hypotheses, the coefficient magnitude is bounded by the stated test bound. (`abs_coefAt_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L159)).

**Cell solid is bounded.** Proved result. For every meridian cell box, the solid obtained by rotation about the axis is bounded in R³. (`solid_bounded`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L174)).

**Generator pairing is integrable.** Proved result. Under the stated hypotheses, the inner product of the two generators is integrable over a period. (`integrable_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L192)).

**Generator pairing in cylinder variables.** Proved result. Under the stated hypotheses, the generator pairing is the radius-weighted cylindrical integral of the time-angular inner product. (`periodPairing_cyl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L231)).

**Label chosen by the side of the plane.** Definition. `Breakdown.CertCell.Instance.Internal.PairingFormula.sideLabel` selects the original label above the plane and the reflected label below it. (`sideLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L243)).

**Coefficient chosen by the side.** Definition. `Breakdown.CertCell.Instance.Internal.PairingFormula.sideValue` selects the upper coefficient or its signed reflected lower coefficient. (`sideValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L245)).

**Product of two real phases.** Definition. This defines the product of the two real phase-weighted coefficients. (`phaseProd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L250)).

**Density for a generator pair.** Definition. This defines the equal-label and opposite-label contributions to the complex pairing density. (`pairDensity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L253)).

**Radial pairing density.** Definition. This defines the radius-weighted real pairing density restricted to both owning rectangles. (`radialDensity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L264)).

**Cylinder belongs to a cell solid.** Proved result. Under the stated hypotheses, a cylindrical point belongs to the solid exactly when its radius and absolute height lie in the rectangle. (`cyl_mem_solid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L268)).

**Solid indicator in cylinder coordinates.** Proved result. Under the stated hypotheses, the solid indicator equals the rectangle indicator at radius and absolute height. (`unitOn_cyl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L276)).

**Generator pairing at a cylinder point.** Proved result. Under the stated hypotheses, the cylindrical generator inner product is the support-weighted finite sum of phase products. (`pairing_at_cyl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L283)).

**Phase is angularly periodic.** Proved result. Under the stated hypotheses, the label phase repeats after two pi. (`labelPhase_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L302)).

**Real phase product is continuous.** Proved result. Under the stated hypotheses, the phase product is continuous jointly in time and angle. (`continuous_phaseProd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L311)).

**Mean of a phase product.** Proved result. Under the stated hypotheses, the time-angular mean retains equal and opposite harmonic frequencies with the stated pi factor. (`slice_mean`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L316)).

**Integrate the finite phase sum.** Proved result. Under the stated hypotheses, the weighted finite phase sum integrates to its equal- and opposite-frequency contributions. (`slice_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L339)).

**Combine upper and lower pair terms.** Proved result. Under the stated hypotheses, the side-dependent frequency terms equal the pairing density at absolute height. (`sum_terms`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L362)).

**Angular pairing gives radial density.** Proved result. Under the stated hypotheses, the radius-weighted time-angular pairing equals pi times the folded radial density. (`angular_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L381)).

**Fold an even-height integral.** Proved result. Under the stated hypotheses, integrating a function of absolute height over the full meridian gives twice its positive-height integral. (`fold_abs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L407)).

**A fixed branch preserves continuity.** Proved result. Under the stated hypotheses, a constant propositional branch choosing the function or zero preserves continuity. (`continuous_ite_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L442)).

**Pairing density is continuous.** Proved result. Under the stated hypotheses, the generator-pairing density is continuous. (`continuous_pairDensity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L448)).

**Rectangle is measurable.** Proved result. Under the stated hypotheses, the cell rectangle is measurable. (`measurableSet_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L455)).

**Folded radial density is integrable.** Proved result. Under the stated hypotheses, the radial pairing density evaluated at absolute height is integrable. (`integrable_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L458)).

**Half-plane integral is the matrix entry.** Proved result. Under the stated hypotheses, twice pi times the positive-half-plane radial density integral is the test-pairing matrix entry. (`half_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L495)).

**Generator pairing equals matrix entry.** Proved result. Under the stated hypotheses, the period pairing of the two generators equals the corresponding test-pairing matrix entry. (`pairing_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L550)).

**Generator Gram matrix formula.** Proved result. Under the stated hypotheses, the generator field Gram matrix equals the finite test-pairing matrix. (`generatorPairingMatrixFormula`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingFormula.lean#L569)).

### Breakdown.CertCell.InstancePairingPosDef

Factors each pairing block and proves positivity of the resulting quadratic form. The block analysis supplies the positive-definiteness condition needed for normalization and inversion. Appendix B: cell-system construction and finite certificate analysis.

**Test-block matrix entry.** Definition. This defines the radius-weighted complex inner product of two cell test fields. (`blockEntry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L22)).

**Factor for a self-opposite label.** Definition. `Breakdown.CertCell.Instance.Internal.RowPairing.blockFactor` uses factor two for a label equal to its negative and factor one otherwise. (`blockFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L27)).

**Complex vector from real rows.** Definition. `Breakdown.CertCell.Instance.Internal.RowPairing.rowVec` assembles complex test coordinates from the matching real row components. (`rowVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L29)).

**Block factor is positive.** Proved result. Under the stated hypotheses, the self-opposite-label factor is strictly positive. (`blockFactor_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L34)).

**Read a test-block entry.** Proved result. Under the stated hypotheses, the test-block matrix entry equals the defined weighted test integral. (`testBlockMatrix_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L37)).

**Cell polynomial is continuous.** Proved result. Under the stated hypotheses, cell polynomial evaluation is continuous. (`eval_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L41)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L45)).

**Block-entry integrand is integrable.** Proved result. Under the stated hypotheses, the weighted test-field pairing is integrable on the cell rectangle. (`blockEntry_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L47)).

**Move the real part outside integration.** Proved result. Under the stated hypotheses, the real weighted integral equals the real part of the complex weighted integral. (`integral_re_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L56)).

**Test-block entries conjugate.** Proved result. Under the stated hypotheses, transposing the block-entry indices gives the complex conjugate. (`blockEntry_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L66)).

**Finite conditional coordinate sum.** Proved result. Under the stated hypotheses, the finite sum selecting one natural-number coordinate gives the corresponding entry or zero. (`sum_fin_ite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L77)).

**Same block fixes the label.** Proved result. Under the stated hypotheses, the stated same-block conditions imply equal labels. (`sameBlock_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L92)).

**Same-block relation is symmetric.** Proved result. Under the stated hypotheses, the same-block relation remains true after swapping the rows. (`sameBlock_symm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L96)).

**Different blocks have zero entry.** Proved result. Under the stated hypotheses, the pairing-matrix entry is zero between the indicated separate blocks. (`entry_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L99)).

**Pairing entry from a complex block.** Proved result. Under the stated hypotheses, the real pairing entry equals the stated scaled real part of its complex block entry. (`entry_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L103)).

**Pairing matrix is symmetric.** Proved result. Under the stated hypotheses, swapping row indices preserves the real pairing-matrix entry. (`entry_symm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L150)).

**Conjugate a conditional value.** Proved result. Under the stated hypotheses, conjugating a conditional entry conjugates the nonzero branch. (`star_ite_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L164)).

**Block matrix applied to row vector.** Proved result. Under the stated hypotheses, the complex test-block action expands into the matching real-row sum. (`mulVec_rowVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L168)).

**Complex row quadratic form.** Proved result. Under the stated hypotheses, the block quadratic form expands into the double sum over matching real rows. (`quad_rowVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L182)).

**Real block quadratic form.** Proved result. Under the stated hypotheses, the real pairing block form equals the positive scale times its complex row-vector form. (`block_quad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L212)).

**A nonzero real row gives a nonzero block.** Proved result. Under the stated hypotheses, the indicated nonzero real coordinate makes its reconstructed complex block vector nonzero. (`rowVec_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L232)).

**Block quadratic form is nonnegative.** Proved result. Under the stated hypotheses, the positive test block gives a nonnegative quadratic value. (`block_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L253)).

**Nonzero block quadratic form is positive.** Proved result. Under the stated hypotheses, the nonzero block vector has strictly positive quadratic value. (`block_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L262)).

**Split the full quadratic form by blocks.** Proved result. Under the stated hypotheses, the full pairing-matrix quadratic form is the sum of its cell-label block contributions. (`quad_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L270)).

**Pairing matrix is positive definite.** Proved result. Under the stated hypotheses, the test-pairing matrix is positive definite for valid row data. (`rowPairingPosDef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstancePairingPosDef.lean#L298)).

### Breakdown.CertCell.InstanceRate

Bounds the compactified chart coordinate and its distance from the endpoints. These geometric estimates produce the stated radial decay rate of the constructed scalar profile. Appendix B: cell-system construction and finite certificate analysis.

**Absolute height ratio is bounded.** Proved result. Under the stated hypotheses, the absolute normalized height is at most one. (`height_abs_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRate.lean#L15)).

**Radial chart lies in the unit interval.** Proved result. Under the stated hypotheses, the compactified radial coordinate lies between zero and one. (`chart_mem_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRate.lean#L23)).

**Radius times chart deficit is bounded.** Proved result. Under the stated hypotheses, radius times one minus the radial chart is bounded by the chart length scale. (`norm_mul_one_sub_chart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRate.lean#L29)).

**Scaled difference of chart values.** Proved result. Under the stated hypotheses, the radius-scaled radial-chart difference is bounded by spatial distance. (`norm_mul_chart_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRate.lean#L40)).

**Difference of decay powers.** Proved result. Under the stated hypotheses, the difference of the two decay powers is bounded by the exponent times the coordinate difference. (`one_sub_pow_sub_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRate.lean#L59)).

**Decay powers are bounded by one.** Proved result. Under the stated hypotheses, the stated decay power has absolute value at most one. (`one_sub_pow_abs_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRate.lean#L74)).

**Scalar decay and gradient rate.** Proved result. Under the stated hypotheses, the scalar, its prescribed radius-weighted decay and radius times its gradient weight are uniformly bounded. (`scalarRateOfDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRate.lean#L81)).

### Breakdown.CertCell.InstanceRegular

Proves measurability and integral regularity of the concrete scalar, vector and gradient fields. Support and pointwise bounds supply the hypotheses of the analytic instance interfaces. Appendix B: cell-system construction and finite certificate analysis.

**Angle is measurable.** Proved result. Under the stated hypotheses, the spatial angle is measurable. (`pointAngle_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L15)).

**Meridian coordinates are continuous.** Proved result. Under the stated hypotheses, the meridian-coordinate map is continuous. (`pointPlane_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L18)).

**Cell solid is measurable.** Proved result. The three-dimensional solid obtained by revolving a closed meridian cell rectangle is a measurable subset of R³. (`solid_measurableSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L21)).

**Single-coordinate vector formula.** Proved result. Under the stated hypotheses, a single-coordinate vector is its value times the unit vector. (`single_eq_smul_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L27)).

**Frame vector is continuous.** Proved result. Under the stated hypotheses, the frame vector is continuous in angle. (`frameUnit_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L31)).

**Frame vector has norm one.** Proved result. At each angle θ, each of the radial, azimuthal and axial basis vectors has Euclidean norm one. (`frameUnit_norm_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L34)).

**Frame matrix term is continuous.** Proved result. Under the stated hypotheses, the rank-one frame reconstruction term is continuous in angle. (`frameTerm_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L38)).

**Cell polynomial is continuous.** Proved result. Under the stated hypotheses, the evaluated cell polynomial is continuous. (`cellPoly_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L43)).

**Frame sign absolute value.** Proved result. Under the stated hypotheses, the frame sign has absolute value one. (`frameSign_abs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L46)).

**Label phase is time-periodic.** Proved result. Under the stated hypotheses, the label phase is unchanged by adding one to time. (`labelPhase_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L49)).

**Label phase has norm one.** Proved result. For every temporal and angular label and all real σ and θ, the factor exp(i(2πkσ+nθ)) has complex modulus one. (`labelPhase_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L58)).

**Real phase coefficient bound.** Proved result. Under the stated hypotheses, the absolute real part of the phase-weighted coefficient is bounded by the coefficient norm. (`coef_abs_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L61)).

**Label values are measurable.** Proved result. Under the stated hypotheses, the cell label value composed with meridian coordinates is measurable. (`labelValueAt_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L66)).

**Phase coefficient is measurable.** Proved result. Under the stated hypotheses, the phase-weighted real coefficient is measurable in spacetime. (`coef_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L80)).

**Cell label values are bounded.** Proved result. Under the stated hypotheses, the cell label value has a uniform bound on the cell solid. (`labelValueAt_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L91)).

**Cell solid radius bound.** Proved result. Under the stated hypotheses, the norm of a point in the solid is bounded by the outer radial and height coordinates. (`solid_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L117)).

**Far points miss the solids.** Proved result. Under the stated hypotheses, a point beyond the stated radius belongs to none of the cell solids. (`outside_solids`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L132)).

**Supported period integral is finite.** Proved result. Under the stated hypotheses, the bounded supported function has finite period lower integral. (`period_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L137)).

**Matrix square from a norm bound.** Proved result. Under the stated hypotheses, the matrix square is at most three times the square of the stated norm bound. (`matSq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L163)).

**Frame-map norm bound.** Proved result. Under the stated hypotheses, the reconstructed frame-map norm is bounded by the sum of absolute matrix entries. (`frameMap_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L173)).

**Cell vector field is measurable.** Proved result. Under the stated hypotheses, the cell vector field is measurable in time and space. (`vec_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L181)).

**Cell matrix field is measurable.** Proved result. Under the stated hypotheses, the cell matrix field is measurable in time and space. (`mat_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L190)).

**Cell vector field is periodic.** Proved result. Under the stated hypotheses, the cell vector field is time-periodic. (`vec_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L200)).

**Cell matrix field is periodic.** Proved result. Under the stated hypotheses, the cell matrix field is time-periodic. (`mat_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L205)).

**Cell vector field is bounded.** Proved result. Under the stated hypotheses, the cell vector field has a uniform norm bound. (`vec_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L210)).

**Cell matrix field is bounded.** Proved result. Under the stated hypotheses, the cell matrix field has a uniform norm bound. (`mat_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L228)).

**Cell vector field vanishes outside.** Proved result. Under the stated hypotheses, the cell vector field vanishes beyond the stated support radius. (`vec_vanish`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L247)).

**Cell matrix field vanishes outside.** Proved result. Under the stated hypotheses, the cell matrix field vanishes beyond the stated support radius. (`mat_vanish`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L252)).

**Cell vector fields are regular.** Proved result. Under the stated hypotheses, cell vector fields are measurable, time-periodic, bounded with bounded support and have finite period square integral. (`cellVecFieldRegular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L260)).

**Cell matrix fields are regular.** Proved result. Under the stated hypotheses, cell matrix fields are measurable, time-periodic, bounded with bounded support and have finite period matrix-square integral. (`cellMatFieldRegular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceRegular.lean#L271)).

### Breakdown.CertCell.InstanceSlope

Bounds polynomial derivatives and propagates their slope estimates across chart intervals. It derives a Lipschitz bound for the glued scalar profile and its associated weight construction. Appendix B: cell-system construction and finite certificate analysis.

**Glue a common slope bound.** Proved result. Under the stated hypotheses, ordered pieces with matching endpoint values inherit their common slope bound. (`glue_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L15)).

**Evaluate first-variable substitution.** Proved result. Under the stated hypotheses, fixing the first polynomial variable fixes that coordinate in evaluation. (`eval_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L70)).

**Evaluate second-variable substitution.** Proved result. Under the stated hypotheses, fixing the second polynomial variable fixes that coordinate in evaluation. (`eval_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L79)).

**Polynomial bound on the unit box.** Proved result. Under the stated hypotheses, the polynomial has uniform value and slope bounds on the complex unit box. (`poly_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L88)).

**Real chart coordinates lie in the box.** Proved result. Under the stated hypotheses, the embedded real chart coordinates have complex norm at most one. (`vec_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L135)).

**Distance of real chart coordinates.** Proved result. Under the stated hypotheses, the complex coordinate-distance sum equals the sum of the real absolute differences. (`vec_dist`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L142)).

**Real polynomial slope bound.** Proved result. Under the stated hypotheses, the real polynomial evaluation has the stated uniform coordinate slope bound on the unit square. (`poly_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L149)).

**Separate the first-variable factor.** Proved result. Under the stated hypotheses, the polynomial is its value at first coordinate zero plus a multiple of the first variable. (`split_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L160)).

**Flat polynomial has a radial factor.** Proved result. Under the stated hypotheses, the height variation of the flat polynomial gains a factor of the first coordinate. (`flat_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L192)).

**Interior breaks remain ordered.** Proved result. Under the stated hypotheses, the interior break list is strictly ordered. (`interior_pw`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L220)).

**Interior breaks are positive.** Proved result. Under the stated hypotheses, every interior breakpoint is positive. (`interior_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L223)).

**A valid grid has two endpoints.** Proved result. Under the stated hypotheses, the valid breakpoint list has at least two entries. (`two_le_length`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L234)).

**Number of interior breaks.** Proved result. Under the stated hypotheses, the number of interior breaks is one less than the cell count. (`interior_len`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L241)).

**Index an interior breakpoint.** Proved result. Under the stated hypotheses, the kth interior break is the original break at index k plus one. (`interior_get`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L244)).

**Cell index is in range.** Proved result. Under the stated hypotheses, the cell index is below the cell count. (`index_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L253)).

**Cell count is positive.** Proved result. Under the stated hypotheses, a valid mesh has at least one cell. (`count_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L262)).

**Zero selects the first cell.** Proved result. Under the stated hypotheses, the cell index at zero is zero. (`index_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L268)).

**Positive finite list has a lower bound.** Proved result. Under the stated hypotheses, a finite list of positive reals has a common positive lower bound. (`list_pos_min`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L277)).

**Noninitial cells stay away from zero.** Proved result. Under the stated hypotheses, there is a positive threshold below every coordinate selecting a nonzero cell index. (`index_gap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L286)).

**Choose one finite bound.** Proved result. Under the stated hypotheses, finitely many monotone bound conditions admit one common nonnegative bound. (`finite_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L295)).

**Radial spline slope estimate.** Proved result. Under the stated hypotheses, the half-spline has the stated slope bound in the radial-chart coordinate. (`t_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L307)).

**Height spline slope estimate.** Proved result. Under the stated hypotheses, the half-spline has the stated slope bound in the height-chart coordinate. (`x_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L332)).

**Unit-interval values have bounded norm.** Proved result. Under the stated hypotheses, a value in the unit interval has absolute value at most one. (`abs_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L356)).

**Uniform radial spline slope.** Proved result. Under the stated hypotheses, the joined half-spline has a uniform radial-chart slope bound. (`spline_t_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L359)).

**Height slope gains a radial factor.** Proved result. Under the stated hypotheses, the joined half-spline's height variation is bounded by radius-chart coordinate times height distance. (`spline_x_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L387)).

**Joined real half-spline value.** Definition. `Breakdown.CertCell.Instance.Internal.Slope.halfVal` selects the real upper or reflected lower spline value. (`halfVal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L440)).

**The two halves agree at the plane.** Proved result. Under the stated hypotheses, the upper and lower half-spline values agree at height zero. (`plane_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L443)).

**Joined radial-coordinate slope.** Proved result. Under the stated hypotheses, the joined scalar has a uniform slope bound in the radial-chart coordinate. (`half_t_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L455)).

**Joined height-coordinate slope.** Proved result. Under the stated hypotheses, the joined scalar's height slope has the stated radial-coordinate factor. (`half_x_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L469)).

**Joined scalar is bounded.** Proved result. Under the stated hypotheses, the joined scalar has a uniform absolute bound on the stated chart region. (`half_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L512)).

**Height ratio preserves the sign.** Proved result. Under the stated hypotheses, the normalized height is nonnegative exactly when the height coordinate is nonnegative. (`sign_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L534)).

**A coordinate is bounded by the norm.** Proved result. Under the stated hypotheses, the absolute value of a coordinate is at most the vector norm. (`coord_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L548)).

**Height ratio has absolute bound one.** Proved result. Under the stated hypotheses, the absolute normalized height is at most one. (`height_abs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L551)).

**Height ratio difference bound.** Proved result. Under the stated hypotheses, the stated radius times the height-ratio difference is at most twice the spatial distance. (`height_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L559)).

**Chart coordinate lies in the unit range.** Proved result. Under the stated hypotheses, the compactified radial coordinate belongs to the unit interval. (`chart_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L598)).

**Chart coordinate grows at most linearly.** Proved result. Under the stated hypotheses, the radial chart is bounded by radius divided by the chart length scale. (`chart_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L604)).

**Radial chart is Lipschitz.** Proved result. Under the stated hypotheses, the radial-chart difference is bounded by distance divided by the chart length scale. (`chart_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L608)).

**Decay power slope estimate.** Proved result. Under the stated hypotheses, the stated decay-power difference is bounded by the exponent times the input difference. (`pow_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L626)).

**Separate the scalar decay factor.** Proved result. Under the stated hypotheses, the scalar evaluation equals its decay factor times the joined chart value. (`eval_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L641)).

**Joined scalar is Lipschitz.** Proved result. Under the stated hypotheses, the joined flat-at-origin scalar has a global Lipschitz bound. (`scalarSlopeBoundOfJoins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSlope.lean#L650)).

### Breakdown.CertCell.InstanceSmooth

Uses spline joins through order two and the constant core to establish smoothness of the concrete scalar field. The result explicitly requires the chart and decay conditions stated in the interface. Appendix B: cell-system construction and finite certificate analysis.

**A valid break list has endpoints.** Proved result. Under the stated hypotheses, the break list has at least two entries. (`two_le_length`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L17)).

**Cell index stays below count.** Proved result. Under the stated hypotheses, the chosen cell index is below the cell count. (`index_lt_count`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L26)).

**Next ordered breakpoint is bounded.** Proved result. Under the stated hypotheses, the selected next break is at most the indicated later breakpoint. (`next_break_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L34)).

**Next cell break before the core limit.** Proved result. Under the stated hypotheses, the next cell breakpoint is at most the stated comparison breakpoint. (`next_break_le_core`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L63)).

**Radial chart is nonnegative.** Proved result. Under the stated hypotheses, the radial chart value is nonnegative. (`chartT_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L78)).

**Radial chart is below one.** Proved result. Under the stated hypotheses, the radial chart value is less than one. (`chartT_lt_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L81)).

**Positive radial chart off the origin.** Proved result. Under the stated hypotheses, the radial chart value is positive at the stated nonzero point. (`chartT_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L87)).

**Radial chart is continuous.** Proved result. Under the stated hypotheses, the radial chart function is continuous. (`chartT_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L90)).

**Radial chart vanishes at the origin.** Proved result. Under the stated hypotheses, the radial chart value at the origin is zero. (`chartT_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L94)).

**Chart pair is twice smooth locally.** Proved result. Under the stated hypotheses, the radial and height chart pair is twice continuously differentiable at the stated point. (`pair_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L96)).

**Constant core has one common value.** Proved result. Under the stated hypotheses, both spline halves take one common value throughout the stated core region. (`core_values`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L106)).

**Scalar smoothness from joins.** Proved result. Under the stated hypotheses, the joined scalar with constant core and zero decay exponent is twice continuously differentiable. (`scalarSmoothOfJoins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceSmooth.lean#L125)).

### Breakdown.CertCell.InstanceStatements

Defines the finite pairing matrices and the analytic clauses for the concrete field instance. These interfaces organize smoothness, decay, support, moments, normalization and row or actuator consequences. Appendix B: cell-system construction and finite certificate analysis.

**Rows in the same block.** Proposition definition. The interface requires that the rows share a cell and have equal or opposite labels. (`SameBlock`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L23)).

**Finite test-pairing matrix.** Definition. This defines the real Gram entries from cell test integrals for matching label blocks. (`testPairingMatrix`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L27)).

**Upper row moment.** Definition. This defines the upper-half radius-weighted pairing of the label velocity with the row test. (`upperMoment`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L40)).

**Lower row moment.** Definition. This defines the reflected lower-half radius-weighted row moment with its frame signs. (`lowerMoment`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L45)).

**Cell-moment vector.** Definition. This defines the complex radius-weighted test moments of one velocity label in a cell. (`cellMoment`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L50)).

**Generator Gram-matrix interface.** Proposition definition. The interface requires that the analytic generator Gram matrix equals the finite test-pairing matrix for valid rows. (`GeneratorPairingMatrixFormula`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L59)).

**Orthonormal row-field interface.** Proposition definition. The interface requires that normalizing a positive generator Gram matrix gives pairwise orthonormal row fields. (`RowFieldsOrthonormal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L63)).

**Generator moment interface.** Proposition definition. The interface requires that the pairing with a generator equals the sum of its upper and lower moments. (`GeneratorPairingMoments`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L69)).

**Row norm interface.** Proposition definition. The interface requires that the weighted row norm equals the corresponding inverse Gram-matrix quadratic expression. (`RowNormIdentity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L76)).

**Positive row-pairing interface.** Proposition definition. The interface requires that valid row data give a positive definite test-pairing matrix. (`RowPairingPosDef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L86)).

**Rows class-form interface.** Proposition definition. The interface requires that the row norm of a reflected field is four pi times the sum of weighted inverse cell-moment forms. (`RowsClassForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L90)).

**Row weight upper bound.** Proved result. Under the stated hypotheses, the specified row weight is at most the given bound. (`rowWeight_le_of_values`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L99)).

**Row weights are nonnegative.** Proved result. Under the stated hypotheses, each specified row weight is nonnegative. (`rowWeight_nonneg_of_values`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L104)).

**Admissible weight conditions.** Proposition structure. The interface requires that the finite classes, positive constants, regular weights, shares and decay bounds satisfy the listed admissibility conditions. (`AdmissibleWeightClauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L124)).

**Weight reflection conditions.** Proposition structure. The interface requires that the strain, vorticity and piece data transform by the specified reflection and piece permutations. (`WeightFlipClauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L162)).

**Remaining reflection conditions.** Proposition structure. The interface requires that the model weights, harmonics, amplitudes, suprema and speeds meet the remaining reflection and rotation conditions. (`OtherFlipClauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L185)).

**Assemble reflection compatibility.** Proved result. Under the stated hypotheses, the weight and remaining reflection clauses give full flip compatibility. (`isFlipCompatible_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L202)).

**Remaining admissibility conditions.** Proposition structure. The interface requires that the period, reference profile, amplitude bounds, one-sided frequencies and comparison bounds meet the listed conditions. (`OtherAdmissibleClauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L217)).

**Assemble weak admissibility.** Proved result. Under the stated hypotheses, the weight and remaining admissibility clauses give the full weak admissibility predicate. (`isAdmissibleWeak_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L253)).

**Scalar smoothness requirement.** Proposition definition. The interface requires that a valid chart with twice-joined scalar, constant core and zero decay exponent yields a twice continuously differentiable scalar. (`ScalarSmoothOfJoins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L311)).

**Scalar derivative decay requirement.** Proposition definition. The interface requires that valid twice-joined scalar data with constant core and zero decay exponent have bounded derivatives through order two after multiplication by one plus spatial norm raised to the derivative order. (`ScalarDerivativeDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L315)).

**Scalar Lipschitz requirement.** Proposition definition. The interface requires that valid order-zero joins and flatness at the origin imply a global Lipschitz bound. (`ScalarSlopeBoundOfJoins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L319)).

**Scalar decay-rate requirement.** Proposition definition. The interface requires that valid joined scalar data flat at the origin give uniform bounds for the scalar, its prescribed radius-weighted decay and radius times its gradient weight. (`ScalarRateOfDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L323)).

**Basic scalar requirements.** Proposition definition. The interface requires that scalar evaluation is measurable and axisymmetric, and nonnegative stored values give nonnegative evaluation. (`ScalarBasicFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L328)).

**Basic step requirements.** Proposition definition. The interface requires that step evaluation is measurable and axisymmetric, and positive step data give strictly positive evaluation. (`StepBasicFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L332)).

**Mirror-evaluation requirement.** Proposition definition. The interface requires that mirrored scalar and step data reproduce the original values after reflection, with the stated plane exception for steps. (`MirrorEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L336)).

**Weight data imply admissibility.** Proved result. Under the stated hypotheses, the weight values imply the admissible-weight clauses. (`weightClauses_of_values`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L341)).

**Weight data imply reflection.** Proved result. Under the stated hypotheses, the weight values imply the weight reflection clauses. (`weightsFlip_of_values`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L422)).

**Weight instance clauses.** Proved result. Under the stated hypotheses, the weight instance gives admissibility, reflection and the coercivity identity at every admitted parameter. (`weightInstance_clauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L483)).

**Constant weight clauses.** Proved result. Under the stated hypotheses, the positive constant weight is measurable, axisymmetric and equals its positive lower bound. (`constantWeight_clauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L498)).

**Cell vector regularity requirement.** Proposition definition. The interface requires that cell vector fields are measurable, periodic, bounded with bounded support and have finite period square integral. (`CellVecFieldRegular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L505)).

**Cell matrix regularity requirement.** Proposition definition. The interface requires that cell matrix fields are measurable, periodic, bounded with bounded support and have finite period matrix-square integral. (`CellMatFieldRegular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L512)).

**Analytic actuator conditions.** Proposition structure. The interface requires that the actuator and its gradient have the listed regularity, support, weak derivative and permitted mode interactions. (`ActuatorFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L519)).

**Shape data imply actuator symmetry.** Proved result. Under the stated hypotheses, the actuator shape conditions imply equivariance under every specified symmetry almost everywhere. (`actuatorInvariant_of_shape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L535)).

**Instance data imply actuator facts.** Proved result. Under the stated hypotheses, the actuator instance implies the full analytic actuator conditions. (`actuatorFacts_of_instance`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L684)).

**Pin instance clauses.** Proved result. Under the stated hypotheses, the pin instance supplies measurable fields with finite period matrix-square integral. (`pinInstance_clauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L734)).

**Row instance clauses.** Proved result. Under the stated hypotheses, the row instance supplies measurable periodic finite-energy orthonormal fields and bounded nonnegative weights. (`rowInstance_clauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L748)).

**Analytic instance consequences.** Proposition structure. The interface requires that the row fields, weights, actuators and pins satisfy the required orthonormality, boundedness, regularity, symmetry and class-form conditions. (`InstanceConsequences`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L828)).

**Conditions for the analytic instance.** Proposition structure. The interface requires that the Gram matrix, moments, row norms, scalar profiles and field constructions satisfy their stated positivity, evaluation and regularity conditions. (`InstanceParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L851)).

**Entry gives analytic consequences.** Proved result. Under the stated hypotheses, a valid instance entry with actuator shape facts gives the required row, weight, actuator and pin conditions. (`instanceConsequences_of_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/InstanceStatements.lean#L868)).

### Breakdown.CertCell.LabelArithmetic

Derives the required frequency and parity arithmetic for valid labels. This supplies the arithmetic interface used by the harmonic class and row constructions. Appendix B: cell-system construction and finite certificate analysis.

**Lattice labels and parity.** Proved result. Under the stated hypotheses, positive azimuthal order makes label frequencies injective, compatible with reflection and negation, and characterized by divisibility and even parity. (`labelArithmetic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelArithmetic.lean#L9)).

### Breakdown.CertCell.LabelModeFacts

Extracts the harmonic corresponding to a valid label and proves weighted mode integrability. It packages the gradient, second derivative and pressure-mode conditions used by the local row analysis. Appendix B: cell-system construction and finite certificate analysis.

**Write a label in harmonic coordinates.** Proved result. Under the stated hypotheses, every label has time and azimuthal indices with the required even-sum parity. (`exists_harmonic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L15)).

**Radius is positive almost everywhere.** Proved result. Under the stated hypotheses, radius is positive almost everywhere in a valid cell rectangle. (`ae_rect_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L21)).

**Square bound for a complex combination.** Proved result. Under the stated hypotheses, the squared norm of x plus i times y is at most twice the sum of their squared norms. (`sq_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L34)).

**Weighted square is integrable.** Proved result. Under the stated hypotheses, the indicated weighted squared profile is integrable on the cell rectangle. (`weighted_sq_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L39)).

**Combine weak integral identities.** Proved result. Under the stated hypotheses, the stated combined integrand satisfies the negative-pairing integral identity. (`combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L53)).

**Finite component sum is integrable.** Proved result. Under the stated hypotheses, the finite coefficient-weighted sum of profile components is integrable. (`combo_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L62)).

**Radial weak-pair terms are integrable.** Proved result. Under the stated hypotheses, both sides of the radius-weighted radial test pairing are integrable. (`radial_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L66)).

**Height weak-pair terms are integrable.** Proved result. Under the stated hypotheses, both sides of the weighted height test pairing are integrable. (`height_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L92)).

**Line weight is nonnegative.** Proved result. Under the stated hypotheses, the line weight is nonnegative throughout the cell rectangle. (`lineWeight_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L124)).

**Cell radius is nonnegative.** Proved result. Under the stated hypotheses, radius is nonnegative throughout the cell rectangle. (`fst_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L132)).

**Label mode facts hold.** Proved result. Under the stated hypotheses, the label-mode measurability, weighted integrability and weak derivative facts hold. (`labelModeFacts_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelModeFacts.lean#L138)).

### Breakdown.CertCell.LabelResolvedEnergy

Controls finite combinations of gradient and slope profiles and proves their integrability. The resulting bridge evaluates resolved energy for valid labels, with the stated axis-mode restriction. Appendix B: cell-system construction and finite certificate analysis.

**Linear combination of gradient modes.** Definition. This defines a fixed complex linear combination of the gradient-mode entries. (`comboGradAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelResolvedEnergy.lean#L18)).

**Linear combination of slope modes.** Definition. This defines the same coefficient combination of the second-derivative mode entries. (`comboSlopeAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelResolvedEnergy.lean#L22)).

**Resolved component energy bound.** Proved result. Under the stated hypotheses, the radial, height and angular energies plus their tails are bounded by the weighted second-derivative square integral. (`combo_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelResolvedEnergy.lean#L26)).

**Resolved second-mode energy integrable.** Proved result. Under the stated hypotheses, the radius-weighted sum of the three second-mode squares is integrable. (`combo_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelResolvedEnergy.lean#L42)).

**Resolved label energy bound.** Proved result. Under the stated hypotheses, the resolved label strain and vorticity energies satisfy their second-derivative bounds. (`labelResolvedEnergy_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelResolvedEnergy.lean#L57)).

### Breakdown.CertCell.LabelRowProfile

Proves measurability, weak differentiation and local integrability of the velocity, gradient and second-derivative label modes. These facts assemble the velocity and gradient parts of the finite row profile. Appendix B: cell-system construction and finite certificate analysis.

**Velocity label is measurable a.e..** Proved result. Under the stated hypotheses, the velocity-label component is almost everywhere strongly measurable on the half-plane. (`vel_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L25)).

**Gradient label is measurable a.e..** Proved result. Under the stated hypotheses, the gradient-label component is almost everywhere strongly measurable on the half-plane. (`grad_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L36)).

**Second label is measurable a.e..** Proved result. Under the stated hypotheses, the second-derivative label component is almost everywhere strongly measurable on the half-plane. (`secondDeriv_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L48)).

**Cell restriction lies below half-plane.** Proved result. Under the stated hypotheses, the cell's restricted volume is bounded by the half-plane's restricted volume. (`rect_le_half`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L62)).

**Coordinate extraction is measurable.** Proved result. Under the stated hypotheses, the indicated coordinate function is almost everywhere strongly measurable. (`coord_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L72)).

**Cell rectangle is measurable.** Proved result. The closed rectangle of radial and height coordinates associated with any cell box is measurable in R². (`rect_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L76)).

**Weighted square by domination.** Proved result. Under the stated hypotheses, the radius-weighted squared profile is integrable under the given domination. (`wsq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L78)).

**Norm of a harmonic combination.** Proved result. Under the stated hypotheses, the norm of a complex cosine-sine combination is bounded by the sum of the two norms. (`norm_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L100)).

**Radial square from line-weight square.** Proved result. Under the stated hypotheses, the line-weight square estimate gives integrability of the radius-weighted square. (`wsq_of_lineWeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L104)).

**Angular-average square is integrable.** Proved result. Under the stated hypotheses, the radius-weighted square of the indicated angular average is integrable on the cell. (`wsq_circle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L122)).

**Velocity mode has a weighted square.** Proved result. Under the stated hypotheses, the velocity mode's radius-weighted square is integrable on the cell. (`vec_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L190)).

**Velocity mode is measurable a.e..** Proved result. Under the stated hypotheses, the velocity mode is almost everywhere strongly measurable on the cell. (`vec_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L199)).

**Local L2 from global L6.** Proved result. Under the stated hypotheses, an L6 field has an integrable squared norm on every stated closed ball. (`sq_ball_of_six`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L206)).

**Reconstruct the label.** Proved result. Under the stated hypotheses, the harmonic-mode constructor recovers the label from its time and first coordinate. (`harmonicMode_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L214)).

**Label parity is even.** Proved result. Under the stated hypotheses, the sum of the label's first coordinate and its time index is even. (`even_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L219)).

**Row profiles are measurable a.e..** Proved result. Under the stated hypotheses, all velocity, gradient, second-derivative and pressure-gradient row-profile components are measurable almost everywhere. (`profile_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L221)).

**Row-profile square is integrable.** Proved result. Under the stated hypotheses, the stated radius-weighted sum of velocity, gradient, Laplacian and pressure-gradient squares is integrable. (`profile_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L234)).

**Row profile validity from parts.** Proved result. Under the stated hypotheses, the component integrability and weak identities make the label row profile valid. (`profile_valid_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L296)).

**Label row profile is valid.** Proved result. Under the stated hypotheses, the constructed label row profile satisfies the row-profile conditions. (`labelRowProfile_valid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L320)).

**Labels give valid row profiles.** Proved result. Under the stated hypotheses, each permitted label admits a valid row profile whose velocity, gradient, Laplacian and pressure gradient agree with the analytic label arrays at positive radius. (`labelRowProfile_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfile.lean#L329)).

### Breakdown.CertCell.LabelRowProfilePressure

Applies the weak pressure-gradient identity to cylindrical test profiles. Weighted radial and height integration by parts identifies the pressure contribution to the finite label row. Appendix B: cell-system construction and finite certificate analysis.

**Chosen potential satisfies weak gradient.** Proved result. Under the stated hypotheses, the chosen potential satisfies the stated integration-by-parts identity against scalar tests. (`potential_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L19)).

**Gradient coordinates integrate locally.** Proved result. Under the stated hypotheses, the indicated gradient-field coordinate is locally integrable. (`inner_locInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L27)).

**Pressure modes are locally integrable.** Proved result. Under the stated hypotheses, the potential mode and the radius-weighted gradient modes are integrable on the stated rectangle. (`mode_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L38)).

**Pressure radial weak derivative.** Proved result. Under the stated hypotheses, the potential's angular mode and radial gradient mode form a radial weak pair. (`grad_radial_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L44)).

**Pressure height weak derivative.** Proved result. Under the stated hypotheses, the potential's angular mode and axial gradient mode form a radius-weighted height weak pair. (`grad_height_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L70)).

**Pressure angular derivative.** Proved result. Under the stated hypotheses, the angular gradient mode times radius equals i times the azimuthal frequency times the potential mode almost everywhere off the axis. (`grad_angular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L110)).

**Supported pressure test is integrable.** Proved result. Under the stated hypotheses, the compactly supported test times the mode is integrable. (`supported_integrable2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L168)).

**Compact support lies away from the axis.** Proved result. Under the stated hypotheses, the stated compact set lies in a bounded box with radius separated from zero. (`compact_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L181)).

**Add radial weak pairs.** Proved result. Under the stated hypotheses, a fixed complex linear combination of radial weak pairs remains a radial weak pair. (`radial_pair_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L195)).

**Add height weak pairs.** Proved result. Under the stated hypotheses, a fixed complex linear combination of height weak pairs remains a height weak pair. (`height_pair_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L236)).

**Radial polynomial factor.** Definition. This defines the radial polynomial formed by conjugating the selected column of coefficients. (`radialFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L285)).

**Height polynomial factor.** Definition. This defines the height polynomial formed by conjugating the selected row of coefficients. (`heightFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L288)).

**Conjugate evaluation by radial factors.** Proved result. Under the stated hypotheses, conjugate cell-polynomial evaluation expands into radial factors times height powers. (`conj_eval_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L291)).

**Conjugate evaluation by height factors.** Proved result. Under the stated hypotheses, conjugate cell-polynomial evaluation expands into height factors times radial powers. (`conj_eval_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L296)).

**Reference radius is smooth.** Proved result. Under the stated hypotheses, the embedded reference radial coordinate is smooth. (`refR_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L302)).

**Reference height is smooth.** Proved result. Under the stated hypotheses, the embedded reference height coordinate is smooth. (`refZ_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L307)).

**Radial factors are smooth.** Proved result. Under the stated hypotheses, the radial polynomial factors are smooth. (`radialFactor_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L312)).

**Height factors are smooth.** Proved result. Under the stated hypotheses, the height polynomial factors are smooth. (`heightFactor_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L317)).

**Polynomial is smooth along radius.** Proved result. Under the stated hypotheses, cell-polynomial evaluation is smooth in the radial variable. (`eval_radial_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L322)).

**Polynomial is smooth along height.** Proved result. Under the stated hypotheses, cell-polynomial evaluation is smooth in the height variable. (`eval_height_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L328)).

**Cell-polynomial evaluation is continuous.** Proved result. Under the stated hypotheses, the cell polynomial is continuous jointly in radius and height. (`eval_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L334)).

**Conjugate radial derivative expansion.** Proved result. Under the stated hypotheses, the conjugate radial derivative expands into derivatives of the radial factors. (`conj_radialDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L340)).

**Conjugate height derivative expansion.** Proved result. Under the stated hypotheses, the conjugate height derivative expands into derivatives of the height factors. (`conj_heightDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L355)).

**Derivative of radius times polynomial.** Proved result. Under the stated hypotheses, the radial derivative of radius times the polynomial is the polynomial plus radius times its derivative. (`radialDeriv_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L370)).

**Lower radial boundary term integrable.** Proved result. Under the stated hypotheses, the stated lower radial boundary integrand is integrable. (`radial_low_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L393)).

**Polynomial radial integration by parts.** Proved result. Under the stated hypotheses, the polynomial radial pairing splits into its two radial boundary contributions with integrable terms. (`radial_poly_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L416)).

**Polynomial height integration by parts.** Proved result. Under the stated hypotheses, the radius-weighted polynomial height pairing splits into its two height boundary contributions with integrable terms. (`height_poly_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L516)).

**Radial boundary as a strip integral.** Proved result. Under the stated hypotheses, the radial trace boundary integral equals the oriented strip integral. (`radial_boundary_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L614)).

**Height boundary as a strip integral.** Proved result. Under the stated hypotheses, the height trace boundary integral equals the oriented strip integral. (`height_boundary_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L638)).

**Pressure pairing equals its boundary.** Proved result. Under the stated hypotheses, the pressure-gradient row pairing equals the pressure boundary functional. (`labelRowProfile_pressure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfilePressure.lean#L667)).

### Breakdown.CertCell.LabelRowProfileSsp

Combines the angular-turn identity with the local second-partial integration-by-parts formulas. It establishes the sum-of-second-partials contribution to the label row profile. Appendix B: cell-system construction and finite certificate analysis.

**Turn operator preserves harmonic sums.** Proved result. Under the stated hypotheses, the turn operator distributes over a vector plus i times another vector. (`turnVector_combo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSsp.lean#L18)).

**Combined weak terms integrate to zero.** Proved result. Under the stated hypotheses, the combined weak integrand is integrable and has zero cell integral. (`combo_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSsp.lean#L22)).

**Laplacian row integration by parts.** Proved result. Under the stated hypotheses, the Laplacian row pairing equals the gradient boundary term minus the gradient-test pairing. (`labelRowProfile_sumSecondPartials`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSsp.lean#L34)).

### Breakdown.CertCell.LabelRowProfileSspLocal

Proves the local mode integrability and component identities required by the second-partial row calculation. The estimates handle the weighted axial component and localized test profiles. Appendix B: cell-system construction and finite certificate analysis.

**Gradient mode is cell-integrable.** Proved result. Under the stated hypotheses, the gradient-mode component is integrable on the cell rectangle. (`gradMode_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L22)).

**Select a second-mode entry.** Proved result. Under the stated hypotheses, the one-entry coefficient array selects the corresponding second-derivative mode. (`combo_oneHot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L29)).

**Weighted second mode is integrable.** Proved result. Under the stated hypotheses, the second-derivative mode multiplied by radius is integrable on the cell. (`weighted_modeThird_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L34)).

**Second mode is measurable a.e..** Proved result. Under the stated hypotheses, the second-derivative mode is almost everywhere strongly measurable on the cell. (`third_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L58)).

**Line-weighted second mode integrable.** Proved result. Under the stated hypotheses, the second-derivative mode multiplied by the line weight is integrable on the cell. (`lineWeight_third_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L69)).

**Local radial weak gradient pair.** Proved result. Under the stated hypotheses, the gradient mode and its radial second mode form the stated weak pair. (`radialWeak_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L90)).

**Radial second-partial identity.** Proved result. Under the stated hypotheses, the radial derivative test and radial second-mode terms have integrable sum with zero cell integral. (`radial_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L140)).

**Select a gradient-mode entry.** Proved result. Under the stated hypotheses, the one-entry coefficient array selects the corresponding gradient mode. (`comboGrad_oneHot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L151)).

**Height derivative of a product test.** Proved result. Under the stated hypotheses, the height derivative differentiates only the height factor of the separable test. (`height_deriv_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L155)).

**Height second-partial identity.** Proved result. Under the stated hypotheses, the height derivative test and axial second-mode terms have integrable radius-weighted sum with zero cell integral. (`height_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L163)).

**Angular second column formula.** Proved result. Under the stated hypotheses, radius times the angular second-mode column equals the turn of the angular gradient column plus the radial column almost everywhere. (`angular_column`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspLocal.lean#L235)).

### Breakdown.CertCell.LabelRowProfileSspParts

Constructs radial and height monomial tests and computes their derivatives. The resulting integration-by-parts identities evaluate the componentwise second-partial row terms. Appendix B: cell-system construction and finite certificate analysis.

**Reference radial monomial.** Definition. This defines a power of the reference radial coordinate. (`monoR`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L17)).

**Reference height monomial.** Definition. This defines a power of the reference height coordinate. (`monoZ`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L19)).

**Radial monomial is differentiable.** Proved result. Under the stated hypotheses, the radial monomial is continuously differentiable. (`monoR_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L21)).

**Height monomial is differentiable.** Proved result. Under the stated hypotheses, the height monomial is continuously differentiable. (`monoZ_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L25)).

**Expand cell-polynomial evaluation.** Proved result. Under the stated hypotheses, the cell polynomial is the double sum of its coefficients times the two reference monomials. (`eval_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L29)).

**Conjugate the polynomial expansion.** Proved result. Under the stated hypotheses, the conjugate polynomial value uses conjugated coefficients and the same real monomials. (`conj_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L35)).

**Radial derivative of the polynomial.** Proved result. Under the stated hypotheses, the radial derivative differentiates the radial monomial in the coefficient expansion. (`eval_hasDerivAt_r`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L41)).

**Height derivative of the polynomial.** Proved result. Under the stated hypotheses, the height derivative differentiates the height monomial in the coefficient expansion. (`eval_hasDerivAt_z`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L52)).

**Cell radial derivative expansion.** Proved result. Under the stated hypotheses, the defined radial derivative equals the coefficient sum with differentiated radial monomials. (`radialDeriv_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L63)).

**Cell height derivative expansion.** Proved result. Under the stated hypotheses, the defined height derivative equals the coefficient sum with differentiated height monomials. (`heightDeriv_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L68)).

**Radial monomial with boundary removed.** Definition. `Breakdown.CertCell.CellCalculus.Internal.RowParts.radialCut` subtracts the affine endpoint interpolation from radius times the radial monomial. (`radialCut`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L74)).

**Height monomial with boundary removed.** Definition. `Breakdown.CertCell.CellCalculus.Internal.RowParts.heightCut` subtracts the affine endpoint interpolation from the height monomial. (`heightCut`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L78)).

**Derivative of the radial cutoff.** Proved result. Under the stated hypotheses, the radial cutoff derivative is the derivative of the weighted monomial minus the two endpoint slopes. (`radialCut_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L82)).

**Derivative of the height cutoff.** Proved result. Under the stated hypotheses, the height cutoff derivative is the monomial derivative minus the two endpoint slopes. (`heightCut_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L94)).

**Radial cutoff is differentiable.** Proved result. Under the stated hypotheses, the radial cutoff is continuously differentiable. (`radialCut_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L105)).

**Height cutoff is differentiable.** Proved result. Under the stated hypotheses, the height cutoff is continuously differentiable. (`heightCut_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L110)).

**Radial cutoff vanishes at the inner side.** Proved result. Under the stated hypotheses, the radial cutoff vanishes at the inner radial endpoint. (`radialCut_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L115)).

**Radial cutoff vanishes at the outer side.** Proved result. Under the stated hypotheses, the radial cutoff vanishes at the outer radial endpoint. (`radialCut_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L120)).

**Height cutoff vanishes at the bottom.** Proved result. Under the stated hypotheses, the height cutoff vanishes at the lower height endpoint. (`heightCut_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L125)).

**Height cutoff vanishes at the top.** Proved result. Under the stated hypotheses, the height cutoff vanishes at the upper height endpoint. (`heightCut_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L130)).

**Radial cutoff expansion.** Proved result. Under the stated hypotheses, the cutoff coefficient sum equals the bulk radial terms minus the two radial boundary terms. (`radial_algebra`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L135)).

**Height cutoff expansion.** Proved result. Under the stated hypotheses, the cutoff coefficient sum equals the bulk height terms minus the two height boundary terms. (`height_algebra`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L151)).

**Polynomial evaluation is continuous.** Proved result. Under the stated hypotheses, the evaluated cell polynomial is continuous. (`continuous_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L167)).

**Radial polynomial derivative continuous.** Proved result. Under the stated hypotheses, the evaluated radial derivative of the polynomial is continuous. (`continuous_radialDeriv_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L171)).

**Height polynomial derivative continuous.** Proved result. Under the stated hypotheses, the evaluated height derivative of the polynomial is continuous. (`continuous_heightDeriv_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L179)).

**Conjugate side value is continuous.** Proved result. Under the stated hypotheses, the conjugate polynomial value along the specified radial side is continuous. (`cont_conj_eval_side`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L187)).

**Conjugate level value is continuous.** Proved result. Under the stated hypotheses, the conjugate polynomial value along the specified height level is continuous. (`cont_conj_eval_level`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L191)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L195)).

**Cell rectangle is measurable.** Proved result. The closed rectangle of radial and height coordinates associated with any cell box is measurable in R². (`rect_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L197)).

**Multiply by a continuous cell factor.** Proved result. Under the stated hypotheses, multiplying the integrable profile by the continuous cell factor preserves integrability. (`int_mul_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L199)).

**Almost every radial slice integrates.** Proved result. Under the stated hypotheses, almost every fixed-height slice is integrable over the radial interval. (`slice_ae_z`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L203)).

**Almost every height slice integrates.** Proved result. Under the stated hypotheses, almost every fixed-radius slice is integrable over the height interval. (`slice_ae_r`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L208)).

**Integrate radius before height.** Proved result. Under the stated hypotheses, the rectangle integral equals the iterated integral with radius integrated first. (`iterated_z`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L213)).

**Integrate height before radius.** Proved result. Under the stated hypotheses, the rectangle integral equals the iterated integral with height integrated first. (`iterated_r`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L219)).

**Radial boundary pairing formula.** Proved result. Under the stated hypotheses, the oriented radial boundary pairing equals the stated integrable rectangle expression. (`radial_boundary`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L225)).

**Height boundary pairing formula.** Proved result. Under the stated hypotheses, the oriented height boundary pairing equals the stated integrable rectangle expression. (`height_boundary`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L261)).

**Turn operator is skew-adjoint.** Proved result. Under the stated hypotheses, the two Hermitian pairings involving the turn operator sum to zero. (`turn_adjoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L297)).

**Sum zero-integral terms.** Proved result. Under the stated hypotheses, a finite sum of integrable zero-integral functions is integrable with zero integral. (`integrable_zero_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L302)).

**Scale a zero-integral term.** Proved result. Under the stated hypotheses, scaling an integrable zero-integral function preserves those properties. (`integrable_zero_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L309)).

**Radial boundary hint is integrable.** Proved result. Under the stated hypotheses, the stated radially scaled affine boundary expression is integrable. (`radial_hint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L315)).

**Height boundary hint is integrable.** Proved result. Under the stated hypotheses, the stated radius-weighted affine height boundary expression is integrable. (`height_hint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L335)).

**Cell radius is nonzero a.e..** Proved result. Under the stated hypotheses, radius is nonzero almost everywhere on the cell rectangle. (`ae_first_ne_zero_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L346)).

**Row integration-by-parts identity.** Proved result. Under the stated hypotheses, the row Laplacian pairing equals its gradient boundary pairing minus the gradient-test integral. (`row_parts_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LabelRowProfileSspParts.lean#L355)).

### Breakdown.CertCell.LeafDensityLower

Proves nonnegativity of the square densities entering a leaf estimate. It then establishes the lower density bound from the stated coefficient inequalities. Appendix B: cell-system construction and finite certificate analysis.

**Strain square sum is nonnegative.** Proved result. Under the stated hypotheses, the finite strain-entry square sum is nonnegative. (`sumSq_nonneg_leaf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LeafDensityLower.lean#L15)).

**Curl square is nonnegative.** Proved result. For any complex 3 × 3 gradient matrix, the sum of squared moduli of its three curl components is nonnegative. (`curlSq_nonneg_leaf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LeafDensityLower.lean#L19)).

**Velocity square is nonnegative.** Proved result. For any three-component complex velocity vector v, the quantity ∑ⱼ |vⱼ|² is nonnegative. (`vecSq_nonneg_leaf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LeafDensityLower.lean#L23)).

**Leaf density has its lower bound.** Proved result. Under the stated hypotheses, the Hessian floors, local quadratic form and box penalty are bounded by the coefficient density evaluated on the gradient, curl and velocity norms. (`leafDensityLower_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LeafDensityLower.lean#L27)).

### Breakdown.CertCell.LeafNorms

Identifies the finite permutation sign with the alternating symbol used by curl. The resulting norm identities connect the leaf's finite vector and curl data with their analytic square densities. Appendix B: cell-system construction and finite certificate analysis.

**Permutation sign equals oriented sign.** Proved result. Under the stated hypotheses, the explicit permutation sign equals the alternating symbol. (`permSign_eq_alternatingSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LeafNorms.lean#L17)).

**Leaf norms agree with analytic norms.** Proved result. Under the stated hypotheses, the velocity, gradient, curl, Hessian and differentiated-curl squared norms equal their cylindrical array expressions at positive radius. (`leafNorms_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LeafNorms.lean#L23)).

### Breakdown.CertCell.LineGradient

Bounds a line value by the integral of the absolute derivative. The directional consequence supplies the line-gradient estimate used in local field control. Appendix B: cell-system construction and finite certificate analysis.

**Point value by derivative integral.** Proved result. Under the stated hypotheses, twice the absolute point value is bounded by the integral of the absolute derivative. (`two_abs_le_integral_abs_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LineGradient.lean#L9)).

**Unit coordinate vectors are nonzero.** Proved result. Under the stated hypotheses, each coordinate unit vector is nonzero. (`unitVector_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LineGradient.lean#L37)).

**Control a value by a line derivative.** Proved result. Under the stated hypotheses, the absolute field value is at most half the integral of the absolute directional derivative along each coordinate line. (`lineGradientBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LineGradient.lean#L42)).

### Breakdown.CertCell.LocalAngularFrame

States and proves the conversion between the angular derivative and the cylindrical frame components. This connects the analytic angular mode to the finite angular-frame relations. Appendix B: cell-system construction and finite certificate analysis.

**Angular frame relation.** Proved result. Under the stated hypotheses, the angular gradient mode equals the specified linear combination of gradient entries almost everywhere on the cell. (`localAngularFrame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalAngularFrame.lean#L19)).

### Breakdown.CertCell.LocalComponentAngular

Assembles the angular component energy formula from the frame and row identities. The result chooses the appropriate finite form for axis and off-axis cells. Appendix B: cell-system construction and finite certificate analysis.

**Angular component energy value.** Proved result. Under the stated hypotheses, the selected angular matrix form evaluates to the angular energy under the mode-data conditions. (`localComponentAngular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngular.lean#L12)).

### Breakdown.CertCell.LocalComponentAngularAlgebra

Expands the finite row forms and their real quadratic values. These algebraic identities match the angular energy terms, including the separate axis and positive-inner-radius cases. Appendix B: cell-system construction and finite certificate analysis.

**Row form as a matrix product.** Proved result. Under the stated hypotheses, the form built from rows is the conjugate transpose of the row matrix times the middle matrix times the row matrix. (`formOfRows_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L12)).

**Evaluate a row-built quadratic form.** Proved result. Under the stated hypotheses, the row-built form evaluates to the middle matrix form on the vector of row evaluations. (`quad_formOfRows`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L18)).

**Conjugate a Hermitian pairing.** Proved result. Under the stated hypotheses, conjugating the matrix pairing swaps its two vector inputs. (`conj_swap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L27)).

**Hermitian diagonal pairing is real.** Proved result. Under the stated hypotheses, the Hermitian self-pairing equals the complex embedding of its real part. (`conj_re`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L31)).

**Positive form on a nonzero vector.** Proved result. Under the stated hypotheses, the stated positive definite matrix has strictly positive real quadratic value on the nonzero vector. (`pd_re_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L40)).

**Cauchy-Schwarz for a matrix form.** Proved result. Under the stated hypotheses, the squared norm of the matrix pairing is bounded by the product of its two quadratic values. (`sesq_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L45)).

**Inverse form equals a supremum.** Proved result. Under the stated hypotheses, the supremum of the normalized squared pairings equals the inverse quadratic value. (`sup_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L84)).

**Quadratic form preserves addition.** Proved result. Under the stated hypotheses, adding matrices adds their real quadratic values. (`quad_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L116)).

**Test supremum as an inverse form.** Proved result. Under the stated hypotheses, the test supremum equals the inverse Gram-matrix quadratic value under the stated parametrization. (`supremum_eq_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L121)).

**Coefficient formulas for tests.** Proved result. Under the stated hypotheses, the test norm and pairing equal the stated Gram-matrix and moment expressions in coefficient space. (`param_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L142)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L186)).

**Cell rectangle is measurable.** Proved result. The closed rectangle of radial and height coordinates associated with any cell box is measurable in R². (`rect_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L188)).

**Vanishing polynomial coefficients.** Proved result. Under the stated hypotheses, the one-variable polynomial coefficient family is zero under the stated vanishing condition. (`poly1_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L190)).

**Vanishing bivariate coefficients.** Proved result. Under the stated hypotheses, the two-variable coefficient family is zero under the stated vanishing condition. (`poly2_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L213)).

**Angular test Gram matrix is positive.** Proved result. Under the stated hypotheses, the angular test Gram matrix is positive definite under the stated weight and independence hypotheses. (`pairMatrix_pd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L228)).

**Axis test Gram matrix is positive.** Proved result. Under the stated hypotheses, the radius-weighted angular test Gram matrix for an axis cell is positive definite. (`pairMatrix_axis_pd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L288)).

**Off-axis test Gram matrix is positive.** Proved result. Under the stated hypotheses, the off-axis angular test Gram matrix is positive definite. (`pairMatrix_off_pd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L292)).

**Move the radial scaling.** Proved result. Under the stated hypotheses, the stated nonzero radial factor may be moved between the field and test factor. (`axis_pt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L309)).

**Swap four finite sums.** Proved result. Under the stated hypotheses, the four finite sums can be reordered as stated. (`sum_swap4`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L316)).

**Parametrize scaled polynomial tests.** Proved result. Under the stated hypotheses, membership in the scaled polynomial test space is equivalent to the stated angular-test expansion. (`scaled_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L320)).

**Evaluate a parametrized test supremum.** Proved result. Under the stated hypotheses, the test supremum equals the inverse test-Gram form of the moment vector. (`supremum_case`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularAlgebra.lean#L346)).

### Breakdown.CertCell.LocalComponentAngularBasis

Evaluates angular basis rows and their low-order pairings. The polynomial and mode-sum identities supply the basis calculation behind the angular component form. Appendix B: cell-system construction and finite certificate analysis.

**Basis functions are continuous.** Proved result. Under the stated hypotheses, the tensor-product basis function is continuous. (`poly_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L12)).

**Coefficients of a component sum.** Proved result. Under the stated hypotheses, taking a basis coefficient distributes over the fixed component combination. (`coef_modeSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L16)).

**Low row evaluates the component sum.** Proved result. Under the stated hypotheses, the low row is the coefficient-weighted sum of the stored strain slots. (`lowRow_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L39)).

**Low pairing row expansion.** Proved result. Under the stated hypotheses, the low pairing row evaluates to the sum of basis moments times the low coefficient rows. (`lowPair_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L49)).

**Tensor basis is orthonormal.** Proved result. Under the stated hypotheses, the weighted product-basis inner product is one for equal indices and zero otherwise. (`orth2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L62)).

**Expand a test pairing in the basis.** Proved result. Under the stated hypotheses, the test pairing equals the sum of its basis moments times the field coefficients. (`expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L76)).

**Monomials lie in the polynomial span.** Proved result. Under the stated hypotheses, each permitted power lies in the span of the specified basis polynomials. (`pow_span`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L117)).

**Bivariate monomials in the basis span.** Proved result. Under the stated hypotheses, the permitted bivariate monomial lies in the tensor-product basis span. (`mono_span`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L137)).

**Polynomial space through coefficients.** Proved result. Under the stated hypotheses, membership in the polynomial space is equivalent to a finite complex monomial expansion. (`poly_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L155)).

**Basis functions lie in the monomial span.** Proved result. Under the stated hypotheses, each tensor-product basis function lies in the permitted monomial span. (`basis_in_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L172)).

**Projection norm is a coefficient sum.** Proved result. Under the stated hypotheses, the polynomial projection's squared norm equals the sum of squared basis coefficients. (`proj_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentAngularBasis.lean#L186)).

### Breakdown.CertCell.LocalComponentHeight

Evaluates the low height row and height-face component pairings. Their combination identifies the finite height component energy, with the inner contribution determined by the cell geometry. Appendix B: cell-system construction and finite certificate analysis.

**Height low-row value.** Proved result. Under the stated hypotheses, the low row evaluates to the basis coefficient of the component gradient-mode combination. (`heightLowRowValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentHeight.lean#L22)).

**Height face-row value.** Proved result. Under the stated hypotheses, the height face row evaluates to the corresponding analytic height moment. (`heightFaceCompValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentHeight.lean#L52)).

**Height component energy value.** Proved result. Under the stated hypotheses, the height component form evaluates to the height energy. (`localComponentHeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentHeight.lean#L71)).

### Breakdown.CertCell.LocalComponentRadial

Expands the outer radial face and low radial pairings into finite row values. These calculations identify the radial component energy form. Appendix B: cell-system construction and finite certificate analysis.

**Expand a radial outer-face row.** Proved result. Under the stated hypotheses, the weighted face-row sum equals the corresponding polynomial radial-face moment. (`radialOuterFaceExpand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentRadial.lean#L23)).

**Low pairing row as an integral.** Proved result. Under the stated hypotheses, the low pairing row evaluates to the line-weighted component integral. (`radialOuterLowPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentRadial.lean#L129)).

**Radial outer row as an integral.** Proved result. Under the stated hypotheses, the radial outer row evaluates to the stated radius-weighted second-mode test integral. (`radialOuterRowValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentRadial.lean#L237)).

**Radial outer form as a supremum.** Proved result. Under the stated hypotheses, the radial outer quadratic form equals the stated test supremum. (`radialOuterValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentRadial.lean#L357)).

**Radial component energy value.** Proved result. Under the stated hypotheses, the radial projection and boundary forms evaluate to the radial energy. (`localComponentRadial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalComponentRadial.lean#L395)).

### Breakdown.CertCell.LocalEnergyValue

Identifies the unit and curl mode sums with their analytic components. Combining the radial, height and angular component formulas gives the local energy value. Appendix B: cell-system construction and finite certificate analysis.

**Unit array selects a component.** Proved result. Under the stated hypotheses, the unit coefficient array selects one component of the mode field. (`modeSum_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalEnergyValue.lean#L15)).

**Curl array gives a curl component.** Proved result. Under the stated hypotheses, the curl coefficient array gives the corresponding algebraic curl component. (`modeSum_curl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalEnergyValue.lean#L19)).

**Component form gives three energies.** Proved result. Under the stated hypotheses, the component form evaluates to the sum of radial, height and angular energies. (`component_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalEnergyValue.lean#L24)).

**Local energy equals its finite form.** Proved result. Under the stated hypotheses, the finite energy form equals the weighted sum of the component strain and curl energies. (`localEnergyValue_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalEnergyValue.lean#L42)).

### Breakdown.CertCell.LocalFaceHeight

Derives weak axial differentiation and height-face identities for local mode data. The argument supplies the height-component relations used by the finite local rows. Appendix B: cell-system construction and finite certificate analysis.

**Axial gradient integrable at the axis.** Proved result. Under the stated hypotheses, the axial gradient modes are integrable on the stated rectangles reaching the axis. (`localModeHeightAxis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L33)).

**Axial second column is measurable.** Proved result. Under the stated hypotheses, the second-derivative column in the axial direction is almost everywhere strongly measurable. (`axial_second_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L62)).

**Axial second column has finite square.** Proved result. Under the stated hypotheses, the axial second-derivative column has an integrable entry-square sum. (`axial_second_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L66)).

**Axial second mode is a column mode.** Proved result. Under the stated hypotheses, the stated mixed second-derivative mode is the gradient mode of the axial second column. (`modeThird_axial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L81)).

**Radial derivative of an axial column.** Proved result. Under the stated hypotheses, the mixed second mode supplies the weak radial derivative of the axial gradient mode. (`localRadialMixedWeak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L84)).

**Normal derivative on a height face.** Proved result. Under the stated hypotheses, the normal height-face relation gives the two corner values and the differentiated side test. (`localHeightNormal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L132)).

**Angular gradient as a component sum.** Proved result. Under the stated hypotheses, the angular gradient mode is the stated component combination almost everywhere off the axis. (`angularGradMode_comb`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L168)).

**Second derivatives are symmetric a.e..** Proved result. Under the stated hypotheses, the two derivative inputs of the second field commute almost everywhere. (`second_symm_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L223)).

**Second modes swap derivative indices.** Proved result. Under the stated hypotheses, the derivative indices of the second mode commute almost everywhere off the axis. (`modeThird_swap_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L247)).

**Angular derivative of the axial mode.** Proved result. Under the stated hypotheses, the angular derivative of the axial gradient mode has the stated cylindrical-frame formula. (`localAngularHeightMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L265)).

**Height turn from component formulas.** Proved result. Under the stated hypotheses, the height-face angular gradient moment equals the turn functional. (`localHeightTurn_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L281)).

**Height-face turn relation.** Proved result. Under the stated hypotheses, the height-face angular gradient moment equals the turn functional. (`localHeightTurn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceHeight.lean#L356)).

### Breakdown.CertCell.LocalFaceSides

Evaluates weighted sums of local side rows against their traces. The resulting formulas identify the finite side velocity and side gradient data with the analytic boundary quantities. Appendix B: cell-system construction and finite certificate analysis.

**Weighted row sum evaluates data.** Proved result. Under the stated hypotheses, the weighted combination of coordinate rows equals the corresponding finite sum of actual data values. (`weighted_row_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceSides.lean#L16)).

**Side gradient row evaluates its moment.** Proved result. Under the stated hypotheses, the side gradient row applied to true data equals the analytic side gradient value. (`localSideGradientEval_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceSides.lean#L38)).

**Side velocity row evaluates its moment.** Proved result. Under the stated hypotheses, the side velocity row applied to true data equals the analytic side velocity value. (`localSideVelocityEval_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceSides.lean#L159)).

### Breakdown.CertCell.LocalFaceStrip

Introduces the axial phase kernel and proves its continuity and bounds. It identifies the third mode component and its strip traces through this kernel. Appendix B: cell-system construction and finite certificate analysis.

**Second-mode phase kernel.** Definition. This defines the Fourier phase times the chosen second-derivative frame component. (`thirdPhaseKernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L16)).

**Second-mode kernel is continuous.** Proved result. Under the stated hypotheses, the second-mode kernel is jointly continuous in angle and the bilinear map. (`thirdPhaseKernel_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L20)).

**Second-mode kernel norm bound.** Proved result. Under the stated hypotheses, the kernel norm is bounded by the bilinear map norm. (`thirdPhaseKernel_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L27)).

**Second mode as a kernel integral.** Proved result. Under the stated hypotheses, the second-derivative mode is its normalized centered angular kernel integral. (`modeThird_eq_kernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L36)).

**Bilinear norm from basis entries.** Proved result. Under the stated hypotheses, the bilinear operator norm is bounded by the sum of its basis-entry norms. (`bilinear_norm_le_entries`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L46)).

**Second field is locally integrable.** Proved result. Under the stated hypotheses, the second-derivative field is locally integrable. (`second_locallyIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L72)).

**Weighted second modes integrate at axis.** Proved result. Under the stated hypotheses, radius-weighted second modes are integrable on the stated bounded strips reaching the axis. (`weighted_third_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L83)).

**Multiply by a real coefficient.** Proved result. Under the stated hypotheses, the indicated real coefficient times the complex profile is integrable. (`real_coef_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L94)).

**Cell lies in a symmetric strip.** Proved result. Under the stated hypotheses, the cell rectangle lies inside the stated strip symmetric in height. (`rect_subset_strip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L98)).

**Reflected endpoint interval.** Proved result. Under the stated hypotheses, the interval between a cell endpoint and its reflected opposite is the full cell interval. (`Icc_min_max_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L104)).

**Radial side expressions integrate.** Proved result. Under the stated hypotheses, the velocity and gradient radial strip expressions are integrable. (`radial_side_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L110)).

**Height side expressions integrate.** Proved result. Under the stated hypotheses, the velocity and radius-weighted gradient height strip expressions are integrable. (`height_side_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L124)).

**Side strip expressions are integrable.** Proved result. Under the stated hypotheses, the velocity and normal-gradient strip expressions are integrable on every radial or height side permitted by the axis restrictions. (`localSideStripIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceStrip.lean#L151)).

### Breakdown.CertCell.LocalFaceTangent

Uses symmetry of weak second derivatives and cylindrical frame differentiation to derive face tangency relations. Periodic angular identities provide the finite tangent constraints. Appendix B: cell-system construction and finite certificate analysis.

**Second derivative entries are symmetric.** Proved result. Under the stated hypotheses, the second-derivative basis entries are symmetric almost everywhere. (`secondEntrySymm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L16)).

**Expand a vector in the unit basis.** Proved result. Under the stated hypotheses, the vector is the sum of its coordinates times the unit basis. (`spaceSumUnits`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L55)).

**Basis symmetry implies bilinear symmetry.** Proved result. Under the stated hypotheses, symmetry on the unit basis implies symmetry of the bilinear map on arbitrary vectors. (`bilinSymmOfUnits`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L58)).

**Second-derivative frame is periodic.** Proved result. Under the stated hypotheses, the second-derivative frame component repeats after two pi. (`frameThirdPeriodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L66)).

**Second mode with centered angle.** Proved result. Under the stated hypotheses, the second mode is its normalized Fourier integral over the centered angular interval. (`modeThirdCentred`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L70)).

**Swap mixed second modes.** Proved result. Under the stated hypotheses, the two mixed radial-height second modes agree almost everywhere off the axis. (`localModeThirdSwap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L78)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rectCompact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L104)).

**Cell rectangle is measurable.** Proved result. The closed rectangle of radial and height coordinates associated with any cell box is measurable in R². (`rectMeasurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L106)).

**Cell rectangle lies in the strip.** Proved result. Under the stated hypotheses, the cell rectangle lies in the stated bounded axis-reaching strip. (`rectInStrip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L108)).

**Separable weight preserves integrability.** Proved result. Under the stated hypotheses, multiplying by the indicated separable continuous weight preserves cell integrability. (`integrableProductWeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L111)).

**Affine radial gradient weight integrates.** Proved result. Under the stated hypotheses, the affine radial weight times the gradient mode is integrable on the cell. (`affineWeightMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L121)).

**Axial second column square integrates.** Proved result. Under the stated hypotheses, the axial second-column square is integrable. (`axialColumnSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L145)).

**Radial strip integration by parts.** Proved result. Under the stated hypotheses, the radial-strip velocity and axial derivative expressions are integrable and satisfy the zero-boundary height test identity. (`localRadialStripIbp_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L157)).

**Radial strip integration by parts.** Proved result. Under the stated hypotheses, the radial strip expression satisfies the stated zero-boundary height test identity. (`localRadialStripIbp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L207)).

**Polynomial height test is continuous.** Proved result. Under the stated hypotheses, the height polynomial evaluated on the plane is continuous. (`polyEvalHeightContinuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L217)).

**Strip moment from corner traces.** Proved result. Under the stated hypotheses, the tangential derivative strip moment equals its two corner terms minus the strip moment of the test derivative. (`stripMomentByParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L221)).

**The axis is null.** Proved result. Under the stated hypotheses, radius is nonzero almost everywhere in the plane. (`offAxisAe`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L345)).

**Restrict mixed-derivative equality.** Proved result. Under the stated hypotheses, the mixed derivative equality off the axis holds almost everywhere on the cell rectangle. (`aeOnRectOfPositive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L352)).

**Radial tangency from weak derivatives.** Proved result. Under the stated hypotheses, the radial-face tangential moment equals the corner terms minus the side value of the differentiated test. (`localRadialTangent_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L358)).

**Radial tangential moment relation.** Proved result. Under the stated hypotheses, the radial-face tangential moment equals the corner terms minus the differentiated side value. (`localRadialTangent`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTangent.lean#L384)).

### Breakdown.CertCell.LocalFaceTraceFree

Transfers divergence-free and weak-derivative assumptions to trace-free gradient and second-derivative identities. These yield the local face constraints used in the row relation space. Appendix B: cell-system construction and finite certificate analysis.

**Gradient columns are locally integrable.** Proved result. Under the stated hypotheses, each indicated gradient column is locally integrable. (`gradient_column_locInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L15)).

**Second field is locally integrable.** Proved result. Under the stated hypotheses, the second-derivative field is locally integrable. (`second_locInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L28)).

**Derivative of the trace vanishes.** Proved result. Under the stated hypotheses, the indicated trace of the second derivative is zero almost everywhere. (`second_trace_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L44)).

**Gradient-mode trace vanishes.** Proved result. Under the stated hypotheses, the sum of the three diagonal gradient modes vanishes almost everywhere on the cell. (`grad_trace_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L94)).

**Second-mode trace vanishes.** Proved result. Under the stated hypotheses, the corresponding sum of diagonal second modes vanishes almost everywhere on the cell. (`third_trace_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L102)).

**Line-weighted second mode integrates.** Proved result. Under the stated hypotheses, the line-weighted second-derivative mode is integrable on the cell. (`third_weighted_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L128)).

**Gradient mode integrates on the cell.** Proved result. Under the stated hypotheses, the gradient mode is integrable on the cell rectangle. (`grad_rect_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L143)).

**Axis gradient modes are integrable.** Proved result. Under the stated hypotheses, the gradient modes are integrable on an axis cell. (`localAxisGradModeIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L157)).

**Height-face trace vanishes.** Proved result. Under the stated hypotheses, the three diagonal height-face moments sum to zero. (`localFaceHeightTraceFree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L161)).

**Face traces are trace-free.** Proved result. Under the stated hypotheses, the diagonal radial and height face moments each sum to zero. (`localFaceTraceFree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTraceFree.lean#L193)).

### Breakdown.CertCell.LocalFaceTurn

Differentiates cylindrical frame components and evaluates their strip and face traces. The radial and height turn relations then connect the analytic modes to the finite face rows. Appendix B: cell-system construction and finite certificate analysis.

**The axis is null.** Proved result. Under the stated hypotheses, the radial coordinate is nonzero almost everywhere. (`ae_fst_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L18)).

**Cell rectangle is measurable.** Proved result. The closed rectangle of radial and height coordinates associated with any cell box is measurable in R². (`rect_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L25)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_isCompact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L28)).

**Split the radial strip integrand.** Proved result. Under the stated hypotheses, the strip expression splits into the radius-scaled expression and its stated correction. (`strip_pointwise_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L31)).

**Offset-weighted term is integrable.** Proved result. Under the stated hypotheses, the radial offset weight times the gradient and test factors is integrable. (`integrableOn_offset_weight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L47)).

**Radial strip integrand is integrable.** Proved result. Under the stated hypotheses, the affine velocity-gradient strip integrand is integrable. (`integrableOn_strip_integrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L67)).

**Turn relation for a strip integral.** Proved result. Under the stated hypotheses, the strip integral equals the inverse-radius weighted combination of the two component strip integrals. (`strip_integral_turn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L82)).

**Turn relation for a strip moment.** Proved result. Under the stated hypotheses, the radial strip moment equals the indicated inverse-radius combination of component moments. (`radialStripMoment_turn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L176)).

**Turn-component Fourier kernel.** Definition. This defines the Fourier phase times the angular-radial second-derivative frame entry. (`turnKernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L200)).

**Turn kernel is continuous.** Proved result. Under the stated hypotheses, the turn-component kernel is jointly continuous. (`turnKernel_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L203)).

**Turn kernel is norm-bounded.** Proved result. Under the stated hypotheses, the turn-kernel norm is bounded by the second-derivative operator norm. (`turnKernel_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L211)).

**Turn second mode as an integral.** Proved result. Under the stated hypotheses, the turn second mode equals the normalized angular integral of its kernel. (`modeThird_turn_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L222)).

**Compact off-axis set has a box.** Proved result. Under the stated hypotheses, the compact positive-radius set lies in a bounded rectangle separated from the axis. (`compact_sub_offAxis_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L233)).

**Kernel integral is locally integrable.** Proved result. Under the stated hypotheses, the stated kernel representation gives integrability on the off-axis rectangle. (`integrableOn_offAxis_of_kernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L245)).

**Compact test times mode is integrable.** Proved result. Under the stated hypotheses, the supported test times the profile is integrable. (`integrable_test_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L260)).

**Profile locally integrable off axis.** Proved result. Under the stated hypotheses, the profile is locally integrable on the positive-radius domain. (`locallyIntegrableOn_halfPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L273)).

**Expand a vector in coordinates.** Proved result. Under the stated hypotheses, the vector is the sum of its coordinate multiples of the unit basis. (`space_eq_sum_basis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L281)).

**Operator norm from unit columns.** Proved result. Under the stated hypotheses, the operator norm is bounded by the sum of its unit-column norms. (`opNorm_le_sum_basis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L284)).

**Fixed-vector evaluation is integrable.** Proved result. Under the stated hypotheses, applying the locally integrable operator field to a fixed vector preserves local integrability. (`locallyIntegrable_clm_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L293)).

**Second derivatives integrate locally.** Proved result. Under the stated hypotheses, the second-derivative field is locally integrable. (`locallyIntegrable_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L302)).

**Polynomial plane frame.** Definition. This defines radial, angular and axial frame vectors from two plane coordinates. (`planeFrame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L328)).

**Plane frame on the unit circle.** Proved result. Under the stated hypotheses, the polynomial plane frame on cosine and sine equals the cylindrical frame. (`planeFrame_circle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L332)).

**Plane frame coordinates are smooth.** Proved result. Under the stated hypotheses, each coordinate of the polynomial plane frame is smooth. (`planeFrame_coord_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L334)).

**Plane frame is smooth.** Proved result. Under the stated hypotheses, the polynomial plane frame depends smoothly on its two inputs. (`planeFrame_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L339)).

**Plane-frame coordinate functional.** Definition. This defines the linear functional taking the indicated plane-frame coordinate. (`frameCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L342)).

**Frame functional is smooth.** Proved result. Under the stated hypotheses, the plane-frame coordinate functional is smooth in its parameters. (`frameCoord_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L345)).

**Frame functional on the circle.** Proved result. Under the stated hypotheses, on the unit circle the functional is the inner product with the cylindrical frame vector. (`frameCoord_circle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L349)).

**Angular-column functional.** Definition. This defines the functional evaluating a matrix's angular column in the chosen output frame direction. (`angularColumnCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L353)).

**Angular-column functional is smooth.** Proved result. Under the stated hypotheses, the angular-column functional depends smoothly on the plane-frame parameters. (`angularColumnCoord_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L356)).

**Angular-column functional on the circle.** Proved result. Under the stated hypotheses, on the unit circle the functional is the stated cylindrical angular-column pairing. (`angularColumnCoord_circle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L359)).

**Scale a weak derivative identity.** Proved result. Under the stated hypotheses, multiplying both fields by the constant preserves the weak pairing identity. (`weak_identity_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L365)).

**Weak radial derivative of angular column.** Proved result. Under the stated hypotheses, the angular gradient column has the stated radial second mode as its weak radial derivative. (`angularColumn_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L371)).

**Radial turn relation a.e..** Proved result. Under the stated hypotheses, radius times the derivative equals the indicated component combination minus the original field almost everywhere off the axis. (`ae_radial_relation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L413)).

**Second-mode turn formula.** Proved result. Under the stated hypotheses, the angular-radial second-mode entries satisfy their cylindrical-frame turn identities almost everywhere. (`localTurnSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L494)).

**Gradient modes integrate at the axis.** Proved result. Under the stated hypotheses, all indicated gradient modes are integrable on bounded strips reaching the axis. (`localGradModeAxis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L530)).

**Weak radial turn derivative.** Proved result. Under the stated hypotheses, the angular gradient column and its radial second mode satisfy the stated weak cell identity. (`localTurnRadialWeak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L533)).

**Radial face turn formula.** Proved result. Under the stated hypotheses, the angular-gradient radial face moment is the turn functional divided by the side radius. (`localRadialTurn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFaceTurn.lean#L593)).

### Breakdown.CertCell.LocalFieldDefs

Defines local second-order admissibility, finite mode data and the main local-to-finite interfaces. The hypotheses track L6 velocity, square-integrable derivatives, weak differentiation, divergence, pressure and valid cell or label parameters. Appendix B: cell-system construction and finite certificate analysis.

**Local second-order field conditions.** Proposition structure. The interface requires that velocity lies in L6, gradient and second derivative have finite square integrals, weak derivatives agree and divergence vanishes. (`IsLocalSecondOrderField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L22)).

**Locally admissible field tuple.** Proposition definition. The interface requires that the tuple contains a local second-order field and a pressure-gradient field. (`IsLocalAdmissible`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L34)).

**Construct a local second-order field.** Proved result. Under the stated hypotheses, the stated component hypotheses give the local second-order field conditions. (`isLocalSecondOrderField_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L37)).

**Construct a locally admissible tuple.** Proved result. Under the stated hypotheses, the stated field and pressure hypotheses give a locally admissible tuple. (`isLocalAdmissible_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L43)).

**All local relation rows vanish.** Interface. The interface requires that every local relation row evaluates to zero on the true data of an admissible field. (`LocalRelationsHoldStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L47)). Proof route: `Breakdown.CertCell.LocalField.localRelationsHold_of`, `Breakdown.CertCell.LocalField.localRelationsHold`.

**True data satisfy the parametrization.** Interface. The interface requires that the valid cell parametrization fixes the true field data. (`LocalTrueParamStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L52)). Proof route: `Breakdown.CertCell.LocalField.localTrueParam_of`, `Breakdown.CertCell.LocalField.localTrueParam`.

**Radial coefficient relations vanish.** Interface. The interface requires that the radial coefficient relation rows vanish on true local data. (`LocalRelRadialCoefStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L57)). Proof route: `Breakdown.CertCell.LocalField.localRelRadialCoef`.

**Height coefficient relations vanish.** Interface. The interface requires that the height coefficient relation rows vanish on true local data. (`LocalRelHeightCoefStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L62)). Proof route: `Breakdown.CertCell.LocalField.localRelHeightCoef_of`.

**Turn relations vanish.** Interface. The interface requires that the angular-turn relation rows vanish on true local data. (`LocalRelTurnStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L67)). Proof route: `Breakdown.CertCell.LocalField.localRelTurn_of`.

**Trace relations vanish.** Interface. The interface requires that the trace relation rows vanish on true local data. (`LocalRelTraceStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L72)). Proof route: `Breakdown.CertCell.LocalField.localRelTrace`.

**Zero-mode relations vanish.** Interface. The interface requires that the zero-mode relation rows vanish on true local data. (`LocalRelZeroModeStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L77)). Proof route: `Breakdown.CertCell.LocalField.localRelZeroMode`.

**Radial-side relations vanish.** Interface. The interface requires that the radial-side relation rows vanish on true local data. (`LocalRelRadialSideStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L82)). Proof route: `Breakdown.CertCell.LocalField.localRelRadialSide_of`.

**Height-side relations vanish.** Interface. The interface requires that the height-side relation rows vanish on true local data. (`LocalRelHeightSideStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L88)). Proof route: `Breakdown.CertCell.LocalField.Internal.height_side_of_parts`, `Breakdown.CertCell.LocalField.localRelHeightSide_of`.

**Axis relations vanish.** Interface. The interface requires that the axis relation rows vanish on true local data. (`LocalRelAxisStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L94)). Proof route: `Breakdown.CertCell.LocalField.localRelAxis_of`.

**Stream relations vanish.** Interface. The interface requires that the stream relation rows vanish on true local data. (`LocalRelStreamStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L100)). Proof route: `Breakdown.CertCell.LocalField.localRelStream_of`.

**Side-splitting relations vanish.** Interface. The interface requires that the side-splitting relation rows vanish on true local data. (`LocalRelSideSplitStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L106)). Proof route: `Breakdown.CertCell.LocalField.localRelSideSplit_of`.

**Local modes have weighted squares.** Interface. The interface requires that gradient combinations and second-mode combinations are measurable with the stated line- and radius-weighted square integrability. (`LocalModeSquareIntegrableStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L112)). Proof route: `Breakdown.CertCell.LocalField.localModeSquareIntegrable`.

**Radial integration-by-parts interface.** Interface. The interface requires that the line-weighted radial second mode transfers its derivative to a test vanishing on both radial sides. (`LocalModeRadialPartsStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L121)). Proof route: `Breakdown.CertCell.LocalField.localModeRadialParts`.

**Height integration-by-parts interface.** Interface. The interface requires that the line-weighted height second mode transfers its derivative to a test vanishing on both height sides. (`LocalModeHeightPartsStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L130)). Proof route: `Breakdown.CertCell.LocalField.localModeHeightParts`.

**Resolved local energy interface.** Interface. The interface requires that the resolved strain and vorticity energies plus their tails are bounded by the corresponding second-mode square integrals. (`LocalResolvedEnergyStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L138)). Proof route: `Breakdown.CertCell.LocalField.localResolvedEnergy`.

**Gradient modes have weighted squares.** Interface. The interface requires that each gradient mode is measurable and has integrable line-weighted square on the cell. (`LocalModeGradSquareStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L155)). Proof route: `Breakdown.CertCell.LocalField.localModeGradSquare`.

**Local velocity radial weak interface.** Interface. The interface requires that the velocity mode and line-weighted radial gradient are integrable and satisfy the stated zero-boundary weak radial identity. (`LocalModeRadialWeakStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L162)). Proof route: `Breakdown.CertCell.LocalField.localModeRadialWeak`.

**Layout modes are rectangle-integrable.** Interface. The interface requires that the layout velocity and gradient modes are integrable on the cell rectangle. (`LocalModeRectIntegrableStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L171)). Proof route: `Breakdown.CertCell.LocalField.localModeRectIntegrable`.

**Local gradient modes are trace-free.** Interface. The interface requires that the diagonal gradient-mode sum vanishes almost everywhere off the axis. (`LocalModeTraceStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L176)). Proof route: `Breakdown.CertCell.LocalField.localModeTrace`.

**Local strip trace requirement.** Interface. The interface requires that the zero-azimuth radial velocity admits the stated common strip trace for affine radial tests. (`LocalStripTraceStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L181)). Proof route: `Breakdown.CertCell.LocalField.localStripTrace`, `Breakdown.CertCell.LocalField.localStripTrace_of`.

**Radial flux from a strip moment.** Interface. The interface requires that radius times the outer radial strip moment equals the stated bulk radial velocity-gradient integral. (`LocalRadialFluxStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L189)). Proof route: `Breakdown.CertCell.LocalField.localRadialFlux_of`.

**Local velocity height-parts interface.** Interface. The interface requires that the weighted height derivative transfers to the scalar test vanishing at the two height endpoints. (`LocalHeightModeIbpStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L197)). Proof route: `Breakdown.CertCell.LocalField.localHeightModeIbp`.

**Weighted gradient modes reach the axis.** Interface. The interface requires that all radius-weighted gradient modes are integrable on the stated bounded rectangles reaching the axis. (`LocalAxisModeIntegrableStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L206)). Proof route: `Breakdown.CertCell.LocalField.localAxisModeIntegrable`.

**Axis flux moment formula.** Interface. The interface requires that the zero-azimuth radial or angular velocity flux moment equals the specified weighted gradient integrals. (`LocalAxisFluxStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L212)). Proof route: `Breakdown.CertCell.LocalField.localAxisFlux`, `Breakdown.CertCell.LocalField.localAxisFlux_of`.

**Line-weighted local modes integrate.** Interface. The interface requires that the line-weighted velocity and gradient modes are integrable on every valid cell. (`LocalModeIntegrableStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L224)). Proof route: `Breakdown.CertCell.LocalField.localModeIntegrable`.

**Cylindrical angular velocity derivative.** Interface. The interface requires that the angular gradient modes are determined by the azimuthal frequency and the cylindrical frame corrections almost everywhere. (`LocalAngularModeStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L231)). Proof route: `Breakdown.CertCell.LocalField.localAngularMode`.

**Local mode weak identities.** Interface. The interface requires that the velocity and gradient modes satisfy the four stated weak radial, height and mixed derivative identities off the axis. (`LocalModeWeakIdentityStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L241)). Proof route: `Breakdown.CertCell.LocalField.localModeWeakIdentity`.

**Unweighted modes integrate at the axis.** Interface. The interface requires that velocity and gradient modes are integrable on the stated axis-reaching strips. (`LocalModeStripIntegrableStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L252)). Proof route: `Breakdown.CertCell.LocalField.localModeStripIntegrable`.

**Total cylindrical flux vanishes.** Interface. The interface requires that the outer radial flux and the two oriented height fluxes sum to zero. (`LocalCylinderFluxStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L259)). Proof route: `Breakdown.CertCell.LocalField.localCylinderFlux`, `Breakdown.CertCell.LocalField.localCylinderFlux_of`.

**Layout side height-parts identity.** Interface. The interface requires that the line-weighted velocity and height derivative satisfy the stated separable zero-boundary height identity. (`LocalSideHeightPartsStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs.lean#L270)). Proof route: `Breakdown.CertCell.LocalField.localHeightParts_of`.

### Breakdown.CertCell.LocalFieldDefs2

States the component, face, row and energy identities for local admissible fields. It separates axis and off-axis formulas and records the almost-everywhere equality required for local energy transport. Appendix B: cell-system construction and finite certificate analysis.

**Side velocity row evaluates correctly.** Interface. The interface requires that the side velocity row on true data equals its analytic side value for the permitted polynomial test. (`LocalSideVelocityEvalStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L26)). Proof route: `Breakdown.CertCell.LocalField.localSideVelocityEval_of`.

**Side gradient row evaluates correctly.** Interface. The interface requires that the side gradient row on true data equals its analytic side value for the permitted polynomial test. (`LocalSideGradientEvalStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L32)). Proof route: `Breakdown.CertCell.LocalField.localSideGradientEval_of`.

**Radial tangential moment interface.** Interface. The interface requires that the radial-face tangential derivative moment equals the corner terms minus the side value of the test derivative. (`LocalRadialTangentStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L38)). Proof route: `Breakdown.CertCell.LocalField.localRadialTangent_of`, `Breakdown.CertCell.LocalField.localRadialTangent`.

**Radial angular moment interface.** Interface. The interface requires that the radial-face angular-gradient moment equals the turn value divided by the side radius. (`LocalRadialTurnStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L47)). Proof route: `Breakdown.CertCell.LocalField.localRadialTurn`.

**Height-face normal moment interface.** Interface. The interface requires that the height-face radial-gradient moment equals the weighted corner terms minus the side value of the radial test derivative. (`LocalHeightNormalStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L54)). Proof route: `Breakdown.CertCell.LocalField.localHeightNormal`.

**Height-face turn moment interface.** Interface. The interface requires that the height-face angular-gradient moment equals the turn value. (`LocalHeightTurnStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L63)). Proof route: `Breakdown.CertCell.LocalField.localHeightTurn_of`, `Breakdown.CertCell.LocalField.localHeightTurn`.

**Local face traces vanish.** Interface. The interface requires that the sums of diagonal radial and height face moments both vanish under the stated axis restriction. (`LocalFaceTraceFreeStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L70)). Proof route: `Breakdown.CertCell.LocalField.localFaceTraceFree`.

**Local side-strip integrability.** Interface. The interface requires that the velocity and normal-gradient strip expressions are integrable on each permitted radial or height side. (`LocalSideStripIntegrableStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L81)). Proof route: `Breakdown.CertCell.LocalField.localSideStripIntegrable`.

**Strain face row evaluates correctly.** Interface. The interface requires that the strain face value equals the strain face row applied to true local data. (`LocalStrainFaceStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L106)). Proof route: `Breakdown.CertCell.LocalField.localStrainFace_of`, `Breakdown.CertCell.LocalField.localStrainFace_of_turn`, `Breakdown.CertCell.LocalField.localStrainFace`.

**Gradient modes integrate on axis cells.** Interface. The interface requires that all gradient-mode components are integrable on a valid cell whose inner radius is zero. (`LocalAxisGradModeIntegrableStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L112)). Proof route: `Breakdown.CertCell.LocalField.localAxisGradModeIntegrable`.

**Mixed radial weak derivative.** Interface. The interface requires that the axial gradient and mixed second mode satisfy the radial zero-boundary integration-by-parts identity. (`LocalRadialMixedWeakStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L117)). Proof route: `Breakdown.CertCell.LocalField.localRadialMixedWeak`.

**Axial gradient integrates at the axis.** Interface. The interface requires that the axial gradient modes are integrable on the stated bounded strips reaching the axis. (`LocalModeHeightAxisStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L124)). Proof route: `Breakdown.CertCell.LocalField.localModeHeightAxis`.

**Angular derivative of axial gradient.** Interface. The interface requires that the angular derivative of the axial gradient has the three stated cylindrical-frame component formulas almost everywhere. (`LocalAngularHeightModeStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L129)). Proof route: `Breakdown.CertCell.LocalField.localAngularHeightMode`.

**Mixed second modes commute.** Interface. The interface requires that the radial-height and height-radial second modes agree almost everywhere off the axis. (`LocalModeThirdSwapStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L139)). Proof route: `Breakdown.CertCell.LocalField.localModeThirdSwap`.

**Radial strip integration-by-parts.** Interface. The interface requires that the radial-strip velocity and axial derivative expressions are integrable and satisfy the stated height test identity. (`LocalRadialStripIbpStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L144)). Proof route: `Breakdown.CertCell.LocalField.localRadialStripIbp_of`, `Breakdown.CertCell.LocalField.localRadialStripIbp`.

**All gradient modes integrate at axis.** Interface. The interface requires that every gradient-mode component is integrable on the stated bounded axis-reaching strip. (`LocalGradModeAxisStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L160)). Proof route: `Breakdown.CertCell.LocalField.localGradModeAxis`.

**Weak radial derivative of a turn mode.** Interface. The interface requires that the angular gradient column is integrable and has the indicated weighted weak radial derivative. (`LocalTurnRadialWeakStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L165)). Proof route: `Breakdown.CertCell.LocalField.localTurnRadialWeak`.

**Angular-radial second-mode formulas.** Interface. The interface requires that the angular-radial second modes have the stated frequency and frame-correction formulas almost everywhere. (`LocalTurnSecondStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L174)). Proof route: `Breakdown.CertCell.LocalField.localTurnSecond`.

**Local radial trace identity.** Interface. The interface requires that the gradient mode and its radial derivative have the stated integrability and oriented boundary trace formula. (`LocalRadialTraceStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L185)). Proof route: `Breakdown.CertCell.LocalField.localRadialTrace`.

**Local height weak-pair requirement.** Interface. The interface requires that the gradient mode and axial second mode form the specified height weak pair on each valid cell. (`LocalHeightModeWeakStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L197)). Proof route: `Breakdown.CertCell.LocalField.localHeightModeWeak`.

**Angular frame relation requirement.** Interface. The interface requires that the angular gradient mode is the specified finite linear combination of gradient modes almost everywhere on the cell. (`LocalAngularFrameStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L203)). Proof route: `Breakdown.CertCell.LocalField.localAngularFrame`.

**True data represent the local field.** Interface. The interface requires that the layout's true data represent the admissible local velocity, gradient and second derivative. (`LocalRepresentsStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L211)). Proof route: `Breakdown.CertCell.LocalField.localRepresents_of`, `Breakdown.CertCell.LocalField.localRepresents`.

**Radial trace-pair conditions.** Proposition definition. The interface requires that the field and derivative have the stated weighted integrability and radial integration-by-parts formula with boundary moments. (`RadialTracePair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L216)).

**Finite mode-data conditions.** Proposition structure. The interface requires that stored coefficients, face moments, weak derivatives and angular frame relations agree with the represented mode fields. (`IsModeData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L223)).

**Component combination of modes.** Definition. This defines the fixed complex coefficient combination of matrix-mode entries. (`modeSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L237)).

**Radial energy-form requirement.** Interface. The interface requires that the radial projection and boundary forms evaluate to the radial energy of the component combination. (`LocalComponentRadialStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L241)). Proof route: `Breakdown.CertCell.LocalField.localComponentRadial`.

**Height energy-form requirement.** Interface. The interface requires that the height projection and boundary forms evaluate to the height energy of the component combination. (`LocalComponentHeightStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L252)). Proof route: `Breakdown.CertCell.LocalField.localComponentHeight`.

**Angular energy-form requirement.** Interface. The interface requires that the axis or off-axis angular matrix form evaluates to the angular energy of the radius-weighted angular second modes. (`LocalComponentAngularStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L263)). Proof route: `Breakdown.CertCell.LocalField.localComponentAngular`.

**Local energy-form requirement.** Interface. The interface requires that the finite energy form equals the weighted sum of the component strain and curl energies. (`LocalEnergyValueStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L273)). Proof route: `Breakdown.CertCell.LocalField.localEnergyValue_of`.

**Combine two represented fields.** Interface. The interface requires that the first represented field plus i times the second satisfies the complex finite mode-data conditions. (`LocalModeDataPairStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L291)). Proof route: `Breakdown.CertCell.LocalField.localModeDataPair_of`.

**A.e. equality preserves local energies.** Interface. The interface requires that almost-everywhere equal fields and derivatives give equal radial, height and angular energies on the cell. (`EnergyAeCongrStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalFieldDefs2.lean#L302)). Proof route: `Breakdown.CertCell.LocalField.energyAeCongr`.

### Breakdown.CertCell.LocalHeightWeak

Establishes local integrability of gradient and second-derivative columns and their weak height derivative relation. A smooth approximation argument yields the height-mode identity. Appendix B: cell-system construction and finite certificate analysis.

**Local gradient is integrable locally.** Proved result. Under the stated hypotheses, the local gradient field is locally integrable. (`localGradient_locInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalHeightWeak.lean#L20)).

**Local second columns integrate locally.** Proved result. Under the stated hypotheses, each local second-derivative column is locally integrable. (`localSecondColumn_locInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalHeightWeak.lean#L26)).

**Gradient has its weak second derivative.** Proved result. Under the stated hypotheses, the gradient field and second-derivative column satisfy the stated distributional derivative identity. (`localGradient_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalHeightWeak.lean#L32)).

**Weak height derivative of gradient modes.** Proved result. Under the stated hypotheses, the gradient mode has the corresponding axial second mode as its weak height derivative. (`localHeightSmoothWeak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalHeightWeak.lean#L51)).

**Weighted local modes are integrable.** Proved result. Under the stated hypotheses, the radius-weighted gradient and axial second mode are integrable on the stated bounded strip. (`localWeightedModes_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalHeightWeak.lean#L72)).

**Separable weighted height identity.** Proved result. Under the stated hypotheses, the radius-weighted gradient and second mode satisfy the separable height test identity. (`localProductWeak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalHeightWeak.lean#L103)).

**Height mode weak pair holds.** Proved result. Under the stated hypotheses, the gradient mode and its axial second mode form the required height weak pair. (`localHeightModeWeak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalHeightWeak.lean#L145)).

### Breakdown.CertCell.LocalModeDataPair

Proves weighted integrability of products of local modes and polynomial tests on a compact cell rectangle. It evaluates the pairings and extracts the finite local mode data. Appendix B: cell-system construction and finite certificate analysis.

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L18)).

**Cell rectangle is measurable.** Proved result. The closed rectangle of radial and height coordinates associated with any cell box is measurable in R². (`rect_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L20)).

**Continuous factors preserve integrals.** Proved result. Under the stated hypotheses, multiplying a cell-integrable function by the continuous factor preserves integrability. (`integrableOn_continuous_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L22)).

**Combine two cell integrals.** Proved result. Under the stated hypotheses, the combined function's integral equals the first integral plus i times the second. (`integral_pair_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L26)).

**Line weight is continuous.** Proved result. Under the stated hypotheses, the line weight embedded in the complex numbers is continuous. (`lineWeight_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L32)).

**Radial basis polynomial is continuous.** Proved result. Every radial basis polynomial is continuous as a function of the real radial coordinate. (`radialPoly_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L40)).

**Height basis polynomial is continuous.** Proved result. Every height basis polynomial is continuous as a function of the real height coordinate. (`heightPoly_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L44)).

**Coefficients of a harmonic combination.** Proved result. Under the stated hypotheses, the coefficient of the first field plus i times the second is the same combination of coefficients. (`coef_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L48)).

**Radial trace integrand is integrable.** Proved result. Under the stated hypotheses, the affine radial trace expression times the test is integrable. (`radial_term_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L62)).

**Height trace integrand is integrable.** Proved result. Under the stated hypotheses, the radius-weighted affine height trace expression times the test is integrable. (`height_term_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L82)).

**A nonunit binary index is zero.** Proved result. Under the stated hypotheses, the indicated binary index is zero. (`fin_two_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L95)).

**Radial moments combine linearly.** Proved result. Under the stated hypotheses, the radial face moment of combined inputs is the first moment plus i times the second. (`radialFaceMoment_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L100)).

**Height moments combine linearly.** Proved result. Under the stated hypotheses, the height face moment of combined inputs is the first moment plus i times the second. (`heightFaceMoment_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L125)).

**Radial trace pairing is integrable.** Proved result. Under the stated hypotheses, the sum of derivative-test and field-test-derivative terms is integrable. (`trace_term_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L148)).

**Combine radial trace pairs.** Proved result. Under the stated hypotheses, the first radial trace pair plus i times the second is a radial trace pair. (`radialTracePair_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L178)).

**Combine height weak pairs.** Proved result. Under the stated hypotheses, the first height weak pair plus i times the second is a height weak pair. (`heightWeakPair_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L206)).

**Rows preserve a harmonic combination.** Proved result. Under the stated hypotheses, a row evaluates the first data vector plus i times the second by the same combination of row values. (`row_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L230)).

**Complex mode data from two fields.** Proved result. Under the stated hypotheses, combining two represented local fields gives the required complex mode data. (`localModeDataPair_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeDataPair.lean#L239)).

### Breakdown.CertCell.LocalModeIntegrable

Combines the local weak-field estimates into integrability of cylindrical modes and their angular or axial derivatives. These conditions permit the trace and energy calculations on the cell rectangle. Appendix B: cell-system construction and finite certificate analysis.

**Local velocity and gradient integrate.** Proved result. Under the stated hypotheses, the line-weighted local velocity and gradient modes are integrable on valid cells. (`localModeIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrable.lean#L17)).

**Angular modes satisfy frame formulas.** Proved result. Under the stated hypotheses, the angular velocity derivatives satisfy the frequency and frame-correction formulas almost everywhere. (`localAngularMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrable.lean#L23)).

**Axial translation of a cylinder point.** Proved result. Under the stated hypotheses, adding an axial coordinate vector translates the cylinder height by the same amount. (`cylPoint_add_axial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrable.lean#L67)).

**Axial translation of a gradient mode.** Proved result. Under the stated hypotheses, translating the field axially translates the height argument of its gradient mode. (`gradMode_add_axial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrable.lean#L72)).

**Weighted modes integrate on axis strips.** Proved result. Under the stated hypotheses, the radius-weighted gradient modes are integrable on the stated strips reaching the axis. (`localAxisModeIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrable.lean#L77)).

**Local layout modes are integrable.** Proved result. Under the stated hypotheses, the layout velocity and gradient modes are integrable on the cell rectangle. (`localModeRectIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrable.lean#L119)).

**Unweighted local strip modes integrate.** Proved result. Under the stated hypotheses, the velocity and gradient modes are integrable on the stated bounded strips reaching the axis. (`localModeStripIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrable.lean#L159)).

### Breakdown.CertCell.LocalModeIntegrableParts

Proves convolution estimates and differentiation formulas for smooth approximations. The resulting square and sixth-power bounds pass local Sobolev control to the weak field modes. Appendix B: cell-system construction and finite certificate analysis.

**Norm power after mollification.** Proved result. Under the stated hypotheses, the norm power of the mollified field is bounded by the mollification of its norm power. (`normPow_conv_le_of_dom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L17)).

**Finite sum of integrals under a bound.** Proved result. Under the stated hypotheses, the sum of the indicated integrals is bounded by the integral of their common total majorant. (`sum_integral_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L77)).

**Mollified column-square bound.** Proved result. Under the stated hypotheses, the sum of mollified column squares is bounded by the mollified energy majorant. (`conv_sum_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L92)).

**Differentiate the mollified field.** Proved result. Under the stated hypotheses, the derivative of the mollified field is the mollification of its weak derivative column. (`mollify_fderiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L106)).

**L6 means integrable sixth power.** Proved result. Under the stated hypotheses, membership in L6 is equivalent to integrability of the sixth power of the norm. (`memLp_six_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L138)).

**Cutoff gradient tail estimate.** Proved result. Under the stated hypotheses, the cutoff-gradient L2 term is controlled by the stated constant times the L6 tail norm. (`cross_tail_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L144)).

**L6 tails tend to zero.** Proved result. Under the stated hypotheses, the L6 norm outside expanding balls tends to zero. (`tail_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L203)).

**Smooth Sobolev estimate.** Proved result. Under the stated hypotheses, the smooth field's L6 norm is bounded by the stated Sobolev constant times its gradient L2 norm. (`smooth_six_of_six`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L234)).

**Compact weak Sobolev estimate.** Proved result. Under the stated hypotheses, the L6 norm is bounded by the stated Sobolev constant times three times the square root of the energy integral. (`six_bound_of_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L298)).

**Weak derivative of a cut-off column.** Proved result. Under the stated hypotheses, the cut-off gradient column has the product-rule weak derivative. (`cutoff_column_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L369)).

**Cut-off columns belong to L6.** Proved result. Under the stated hypotheses, each smoothly cut-off gradient column belongs to L6. (`cutoff_column_memLp_six`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L410)).

**Cut-off gradient belongs to L6.** Proved result. Under the stated hypotheses, the smoothly cut-off gradient field belongs to L6. (`cutoff_memLp_six`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeIntegrableParts.lean#L447)).

### Breakdown.CertCell.LocalModeWeak

Derive the weak radial and height derivative identities for Fourier coefficients of a local second-order field, using smooth moving-frame coordinate maps. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Cylindrical frame from planar data.** Definition. Build the radial, angular and axial frame vectors from a planar pair. (`planeFrameAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L19)).

**The planar frame restricts to the circle.** Proved result. On a cosine-sine pair, the planar frame is the usual cylindrical orthonormal frame. (`planeFrameAt_circle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L23)).

**A moving-frame coordinate.** Definition. Read a vector component in the frame determined by a planar pair. (`planeFrameCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L25)).

**A frame coordinate on the circle.** Definition. Restrict the planar frame-coordinate map to the unit circle. (`circleFrameCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L28)).

**A circle coordinate is a frame pairing.** Proved result. The circle-frame coordinate of a vector is its inner product with the selected frame unit vector. (`circleFrameCoord_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L30)).

**Cylindrical frame is smooth.** Proved result. Every Cartesian component of (q₁,q₂,0), (−q₂,q₁,0) and (0,0,1) is smooth in q ∈ R², giving smooth extensions of the cylindrical frame off the unit circle. (`planeFrameAt_coord_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L34)).

**Cylindrical frame is smooth.** Proved result. The three vector-valued functions (q₁,q₂,0), (−q₂,q₁,0) and (0,0,1) are smooth on R² and restrict to the cylindrical frame on the unit circle. (`planeFrameAt_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L40)).

**Frame coordinate is smooth.** Proved result. The moving-frame coordinate map is smooth. (`planeFrameCoord_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L43)).

**A radial column coordinate.** Definition. Apply a linear map to the radial frame vector and read its chosen output component. (`planeRadialColumnCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L47)).

**A radial column on the circle.** Definition. Restrict the radial-column evaluator to the unit circle. (`circleRadialColumnCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L50)).

**Radial column is smooth.** Proved result. The radial-column coordinate map is smooth. (`planeRadialColumnCoord_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L53)).

**Read a radial matrix column in the frame.** Proved result. The radial-column evaluator pairs the image of the radial unit vector with the selected output frame vector. (`circleRadialColumnCoord_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L56)).

**Expand a vector in the coordinate basis.** Proved result. Every spatial vector equals the sum of its coordinate multiples of the standard basis vectors. (`space_eq_sum_coords`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L62)).

**Bound an operator by its columns.** Proved result. The operator norm is at most the sum of the norms of its coordinate columns. (`opNorm_le_sum_columns`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L65)).

**Norms preserve local integrability.** Proved result. Under the declaration's hypotheses, the pointwise norm of a locally integrable function is locally integrable. (`locallyIntegrable_norm_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L74)).

**Integrable columns give integrable maps.** Proved result. Under the declaration's hypotheses, local integrability of all coordinate columns gives local integrability of the full operator-valued field. (`locallyIntegrable_of_columns`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L78)).

**Gradient columns are square integrable.** Proved result. Under the declaration's hypotheses, each coordinate column of the gradient belongs to the spatial L2 space. (`gradient_column_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L89)).

**Hessian entries are square integrable.** Proved result. Under the declaration's hypotheses, contracting the Hessian with two coordinate unit vectors gives a spatially square-integrable vector field. (`second_entry_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L100)).

**Smooth tests inside the half-plane.** Proposition definition. A half-plane test is smooth, compactly supported and supported where the radius is positive. (`IsHalfPlaneTest`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L116)).

**Differentiate a half-plane test.** Proved result. Under the declaration's hypotheses, a constant-direction derivative of a smooth supported half-plane test is again such a test. (`isHalfPlaneTest_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L119)).

**Mixed smooth derivatives commute.** Proved result. For a smooth scalar test, differentiating in the two constant directions commutes. (`fderiv_fderiv_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L124)).

**Recover the mixed weak derivative.** Proved result. Under the declaration's hypotheses, the three specified weak derivative identities imply the remaining mixed weak derivative identity. (`weak_mixed_of_three`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L136)).

**Scale a weak derivative identity.** Proved result. Under the declaration's hypotheses, multiplying both field entries by the same constant preserves the stated weak derivative pairing. (`weak_identity_const_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L151)).

**Frame coordinates are inner products.** Proved result. A cylindrical vector coordinate is the inner product with the corresponding frame unit vector. (`frameVec_eq_inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L157)).

**Local modes have weak derivatives.** Proved result. The local Fourier modes satisfy the stated radial and height weak derivative identities. (`localModeWeakIdentity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L161)).

**Weak radial derivatives of local modes.** Proved result. The local velocity modes have the specified radial weak derivatives. (`localModeRadialWeak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L227)).

**Height integration by parts for modes.** Proved result. Local modes satisfy the height integration-by-parts identity. (`localHeightModeIbp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalModeWeak.lean#L270)).

### Breakdown.CertCell.LocalRadialPieces

Identify the finite radial quadratic forms with the projected radial energy and the interior test supremum. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The low row reads a combined coefficient.** Proved result. Under the declaration's hypotheses, the low row applied to coefficient data equals the cell-basis coefficient of the chosen matrix-weighted mode combination. (`radialRowValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialPieces.lean#L17)).

**Radial weak integration by parts.** Proved result. Under the declaration's hypotheses, the pairing of the differentiated mode combination with a separated test equals minus the pairing of the original combination with the radial derivative of that test. (`radialFieldParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialPieces.lean#L59)).

**Low row equals the weighted pairing.** Proved result. Under the declaration's hypotheses, the low pairing row evaluated on the field data equals the cell integral of the selected mode combination times its test weight. (`radialLowPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialPieces.lean#L94)).

**The radial form equals projected energy.** Proved result. Under the declaration's hypotheses, the radial projection quadratic form equals the inner-radius factor times the weighted square norm of the radial derivative of the polynomial projection. (`localRadialProjPiece`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialPieces.lean#L199)).

**The interior form equals a test supremum.** Proved result. For a cell away from the axis, the interior radial form equals the weighted polynomial-test supremum of the corresponding second-derivative combination. (`localRadialInnerPiece`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialPieces.lean#L243)).

**Combine the two radial energy pieces.** Proved result. Under the declaration's hypotheses, the sum of the projection form and the applicable interior form equals the sum of their projected energy and test-supremum expressions. (`localRadialLowPieces`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialPieces.lean#L297)).

### Breakdown.CertCell.LocalRadialTrace

Obtain radial weak traces of gradient modes from the local second-order field hypotheses. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The local Hessian is locally integrable.** Proved result. Under the declaration's hypotheses, the Hessian of a local second-order field is locally integrable in space as a bilinear operator-valued field. (`localSecondLocallyIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialTrace.lean#L16)).

**Gradient modes have radial weak traces.** Proved result. Under the declaration's hypotheses, the local gradient mode and the radial second-derivative mode form the stated radial weak derivative pair. (`localRadialWeakMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialTrace.lean#L24)).

**Weighted radial Hessian modes integrate.** Proved result. Under the declaration's hypotheses, the radial Hessian-mode coefficient multiplied by the cell weight is integrable on the cell rectangle. (`localThirdLineIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialTrace.lean#L84)).

**Gradient modes integrate on the cell.** Proved result. Under the declaration's hypotheses, each local gradient Fourier coefficient is integrable on the cell rectangle. (`localGradRectIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialTrace.lean#L94)).

**Radial traces of local gradient modes.** Proved result. Local gradient modes have the stated radial trace pairs. (`localRadialTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRadialTrace.lean#L109)).

### Breakdown.CertCell.LocalRelations

Assemble the ten local coefficient and boundary relations, then place the true field data in the admissible parameter space. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**True data satisfy the local relations.** Proved result. Under the hypotheses of this declaration, the true local data satisfy the full set of local linear relations. (`localRelationsHold_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelations.lean#L17)).

**True local data give valid parameters.** Proved result. Under the hypotheses of this declaration, the true local data define an admissible cell parameter. (`localTrueParam_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelations.lean#L34)).

**Local strip traces are well defined.** Proved result. The local weak strip traces have the required values and integrability. (`localStripTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelations.lean#L41)).

**The local cylindrical flux relation.** Proved result. The local modes satisfy the cylindrical flux identity. (`localCylinderFlux`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelations.lean#L44)).

**The local axial flux relation.** Proved result. The local modes satisfy the axial flux identity. (`localAxisFlux`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelations.lean#L47)).

**True data satisfy the local relations.** Proved result. The true local data satisfy the full set of local linear relations. (`localRelationsHold`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelations.lean#L50)).

**True local data give valid parameters.** Proved result. The true local data define an admissible cell parameter. (`localTrueParam`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelations.lean#L58)).

### Breakdown.CertCell.LocalRelationsA

Prove the radial and height coefficient equations and the trace, zero-mode and radial-side relations for true local data. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The radial coefficient relation.** Proved result. The true local coefficients satisfy the radial derivative row. (`localRelRadialCoef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L18)).

**Recover velocity from height modes.** Proved result. Under the declaration's hypotheses, a velocity coefficient is a finite combination of axial gradient coefficients, weighted by the height polynomial derivative and divided by the height eigenvalue. (`coef_height_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L88)).

**True data satisfy the height relation.** Proved result. Assuming the local height integration-by-parts interface, every height relation row annihilates the true data of a locally admissible field. (`height_row_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L177)).

**The radial axis is a null set.** Proved result. The first coordinate is nonzero almost everywhere for planar Lebesgue measure. (`ae_first_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L206)).

**The height coefficient relation.** Proved result. Under the hypotheses of this declaration, the true local coefficients satisfy the height derivative row. (`localRelHeightCoef_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L215)).

**The local trace-free relation.** Proved result. The true local coefficients satisfy the trace-free gradient relation. (`localRelTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L218)).

**The local zero-mode relation.** Proved result. The true local coefficients satisfy the required zero-mode relation. (`localRelZeroMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L236)).

**The radial side relation.** Proved result. Under the hypotheses of this declaration, the true local data satisfy the radial-side integration-by-parts row. (`localRelRadialSide_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsA.lean#L261)).

### Breakdown.CertCell.LocalRelationsB

Turn weak mode identities into axial, stream, cylindrical-flux and segmented-side relations. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The local axial flux relation.** Proved result. Under the hypotheses of this declaration, the local modes satisfy the axial flux identity. (`localAxisFlux_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L20)).

**The axis relation for true data.** Proved result. Under the hypotheses of this declaration, the true local data satisfy the axis relation. (`localRelAxis_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L55)).

**The stream relation for true data.** Proved result. Under the hypotheses of this declaration, the true local data satisfy the stream-flux relation. (`localRelStream_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L105)).

**The local radial flux identity.** Proved result. Under the hypotheses of this declaration, the local weak traces satisfy the radial flux identity. (`localRadialFlux_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L227)).

**Local gradient modes are trace-free.** Proved result. The local gradient modes have vanishing trace. (`localModeTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L250)).

**The local cylindrical flux relation.** Proved result. Under the hypotheses of this declaration, the local modes satisfy the cylindrical flux identity. (`localCylinderFlux_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L272)).

**Local strip traces are well defined.** Proved result. Under the hypotheses of this declaration, the local weak strip traces have the required values and integrability. (`localStripTrace_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L298)).

**Split an extra velocity moment.** Proved result. Under the declaration's hypotheses, an extra side-velocity moment equals the sum of segment velocity moments multiplied by the overlaps of their test polynomials with the original side test. (`localExtraSplit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L308)).

**Side data split over their segments.** Proved result. Under the hypotheses of this declaration, the true side data split into the stored segment moments. (`localRelSideSplit_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsB.lean#L391)).

### Breakdown.CertCell.LocalRelationsTurnSide

Convert angular differentiation and height integration by parts into the corresponding finite cell rows. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Pairing distributes over row addition.** Proved result. Pairing the sum of two finite rows with a test vector equals the sum of their pairings. (`turn_pair_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L18)).

**Radius multiplication stays in the span.** Proved result. Under the declaration's hypotheses, the radial basis polynomial multiplied by radius has a finite expansion in the retained radial basis. (`turn_shift_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L22)).

**Coefficients of radius multiplication.** Proved result. Under the declaration's hypotheses, the weighted integral of radius times two radial basis polynomials is the corresponding coefficient in the expansion of the radius-multiplied polynomial. (`turn_shift_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L39)).

**Tensor-product basis continuity.** Proved result. The product of a radial basis polynomial and a height basis polynomial, viewed as a complex plane function, is continuous. (`turn_basis_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L56)).

**The radial axis is a null set.** Proved result. The first coordinate is nonzero almost everywhere for planar Lebesgue measure. (`turn_axis_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L61)).

**Radius multiplication of coefficients.** Proved result. Under the declaration's hypotheses, multiplying the radial coefficient vector by the weighted radius-overlap matrix gives the cell coefficients of the radius-weighted field. (`turn_coef_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L67)).

**Cell coefficients are complex linear.** Proved result. Under the declaration's hypotheses, the cell coefficient of a complex linear combination is the same linear combination of the two cell coefficients. (`turn_coef_lin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L105)).

**The local angular coefficient relation.** Proved result. Under the hypotheses of this declaration, the true local coefficients satisfy the angular derivative row. (`localRelTurn_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L120)).

**Height parts on the local cell side.** Proved result. Under the hypotheses of this declaration, the local side data satisfy height integration by parts. (`localHeightParts_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L176)).

**The local height-side relation.** Proved result. Under the hypotheses of this declaration, the true local data satisfy the height-side row. (`height_side_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L210)).

**The local height-side relation.** Proved result. Under the hypotheses of this declaration, the true local data satisfy the height-side row. (`localRelHeightSide_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalRelationsTurnSide.lean#L341)).

### Breakdown.CertCell.LocalResolvedEnergy

Bound the resolved cell energy by the weighted square integral of the field second derivative. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Square bounds for local gradient modes.** Proved result. The squared local gradient modes obey the stated square-integral bounds. (`localModeGradSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L16)).

**Local mode squares are integrable.** Proved result. The required local mode square densities are integrable. (`localModeSquareIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L22)).

**The local gradient is locally integrable.** Proved result. Under the declaration's hypotheses, the gradient field of a local second-order field is locally integrable as an operator-valued field. (`locGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L44)).

**Hessian columns are locally integrable.** Proved result. Under the declaration's hypotheses, contracting a local Hessian with any coordinate unit vector gives a locally integrable operator-valued field. (`locSecondCol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L50)).

**The local Hessian is locally integrable.** Proved result. Under the declaration's hypotheses, a local second-order field has a locally integrable Hessian. (`locSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L56)).

**The Hessian is a weak derivative.** Proved result. Under the declaration's hypotheses, in every coordinate direction, pairing the gradient field with the derivative of a scalar test equals minus pairing the Hessian in that direction with the test. (`weakGradOp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L61)).

**Weak radial derivative of a mode.** Proved result. Under the declaration's hypotheses, the radial weak derivative of a gradient mode is its radial Hessian mode. (`weakRadialPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L82)).

**Weighted Hessian modes are integrable.** Proved result. Under the declaration's hypotheses, the radial Hessian mode multiplied by the cell line weight is integrable on the cell rectangle. (`thirdInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L103)).

**Weighted gradient modes are integrable.** Proved result. Under the declaration's hypotheses, the gradient mode multiplied by the cell line weight is integrable on the cell rectangle. (`gradInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L122)).

**Radial Hessian modes are a.e. measurable.** Proved result. Under the declaration's hypotheses, the radial Hessian Fourier coefficient is almost everywhere strongly measurable on the cell rectangle. (`thirdMeas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L128)).

**Real radial integration by parts.** Proved result. Under the declaration's hypotheses, the gradient mode paired with the radial derivative of the weighted real test is integrable, and its cell integral is minus the pairing of the radial Hessian mode with that weighted test. (`realRadialParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L143)).

**Complex radial integration by parts.** Proved result. Under the declaration's hypotheses, both terms in the weighted radial integration-by-parts identity are integrable on the cell, and the Hessian-mode test pairing is minus the gradient-mode pairing with the derivative of the weighted test. (`entryRadialParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L157)).

**Weak height derivative of a mode.** Proved result. Under the declaration's hypotheses, the height weak derivative of a gradient mode is the gradient-mode transform of the Hessian contracted with the axial unit vector. (`weakHeightPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L201)).

**Radial parts for local gradient modes.** Proved result. The local gradient and second-derivative modes satisfy radial integration by parts. (`localModeRadialParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L225)).

**Height parts for local gradient modes.** Proved result. The local gradient and second-derivative modes satisfy height integration by parts. (`localModeHeightParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L249)).

**Second modes bound resolved energy.** Proved result. For a local second-order field and azimuthal mode zero on axis cells, the radial, height and angular resolved energies plus their tails are bounded by the radius-weighted integral of the three Hessian-mode squares. (`comboBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L284)).

**Combined Hessian energy is integrable.** Proved result. Under the declaration's hypotheses, the radius-weighted sum of the squared norms of the three selected Hessian-mode combinations is integrable on the cell rectangle. (`comboIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L300)).

**Bound the resolved local energy.** Proved result. The resolved local cell energy is bounded by the corresponding weighted second-derivative energy. (`localResolvedEnergy`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalResolvedEnergy.lean#L314)).

### Breakdown.CertCell.LocalStrainFace

Show that strain-face rows evaluate to physical face traces, completing the representation of true cell data. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Evaluate a row on true cell data.** Definition. Evaluate a finite row by summing its coefficients against the true field data. (`rowValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L23)).

**Evaluate a sum of rows.** Proved result. The value of the sum of two rows is the sum of their values on the same field data. (`rowValue_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L25)).

**Evaluate a difference of rows.** Proved result. The value of the difference of two rows is the difference of their values on the same field data. (`rowValue_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L29)).

**Evaluate a negated row.** Proved result. Negating a row negates its value on field data. (`rowValue_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L33)).

**Scale a row evaluation.** Proved result. Multiplying a row by a complex scalar multiplies its value by the same scalar. (`rowValue_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L37)).

**A unit row reads its true datum.** Proved result. Evaluating the unit row at a datum index returns that true field datum. (`rowValue_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L41)).

**A finite power sum is a polynomial.** Proved result. A weighted sum of powers from zero through degree D defines a polynomial function of degree at most D. (`polyFn_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L51)).

**Increase a polynomial degree bound.** Proved result. Under the declaration's hypotheses, a polynomial satisfying the smaller degree bound also satisfies the larger bound. (`polyFn_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L60)).

**Differentiate a polynomial degree bound.** Proved result. Under the declaration's hypotheses, differentiating the polynomial lowers the stated degree bound by one. (`polyFn_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L64)).

**A radial factor raises polynomial degree.** Proved result. Under the declaration's hypotheses, multiplying a polynomial function by the radial variable raises its degree bound by one. (`polyFn_mulX`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L71)).

**Forget a particular polynomial bound.** Proved result. Under the declaration's hypotheses, a function satisfying a specified finite polynomial degree bound is a polynomial function. (`polyFn_any`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L78)).

**A corner row reads the physical corner.** Proved result. Under the declaration's hypotheses, evaluating the corner row on true data gives the corresponding physical corner value. (`cornerRow_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L82)).

**Decode a radial side index.** Proved result. Encoding a radial side as a four-side index and decoding it returns the original side index. (`radialIndex_val`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L112)).

**Decode a height side index.** Proved result. Encoding a height side by adding two and then decoding it returns the original side index. (`heightIndex_val`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L116)).

**Strain rows give physical face values.** Proved result. Under the hypotheses of this declaration, the finite strain-face rows evaluate to the corresponding physical traces. (`localStrainFace_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L124)).

**Strain rows give physical face values.** Proved result. Under the hypotheses of this declaration, the finite strain-face rows evaluate to the corresponding physical traces. (`localStrainFace_of_turn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L208)).

**True data represent the local field.** Proved result. Under the hypotheses of this declaration, the true local datum vector represents the field in the specified cell layout. (`localRepresents_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L213)).

**Strain rows give physical face values.** Proved result. The finite strain-face rows evaluate to the corresponding physical traces. (`localStrainFace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L245)).

**True data represent the local field.** Proved result. The true local datum vector represents the field in the specified cell layout. (`localRepresents`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LocalStrainFace.lean#L248)).

### Breakdown.CertCell.LowSlotFormValue

Expand strain and velocity slots to identify their finite quadratic form with the low-mode field pairing. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Separate strain and velocity slots.** Definition. Identify low slots with the disjoint union of their strain and velocity index sets. (`slotSplit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L21)).

**Separate strain and velocity slots.** Proved result. A sum over all low slots is the sum over strain components and their larger polynomial range plus the sum over velocity components and their smaller range. (`sum_slot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L29)).

**Reconstruct one strain component.** Proved result. The weighted sum of all low-slot strain fields reduces to the tensor-product basis expansion of the selected strain component. (`strain_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L36)).

**Reconstruct one velocity component.** Proved result. The weighted sum of all low-slot velocity fields reduces to the tensor-product basis expansion of the selected velocity component. (`velocity_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L42)).

**Conjugate linearity on the left.** Proved result. The matrix sesquilinear pairing of a finite linear combination in its first argument is the sum of the component pairings with conjugated coefficients. (`sesq_sum_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L48)).

**Linearity in the second argument.** Proved result. The matrix sesquilinear pairing of a finite linear combination in its second argument is the sum of the component pairings with the original coefficients. (`sesq_sum_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L56)).

**Expand the combined low field in slots.** Proved result. The paired low strain and velocity field is the sum of the paired slot fields multiplied by the corresponding finite data coordinates. (`pair_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L63)).

**The slot quadratic form.** Proved result. The row-built quadratic form is the real part of the double matrix sum of slot data with the first data factor conjugated. (`value_slot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L77)).

**Low slots give the field quadratic form.** Proved result. The finite low-slot quadratic form equals the low-mode field pairing. (`lowSlotFormValue_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/LowSlotFormValue.lean#L91)).

### Breakdown.CertCell.MeanStretchModeSum

Express the time and angular mean of the stretching form as an absolutely summable interaction of shifted Fourier modes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Velocity and gradient coordinates.** Definition. Use a disjoint union to index three velocity coordinates and nine gradient coordinates. (`Slot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L21)).

**Stretching as a bilinear pairing.** Definition. Evaluate the stretching bilinear form after separating velocity and gradient slots. (`pairForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L23)).

**Curl is additive in the gradient.** Proved result. The curl extracted from a sum of gradient matrices is the sum of their extracted curls. (`curlOfGrad_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L27)).

**Curl commutes with scalar multiplication.** Proved result. Scaling every gradient entry scales each extracted curl component by the same complex scalar. (`curlOfGrad_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L31)).

**Vorticity gradients add.** Proved result. The vorticity gradient extracted from a pointwise sum of Hessian entries is the sum of the extracted vorticity gradients. (`curlGradOfSecondDeriv_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L37)).

**Vorticity gradients scale.** Proved result. Under the declaration's hypotheses, scaling each Hessian entry by a complex scalar scales the extracted vorticity gradient by that scalar. (`curlGradOfSecondDeriv_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L41)).

**Add Hessians before extracting vorticity.** Proved result. The vorticity gradient extracted from the sum of two Hessian tensors is the sum of their extracted vorticity gradients. (`curlGradOfSecondDeriv_add'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L47)).

**Scale Hessians to scale vorticity.** Proved result. Under the declaration's hypotheses, the vorticity gradient of a scalar multiple of a Hessian tensor is that scalar times the original vorticity gradient. (`curlGradOfSecondDeriv_smul'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L51)).

**A zero gradient has zero curl.** Proved result. The curl extracted from the zero gradient matrix is zero in every component. (`curlOfGrad_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L55)).

**Zero Hessians give zero vorticity slope.** Proved result. The vorticity gradient extracted from the zero Hessian tensor is zero in every entry. (`curlGradOfSecondDeriv_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L58)).

**The first pairing argument is additive.** Proved result. The stretching pairing distributes over addition in its first perturbation argument. (`pairForm_add_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L61)).

**The second pairing argument is additive.** Proved result. The stretching pairing distributes over addition in its second perturbation argument. (`pairForm_add_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L66)).

**Scale the first pairing argument.** Proved result. Multiplying the first perturbation argument by a complex scalar multiplies the stretching pairing by that scalar. (`pairForm_smul_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L71)).

**Scale the second pairing argument.** Proved result. Multiplying the second perturbation argument by a complex scalar multiplies the stretching pairing by that scalar. (`pairForm_smul_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L76)).

**The stretching bilinear map.** Definition. Package the stretching pairing as a complex bilinear map. (`pairLinear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L81)).

**Coordinate expansion of stretching.** Proved result. The stretching pairing is the double sum of its coordinate-basis pairings multiplied by the two input coordinates. (`pairForm_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L86)).

**The background data enter additively.** Proved result. Adding two pairs of background gradient and Hessian data adds their stretching pairings. (`pairForm_add_W`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L104)).

**Scale both background derivative tensors.** Proved result. Scaling both the background gradient and Hessian by the same complex scalar scales the stretching pairing by that scalar. (`pairForm_smul_W`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L110)).

**Zero background gives zero stretching.** Proved result. The stretching pairing vanishes when both background gradient and Hessian are zero. (`pairForm_zero_W`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L115)).

**Add background modes inside the pairing.** Proved result. Under the declaration's hypotheses, the stretching pairing distributes over simultaneous finite sums of the background gradient and Hessian. (`pairForm_sum_W`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L120)).

**Conjugate all stretching inputs.** Proved result. Conjugating both background tensors and both perturbation arguments conjugates the stretching pairing. (`pairForm_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L128)).

**Conjugate backgrounds with real inputs.** Proved result. For a real perturbation slot vector, conjugating the background gradient and Hessian conjugates its stretching pairing with itself. (`pairForm_real_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L135)).

**Use a harmonic background expansion.** Proved result. Under the declaration's hypotheses, a real stretching pairing equals the real part of the weighted sum of the pairings of its harmonic background gradient and Hessian components. (`re_pairForm_of_expansion`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L142)).

**Second derivatives in the moving frame.** Definition. Read a second derivative in a frame rotated with the point and both input directions. (`frameSecondDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L178)).

**Vorticity gradient from the Hessian.** Definition. Contract a real second-derivative tensor with the alternating symbol to obtain the vorticity gradient. (`curlGradReal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L181)).

**The real stretching form.** Definition. Combine the strain-vorticity quadratic term with the velocity-gradient bilinear term. (`realForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L184)).

**Write stretching in real coordinates.** Proved result. The physical stretching form equals the real coordinate form built from the reference gradient, vorticity gradient and perturbation data. (`stretchFormWith_eq_realForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L187)).

**Expand a unit vector in a rotated frame.** Proved result. A coordinate unit vector is the sum of rotated unit vectors weighted by the corresponding row of the rotation matrix. (`unit_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L194)).

**Rotate a real linear combination.** Proved result. Axial rotation commutes with a finite real linear combination of vectors. (`axialRot_sum_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L200)).

**Transform all three Hessian indices.** Proved result. Each Hessian entry is reconstructed from its rotated-frame entries using one rotation-matrix factor for each of its output and two input indices. (`secondDeriv_coord_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L205)).

**Change frame in the vorticity gradient.** Proved result. The Cartesian vorticity gradient is the rotation conjugate of the vorticity gradient extracted from the Hessian in the rotated frame. (`vortGrad_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L223)).

**Transpose rotation cancels rotation.** Proved result. Applying the transpose rotation after the corresponding vector rotation returns the original vector. (`rotT_rotVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L239)).

**Stretching is rotation invariant.** Proved result. Simultaneously rotating all vector and matrix inputs leaves the real stretching form unchanged. (`realForm_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L244)).

**Complexifying commutes with curl.** Proved result. The complex curl contraction of a real matrix equals the complex cast of its real curl. (`curlOfGrad_ofReal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L258)).

**Complexify the vorticity gradient.** Proved result. Under the declaration's hypotheses, the complex contraction of a real Hessian equals the complex cast of its real vorticity gradient. (`curlGradOfSecondDeriv_ofReal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L264)).

**Store velocity and gradient together.** Definition. Place velocity and gradient entries in their respective parts of the slot index. (`slotOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L270)).

**complex pairing recovers real stretch.** Proved result. The complex stretching pairing on real coordinate data equals the complex cast of the real stretching form. (`pairForm_ofReal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L272)).

**Inverse rotation uses transposed entries.** Proved result. A coordinate of the inverse-rotated vector is the sum of the original coordinates weighted by a column of the forward rotation matrix. (`rotNeg_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L297)).

**Expand a rotated coordinate vector.** Proved result. A rotated coordinate unit vector is the sum of coordinate unit vectors weighted by its rotation-matrix column. (`col_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L300)).

**Compose two Hessian frame rotations.** Proved result. Transforming all three indices of a Hessian in one rotated frame by a second rotation gives its components in the frame at the sum of the angles. (`frame_shift3`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L304)).

**Compose two gradient frame rotations.** Proved result. Transforming both indices of a gradient in one rotated frame by a second rotation gives its components in the frame at the sum of the angles. (`frame_shift2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L324)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`axialRot_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L341)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`axialRot_neg_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L344)).

**The frame Hessian has unit time period.** Proved result. Under the declaration's hypotheses, adding one to time leaves each moving-frame Hessian component unchanged. (`frameSecondDeriv_periodic_time`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L349)).

**frame Hessian has full angular period.** Proved result. Adding two pi to the frame angle leaves every Hessian component unchanged. (`frameSecondDeriv_periodic_angle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L353)).

**The orbit gradient has unit time period.** Proved result. Under the declaration's hypotheses, adding one to time leaves every moving-frame gradient component unchanged. (`fibGrad_periodic_time`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L357)).

**orbit gradient has full angular period.** Proved result. Adding two pi to angle leaves every moving-frame gradient component unchanged. (`fibGrad_periodic_angle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L361)).

**Hessian mode at time zero.** Proved result. At base time zero, a Hessian mode is the time-angle integral of its moving-frame component times the negative Fourier phase, normalized by one over two pi. (`modeSecondDeriv_zero_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L365)).

**Gradient mode at time zero.** Proved result. At base time zero, a gradient mode is the time-angle integral of its moving-frame component times the negative Fourier phase, normalized by one over two pi. (`modeGrad_zero_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L371)).

**Separate a sum over three indices.** Proved result. A sum over triples of coordinate indices equals the three nested coordinate sums. (`sum_triple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L376)).

**Separate a sum over a product pair.** Proved result. A sum over pairs of coordinate indices equals the two nested coordinate sums. (`sum_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L380)).

**Reconstruct the moving-frame Hessian.** Proved result. Under the declaration's hypotheses, a moving-frame Hessian entry is the finite sum of real parts of its Fourier coefficients multiplied by their positive time-angle phases. (`frameSecondDeriv_expansion`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L384)).

**Reconstruct the moving-frame gradient.** Proved result. Under the declaration's hypotheses, a moving-frame gradient entry is the finite sum of real parts of its Fourier coefficients multiplied by their positive time-angle phases. (`frameGrad_expansion`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L428)).

**Evaluate stretching in the orbit frame.** Proved result. At a rotated point, the physical stretching density equals the real form evaluated on the moving-frame field coordinates. (`stretchFormWith_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L475)).

**Field slots along a rotation orbit.** Definition. Read the velocity or gradient slot along a time and rotation orbit. (`slotFn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L494)).

**Fourier coefficients of field slots.** Definition. Store the velocity and gradient Fourier coefficients in one slot vector. (`slotMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L497)).

**A slot mode is its scalar Fourier mode.** Proved result. The scalar torus coefficient of a field slot equals the corresponding entry of the combined velocity-gradient mode vector. (`torusMode_slotFn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L500)).

**Expand stretching by background modes.** Proved result. Under the declaration's hypotheses, stretching along the time-angle orbit is the sum of real parts of phase-weighted pairings using each background mode and the full perturbation slot vector. (`orbit_stretch_expansion`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L506)).

**Iterated integral on the time torus.** Proved result. Under the declaration's hypotheses, the integral over one time period followed by one angular period equals the integral for the corresponding product measure. (`iter_eq_box_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L526)).

**Bound the pairing by its matrix entries.** Proved result. The norm of the stretching pairing is bounded by the double sum of its coordinate-entry norms multiplied by the corresponding input coordinate norms. (`norm_pairForm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L533)).

**mean pairing has a convergent mode sum.** Proved result. Under the declaration's hypotheses, the phase-weighted stretching pairing is integrable on the time-angle box, and its normalized integral is the absolutely convergent sum of symmetrized pairings of each mode with the conjugate shifted mode. (`pairing_mean`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L541)).

**Symmetrize the stretching interaction.** Proved result. Under the declaration's hypotheses, the three-mode stretching interaction equals the average of the two orders of the bilinear slot pairing. (`stretchTriple_eq_pairForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L623)).

**Stretching equals a mode interaction sum.** Proved result. Under the declaration's hypotheses, the normalized orbit average of stretching equals the finite sum over background modes of absolutely summable perturbation interactions with their shifted conjugate modes. (`point_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L634)).

**Expand a vector in the coordinate basis.** Proved result. Every spatial vector equals the sum of its coordinate multiples of the standard basis vectors. (`basis_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L681)).

**Coordinate unit vectors have norm one.** Proved result. Every coordinate unit vector has norm one. (`norm_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L685)).

**Bound the operator norm by entry energy.** Proved result. The squared operator norm is at most three times the sum of squared matrix-column norms. (`opNorm_sq_le_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L688)).

**Gradient field is continuous.** Proved result. Under the hypotheses of this declaration, the spatial gradient field is continuous. (`continuous_gradField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L703)).

**Orbit slots are square integrable.** Proved result. Under the declaration's hypotheses, each chosen velocity or gradient slot is square integrable on the one-period time-angle box. (`memLp_slot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L716)).

**Translation preserves plane measure.** Proved result. Adding a fixed pair of real numbers to a point in the plane preserves two-dimensional Lebesgue measure. (`measurePreserving_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L738)).

**Shifted frame Hessians are integrable.** Proved result. Under the declaration's hypotheses, each entry of the time-angle shifted Hessian expressed in the rotating frame is integrable on the time-angle box. (`integrable_shift_secondDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L742)).

**Shifted frame gradients are integrable.** Proved result. Under the declaration's hypotheses, each entry of the time-angle shifted gradient expressed in the rotating frame is integrable on the time-angle box. (`integrable_shift_grad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L763)).

**Mean stretching equals its mode sum.** Proved result. Under the hypotheses of this declaration, the mean stretching form equals its absolutely summable Fourier interaction sum. (`meanStretchModeSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchModeSum.lean#L785)).

### Breakdown.CertCell.MeanStretchOrbit

Transfer measurability and local square integrability to almost every time and rotation orbit. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Cylindrical orbits preserve null sets.** Proved result. The map from half-plane and time-angle coordinates to spacetime pulls volume-null sets back to null sets. (`quasiMeasurePreserving_orbitPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L19)).

**Transfer null sets to rotation orbits.** Proved result. Under the declaration's hypotheses, an almost-everywhere spacetime property holds for almost every time-angle point on almost every half-plane orbit. (`ae_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L30)).

**Most orbit slices are measurable.** Proved result. For almost every half-plane base point, restricting the spacetime field to its time-angle orbit is almost everywhere strongly measurable. (`ae_aestronglyMeasurable_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L34)).

**The torus product measure.** Proved result. The time-angle box measure is the product of volume restricted to one time period and one angular period. (`boxMeasure_eq_prod`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L40)).

**Torus measure is absolutely continuous.** Proved result. The restricted time-angle measure is absolutely continuous with respect to planar Lebesgue measure. (`boxMeasure_ac`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L43)).

**The spacetime orbit map is continuous.** Proved result. Mapping time and angle to the corresponding spacetime point on a fixed cylindrical orbit is continuous. (`continuous_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L48)).

**Compare two angular integration windows.** Proved result. For a nonnegative function of angular period two pi, its integral over one positive period is at most twice its integral over the symmetric period. (`lintegral_window_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L55)).

**Angular integrals vary measurably.** Proved result. Under the declaration's hypotheses, the nonnegative angular integral of a measurable spacetime function along a cylindrical orbit is measurable in its radial-height point and time. (`measurable_orbitSlice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L83)).

**Cylindrical integration on an orbit.** Proved result. Under the declaration's hypotheses, integrating a nonnegative spacetime function over positive radii, all heights, one time period and one angular period with radial Jacobian equals its one-period spacetime integral. (`lintegral_orbit_cylindrical`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L94)).

**Almost every orbit has finite integral.** Proved result. Under the declaration's hypotheses, local finiteness of the one-period spacetime integral implies finiteness of the time-angle orbit integral at almost every half-plane point. (`ae_lintegral_orbit_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L112)).

**Most orbit slices are square integrable.** Proved result. For almost every half-plane point, the time-angle orbit restriction is square integrable over one period box. (`ae_memLp_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchOrbit.lean#L178)).

### Breakdown.CertCell.MeanStretchTorus

Establish phase multiplication, conjugation and shifted Parseval pairings on the time-angle torus. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The time-angle Fourier phase.** Definition. Form the angle 2π times the time frequency times time, plus the angular frequency times angle. (`waveArg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L17)).

**The complex Fourier phase.** Definition. Exponentiate the imaginary time-angle phase. (`phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L19)).

**A scalar time-angle Fourier mode.** Definition. Take the normalized Fourier average of a real scalar function on the time-angle torus. (`torusMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L21)).

**The averaging factor has negative phase.** Proved result. The Fourier averaging factor is the exponential of minus i times the time-angle phase angle. (`expFactor_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L23)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`norm_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L26)).

**Fourier phase is continuous.** Proved result. The complex Fourier phase is continuous. (`continuous_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L30)).

**Subtract frequencies and phase angles.** Proved result. The time-angle phase angle at the difference of two frequencies is the difference of their phase angles. (`waveArg_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L34)).

**Adding frequencies adds phase angles.** Proved result. The time-angle phase angle at the sum of two frequencies is the sum of their phase angles. (`waveArg_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L38)).

**Negate the frequency and phase angle.** Proved result. Reversing both frequency indices negates the time-angle phase angle. (`waveArg_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L42)).

**Multiplying by a wave shifts the label.** Proved result. Multiplying the negative Fourier exponential by a positive phase subtracts the phase label from the Fourier label. (`expFactor_mul_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L46)).

**Fourier exponential labels add.** Proved result. Multiplying two negative Fourier exponentials adds their labels. (`expFactor_mul_expFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L53)).

**Conjugate a Fourier exponential.** Proved result. Conjugating the negative Fourier exponential reverses both frequency indices. (`conj_expFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L60)).

**Negative phases preserve integrability.** Proved result. Under the declaration's hypotheses, multiplying an integrable real function by the negative Fourier exponential gives an integrable complex function on the time-angle box. (`integrable_expFactor_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L68)).

**Positive phases preserve integrability.** Proved result. Under the declaration's hypotheses, multiplying an integrable real function by the positive Fourier phase gives an integrable complex function on the time-angle box. (`integrable_phase_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L75)).

**Fourier coefficient as a box integral.** Proved result. Under the declaration's hypotheses, a torus Fourier coefficient is the product-measure integral against the negative Fourier phase, normalized by one over two pi. (`torusMode_eq_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L82)).

**Opposite torus modes are conjugates.** Proved result. Under the declaration's hypotheses, the Fourier coefficient of a real torus function at the negative frequency is the conjugate of its original coefficient. (`torusMode_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L89)).

**Cosine is a sum of two exponentials.** Proved result. The complex value of a real cosine is half the sum of its positive and negative complex exponentials. (`ofReal_cos_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L99)).

**Sine is a difference of exponentials.** Proved result. The complex value of a real sine is the difference of its negative and positive exponentials multiplied by i divided by two. (`ofReal_sin_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L103)).

**Integrability with trigonometric factors.** Proved result. Under the declaration's hypotheses, multiplying an integrable function by a continuous function of its harmonic phase angle preserves integrability on the time-angle box when that factor has absolute value at most one. (`integrable_mul_trig`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L108)).

**Cosine multiplication averages two modes.** Proved result. Under the declaration's hypotheses, multiplying by a cosine averages the two Fourier coefficients shifted by the cosine frequency. (`torusMode_mul_cos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L119)).

**Sine multiplication subtracts two modes.** Proved result. Under the declaration's hypotheses, multiplying by a sine gives i divided by two times the difference of the positively and negatively shifted coefficients. (`torusMode_mul_sin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L135)).

**Squared Fourier modes are summable.** Proved result. Under the declaration's hypotheses, the squared absolute values of the torus Fourier coefficients form a summable family over all integer frequency pairs. (`hasSum_normSq_torusMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L151)).

**Summable shifted Fourier norm products.** Proved result. Under the declaration's hypotheses, the products of Fourier coefficient norms with norms of the shifted coefficients of the second function form a summable family. (`summable_norm_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L159)).

**Fourier pairing with shifted frequencies.** Proved result. Under the declaration's hypotheses, the product of each Fourier coefficient with the conjugate coefficient shifted by the background frequency sums to the normalized integral of the product times the positive background phase. (`hasSum_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L170)).

**Fourier exponential has unit time period.** Proved result. Adding one to time preserves the negative Fourier exponential at integer temporal frequency. (`expFactor_add_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L263)).

**Compensate a temporal Fourier shift.** Proved result. The negative Fourier phase at one time equals its value at that time plus a shift multiplied by the positive temporal phase of the shift. (`expFactor_time_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L272)).

**Translation phases the torus coefficient.** Proved result. Under the declaration's hypotheses, translating a periodic integrand in time and angle multiplies its Fourier coefficient by the positive phase of that translation. (`shifted_average`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/MeanStretchTorus.lean#L280)).

### Breakdown.CertCell.ModeAxisIntegrable

Control weighted Fourier modes on rectangles that can meet the axis by cylindrical integration. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The temporal Fourier factor.** Definition. Use the complex exponential with negative temporal frequency in the time average. (`timePhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L20)).

**Velocity mode integrand.** Definition. Multiply a rotated velocity coordinate by its angular Fourier factor. (`velEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L22)).

**Gradient mode integrand.** Definition. Read a rotated gradient entry with its angular Fourier factor. (`gradEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L25)).

**Second-derivative mode integrand.** Definition. Read a rotated second-derivative entry with its angular Fourier factor. (`slopeEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L28)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`phase_norm_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L32)).

**Temporal phase is continuous.** Proved result. The temporal Fourier factor is continuous. (`timePhase_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L36)).

**The temporal phase has extended norm one.** Proved result. The temporal Fourier factor has extended norm one. (`enorm_timePhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L40)).

**Rotated coordinate vectors have norm one.** Proved result. Axial rotation preserves the norm one of a coordinate unit vector. (`rot_unit_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L43)).

**A rotated component is norm bounded.** Proved result. The norm of any coordinate of an axially rotated real vector is at most the original vector norm. (`rot_comp_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L46)).

**Velocity evaluator is contractive.** Proved result. The absolute value of the phase-weighted velocity evaluator is at most the norm of its vector input. (`velEval_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L50)).

**Gradient evaluator is contractive.** Proved result. The absolute value of the phase-weighted gradient evaluator is at most the operator norm of its input. (`gradEval_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L54)).

**Hessian evaluator is contractive.** Proved result. The absolute value of the phase-weighted Hessian evaluator is at most the bilinear operator norm of its input. (`slopeEval_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L60)).

**Continuity of the angular exponential.** Proved result. The negative angular-frequency complex exponential is continuous in angle. (`phase_pair_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L68)).

**Velocity evaluator is continuous.** Proved result. The velocity Fourier evaluator is continuous. (`velEval_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L72)).

**Gradient evaluator is continuous.** Proved result. The gradient Fourier evaluator is continuous. (`gradEval_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L78)).

**Hessian evaluator is continuous.** Proved result. The second-derivative Fourier evaluator is continuous. (`slopeEval_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L87)).

**Bound a cylindrical strip by a ball.** Proved result. Under the declaration's hypotheses, the radius-weighted angular integral over a bounded radial-height strip is bounded by the spatial integral over the ball of radius twice the absolute outer radius plus the absolute heights of both endpoints. (`strip_orbit_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L97)).

**Weighted orbit integrability at the axis.** Proved result. Under the declaration's hypotheses, the radius-weighted, temporally phased orbit mode restricted to the radial-height rectangle is integrable over the plane and one time period. (`weighted_orbit_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L148)).

**Weighted mode integrability on strips.** Proved result. Under the declaration's hypotheses, the mode multiplied by radius is integrable on the closed radial-height strip, including a possible endpoint on the axis. (`weighted_mode_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L195)).

**Velocity mode through angular averaging.** Proved result. A plane velocity mode is the one-period time integral of its angular orbit mode times the temporal phase, normalized by one over two pi. (`vel_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L214)).

**Gradient mode through angular averaging.** Proved result. A plane gradient mode is the one-period time integral of its angular orbit mode times the temporal phase, normalized by one over two pi. (`grad_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L228)).

**Hessian mode through angular averaging.** Proved result. A plane Hessian mode is the normalized temporal Fourier integral of its angular orbit mode, with the derivative and matrix-column indices ordered as in the evaluator. (`slope_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L242)).

**Weighted modes integrate at the axis.** Proved result. For an admissible perturbation, the radius-weighted velocity, gradient and Hessian plane modes are integrable on bounded rectangles reaching the axis. (`modeAxisIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisIntegrable.lean#L259)).

### Breakdown.CertCell.ModeAxisPlainIntegrable

Lift local cosine and sine estimates to unweighted plane modes on rectangles meeting the axis. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Plane coefficients from time harmonics.** Proved result. Under the declaration's hypotheses, at almost every point of positive radius, the spacetime velocity and gradient modes equal the local modes of their cosine time harmonics plus the imaginary unit times the modes of their sine harmonics. (`plane_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisPlainIntegrable.lean#L23)).

**Radius is positive almost everywhere.** Proved result. Almost every point of a rectangle with nonnegative radial endpoints has strictly positive radius. (`ae_radius_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisPlainIntegrable.lean#L54)).

**Unweighted modes integrate at the axis.** Proved result. For an admissible perturbation, the unweighted velocity and gradient plane modes are integrable on bounded rectangles reaching the axis. (`modeAxisPlainIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeAxisPlainIntegrable.lean#L67)).

### Breakdown.CertCell.ModeConjugate

Identify negative Fourier labels with complex conjugates for real-valued orbit data. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Opposite modes are complex conjugates.** Proved result. The mode average of real component data at the negative frequency is the complex conjugate of the original mode average. (`modeAverage_neg_eq_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeConjugate.lean#L13)).

**Negative modes are conjugates.** Proved result. Negating a Fourier label conjugates the corresponding real-field mode. (`modeConjugate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeConjugate.lean#L28)).

### Breakdown.CertCell.ModeDensityBridgeLinks

Reduce the full-space lattice energy and stretching integrals to the weighted half-plane integrals used by the cells. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Reduce lattice density to a half-plane.** Proved result. Under the declaration's hypotheses, the spatial integral of the sum of mode densities equals four pi times the sum of their relabelled, radius-weighted integrals on the half-plane. (`lattice_reduction`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinks.lean#L16)).

**Reduce stretching to a half-plane.** Proved result. Under the declaration's hypotheses, the one-period spacetime integral of the nonnegative stretching density equals four pi times the radius-weighted half-plane integral of its normalized time-angle average. (`stretch_reduction`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinks.lean#L75)).

### Breakdown.CertCell.ModeDensityBridgeLinksParts

Check the measurability, rotation invariance and reflection symmetry required by the mode-density reduction. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Mode energy is independent of base time.** Proved result. Under the declaration's hypotheses, the mode-energy term at any base time equals its value at time zero. (`modeTerm_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L21)).

**Mode energy is axially invariant.** Proved result. Under the declaration's hypotheses, the mode-energy term is unchanged when the spatial point is rotated around the axis. (`modeTerm_rot_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L31)).

**Derivative norms inherit axial symmetry.** Proved result. Under the declaration's hypotheses, the norm of an iterated derivative of an axially invariant scalar function is unchanged by axial rotation of its evaluation point. (`norm_iteratedFDeriv_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L46)).

**The gradient weight is axially invariant.** Proved result. Under the declaration's hypotheses, the gradient weight of the symmetric field is unchanged by rotating the spatial point around the axis. (`wtGrad_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L52)).

**The Hessian weight is axially invariant.** Proved result. Under the declaration's hypotheses, the second-derivative norm weight is unchanged by rotating the spatial point around the axis. (`secondDerivNorm_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L57)).

**The mode density is axially invariant.** Proved result. For fixed energy arguments, the mode density has the same value at a point and at any axial rotation of that point. (`modeDensity_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L61)).

**Positivity indicators are measurable.** Proved result. Under the declaration's hypotheses, the indicator of positivity of a measurable real function is measurable. (`measurable_ind_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L106)).

**Forward weight sum is measurable.** Proved result. Under the hypotheses of this declaration, the forward interaction-weight sum is measurable. (`measurable_fwdSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L111)).

**Backward weight sum is measurable.** Proved result. Under the hypotheses of this declaration, the backward interaction-weight sum is measurable. (`measurable_backSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L121)).

**Inward weight is measurable.** Proved result. Under the hypotheses of this declaration, the inward interaction weight is measurable. (`measurable_inward`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L131)).

**Outward weight is measurable.** Proved result. Under the hypotheses of this declaration, the outward interaction weight is measurable. (`measurable_outward`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L143)).

**Gradient weight is measurable.** Proved result. For any scalar weight f on R³, y ↦ ‖Df(y)‖ is measurable when Df is assigned zero at points where f is not differentiable. (`measurable_wtGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L158)).

**Hessian weight is measurable.** Proved result. Under the hypotheses of this declaration, the second-derivative norm weight is measurable. (`measurable_secondDerivNorm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L161)).

**Measurability of density coefficients.** Proved result. Under the declaration's hypotheses, the share coefficient and the three energy-density coefficients are measurable functions of position. (`measurable_coefs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L164)).

**Hessian mode is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the spacetime second-derivative Fourier coefficient is almost everywhere strongly measurable for the stated measure. (`aesm_modeSecondDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L247)).

**Mode norms are a.e. strongly measurable.** Proved result. Under the declaration's hypotheses, the square root of the sum of squared absolute entries of an almost everywhere measurable complex field is almost everywhere strongly measurable. (`aesm_sqrt_cnormSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L260)).

**Mode curl is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the curl extracted from a gradient matrix is almost everywhere strongly measurable for the stated measure. (`aesm_curlOfGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L267)).

**Vorticity gradient is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the vorticity gradient extracted from the Hessian is almost everywhere strongly measurable for the stated measure. (`aesm_curlGradOfSecondDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L274)).

**Mode-energy term is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the mode-energy term is almost everywhere strongly measurable for the stated measure. (`aesm_modeTerm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L281)).

**Off-lattice modes have zero energy.** Proved result. Assuming the class-support interface, a mode outside the symmetry lattice has zero energy term at almost every spatial point. (`ae_modeTerm_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L309)).

**Zero height is negligible in spacetime.** Proved result. Almost every spacetime point has nonzero height. (`ae_height_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L322)).

**Reflected energies agree a.e..** Proved result. Under the declaration's hypotheses, almost everywhere in space, reflecting the point and reversing the angular frequency preserves the mode-energy term at time zero. (`ae_modeTerm_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L327)).

**Points with rotation-invariant modes.** Definition. Collect points where all relevant labelled densities are invariant under axial rotation. (`goodSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L339)).

**Good points are rotation invariant.** Proved result. Under the declaration's hypotheses, rotating a point preserves membership in the set where all mode terms are rotation invariant. (`goodSet_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L344)).

**Mode invariance almost everywhere.** Proved result. Under the declaration's hypotheses, almost every spatial point lies in the set where all labelled mode terms are rotation invariant. (`ae_goodSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeDensityBridgeLinksParts.lean#L355)).

### Breakdown.CertCell.ModeFlip

Transfer the imposed spatial reflection through weak derivatives and Fourier mode extraction. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A reflection sign squares to one.** Proved result. Multiplying the coordinate reflection sign by itself gives one. (`frameSign_mul_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L25)).

**Reflection changes two coordinate signs.** Proved result. The spatial reflection preserves the first coordinate and negates the second and third coordinates. (`flipPoint_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L29)).

**Spatial reflection is an involution.** Proved result. Applying the spatial reflection twice returns the original point. (`flipPoint_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L32)).

**Reflect a coordinate unit vector.** Proved result. The coordinate unit vector is multiplied by its reflection sign, positive for the first coordinate and negative for the other two. (`flipPoint_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L36)).

**Reflection commutes with real scaling.** Proved result. Reflecting a real scalar multiple of a spatial vector gives the same scalar multiple of its reflection. (`flipPoint_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L41)).

**Reflection reverses rotation.** Proved result. Reflecting before axial rotation equals rotating through the opposite angle before reflecting. (`axialRot_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L46)).

**Reverse a basis rotation by reflection.** Proved result. A coordinate unit vector rotated by the negative angle equals its reflected positive-angle rotation times its coordinate reflection sign. (`axialRot_neg_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L56)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`axialRot_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L62)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`axialRot_neg_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L65)).

**Reflect the angle and its frequency.** Proved result. Reversing the angular frequency and negating the angular variable together leave the negative Fourier exponential unchanged. (`expFactor_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L70)).

**Reflect a full-period integral.** Proved result. For a function of period 2π, reversing the angular variable leaves its full-period integral unchanged. (`integral_neg_of_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L76)).

**A linear map expands in its columns.** Proved result. Applying a real linear map to a vector equals the sum of its coordinate-basis images weighted by the vector coordinates. (`clm_apply_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L82)).

**Local integrability under isometries.** Proved result. Under the declaration's hypotheses, precomposing a locally integrable field with the spatial isometry preserves local integrability. (`locallyIntegrable_comp_isometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L87)).

**Isometry preserves a spatial integral.** Proved result. Under the declaration's hypotheses, precomposing a spatial integrand by the specified isometry leaves its Lebesgue integral unchanged. (`integral_comp_isometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L94)).

**Linear isometries commute with integrals.** Proved result. Under the declaration's hypotheses, applying the linear isometry to a Bochner integral gives the integral of its pointwise application. (`integral_isometry_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L99)).

**Transport a weak gradient by an isometry.** Proved result. Under the declaration's hypotheses, conjugating a vector field by the linear isometry and multiplying by a scalar transports its weak gradient by the same scalar and isometry on its input and output. (`weakGradient_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L103)).

**Weak gradients inherit reflection signs.** Proved result. Under the declaration's hypotheses, almost everywhere, a coordinate column of the gradient at the reflected point is the reflected original column multiplied by the field symmetry sign and that coordinate's reflection sign. (`ae_flip_gradient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L177)).

**Reflection symmetry holds in spacetime.** Proved result. Under the declaration's hypotheses, almost everywhere in spacetime, the field at the reflected point equals the signed reflection of its original value. (`ae_joint_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L197)).

**Null sets lift to shifted orbits.** Proved result. Under the declaration's hypotheses, an almost-everywhere spacetime property remains valid for almost every time shift and rotation of almost every base point. (`ae_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L223)).

**Column identities determine reflection.** Proved result. Under the declaration's hypotheses, the stated reflection identities on coordinate columns imply reflection of the full linear map on every vector. (`grad_of_columns`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L228)).

**Coordinate identities fix the Hessian.** Proved result. Under the declaration's hypotheses, the stated coordinate reflection identities imply reflection of the full bilinear second derivative. (`secondDeriv_of_columns`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L236)).

**One reflection sign for velocity modes.** Proved result. Under the declaration's hypotheses, reflecting the spatial point and angular frequency multiplies each velocity-mode component by its coordinate reflection sign. (`modeVel_flip_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L259)).

**Two reflection signs for gradient modes.** Proved result. Under the declaration's hypotheses, reflecting the spatial point and angular frequency multiplies each gradient-mode entry by the product of its two coordinate reflection signs. (`modeGrad_flip_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L290)).

**Three reflection signs for Hessian modes.** Proved result. Under the declaration's hypotheses, reflecting the spatial point and angular frequency multiplies each Hessian-mode entry by the product of its three coordinate reflection signs. (`modeSecondDeriv_flip_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeFlip.lean#L329)).
<!-- /passage:front -->

