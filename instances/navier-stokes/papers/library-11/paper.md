
<!-- passage:front -->
# Library guide 11: Breakdown/CertCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) **11** [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.CertCell.ModeHeightDerivative` to `Breakdown.CertCell.ShapeJetVanish` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.CertCell.ModeHeightDerivative

Represent mode coefficients as orbit averages and derive their weak height derivatives. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The cosine frame coefficients.** Definition. Collect the coordinate projections multiplying the cosine component of the frame. (`rotCoeff0`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L15)).

**The sine frame coefficients.** Definition. Collect the signed coordinate projections multiplying the sine component of the frame. (`rotCoeff1`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L17)).

**The axial frame coefficients.** Definition. Keep only the axial coordinate projection. (`rotCoeff2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L19)).

**A frame-coordinate functional.** Definition. Combine the planar cosine and sine coefficients with the axial projection. (`frameCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L21)).

**Frame functional is smooth.** Proved result. The moving-frame functional is smooth. (`frameCoord_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L23)).

**The frame map reads inverse rotation.** Proved result. On a cosine-sine pair, the frame-coordinate functional reads a component after inverse axial rotation. (`frameCoord_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L26)).

**Rotating a plane point is cylindrical.** Proved result. Axial rotation of the embedded half-plane point gives the cylindrical point with the same radius and height. (`axialRot_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L32)).

**Rotate the first unit vector radially.** Proved result. The first coordinate unit vector rotates to the radial unit vector at the given angle. (`axialRot_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L36)).

**Axial rotation fixes the axial vector.** Proved result. Axial rotation leaves the third coordinate unit vector unchanged. (`axialRot_third`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L40)).

**Normalize the angular orbit average.** Proved result. Under the declaration's hypotheses, the mode average equals the corresponding time-angle wave average divided by 2π. (`mode_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L46)).

**Represent a velocity mode by an average.** Proved result. The plane velocity mode equals the moving-frame wave average divided by 2π. (`vel_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L63)).

**Represent the height-gradient mode.** Proved result. The axial gradient mode equals the orbit average of the axial evaluator divided by 2π. (`gradz_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L68)).

**Represent the radial-gradient mode.** Proved result. The radial gradient mode equals the orbit average of the radial evaluator divided by 2π. (`gradr_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L75)).

**Represent the second height derivative.** Proved result. The height-height second-derivative mode is the twice-axial orbit average divided by 2π. (`secondDerivzz_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L82)).

**Represent the mixed radial-height mode.** Proved result. The mixed radial-height second-derivative mode is the corresponding mixed evaluator average divided by 2π. (`secondDerivrz_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L89)).

**Expand a vector in the coordinate basis.** Proved result. Every spatial vector equals the sum of its coordinate multiples of the standard basis vectors. (`vec_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L97)).

**Bound an operator by its columns.** Proved result. The operator norm is at most the sum of the norms of its coordinate columns. (`opNorm_le_cols`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L101)).

**Norms preserve local integrability.** Proved result. Under the declaration's hypotheses, the norm of a locally integrable vector-valued field is locally integrable. (`loc_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L113)).

**Operator columns are locally integrable.** Proved result. Under the declaration's hypotheses, applying a locally integrable operator-valued field to a fixed coordinate unit vector gives a locally integrable field. (`col_loc`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L117)).

**Swap inputs of integrable bilinear maps.** Proved result. Under the declaration's hypotheses, an almost everywhere measurable bilinear field is locally integrable if fixing each coordinate unit vector in its second input gives a locally integrable linear-map field. (`flip_loc`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L123)).

**Weak derivative of the gradient field.** Proved result. Under the declaration's hypotheses, pairing a directional test derivative with the gradient field equals minus pairing the test with the Hessian in that coordinate direction. (`grad_weak_op`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L132)).

**Scale a weak derivative identity.** Proved result. Under the declaration's hypotheses, multiplying both field entries by the same constant preserves the stated weak derivative pairing. (`scale_id`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L155)).

**Mixed smooth derivatives commute.** Proved result. For a smooth scalar test, differentiating in the two constant directions commutes. (`mixed_partial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L164)).

**Derivatives remain admissible tests.** Proved result. Under the declaration's hypotheses, a directional derivative of a smooth compactly supported plane test is smooth, compactly supported and supported at positive radius. (`deriv_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L175)).

**Weak height derivatives on a.e. slices.** Proved result. For an admissible perturbation and almost every positive radius, the plane velocity and gradient modes have the corresponding gradient and Hessian modes as weak height derivatives on every bounded symmetric height interval. (`modeHeightDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightDerivative.lean#L185)).

### Breakdown.CertCell.ModeHeightLineSlice

Use a countable dense family of line tests to obtain weak height derivatives on almost every radial slice. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A symmetric bounded line interval.** Definition. Use the closed interval from minus N to N for the line approximation. (`seg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L12)).

**Order the symmetric interval endpoints.** Proved result. For a natural number, its negative as a real number is at most its positive value. (`seg_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L14)).

**Smooth supported height tests.** Definition. Collect smooth height tests whose support lies in the selected bounded interval. (`lineTests`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L16)).

**A height test and its derivative.** Definition. Package the restricted test and derivative as a pair of continuous functions. (`lineData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L18)).

**Weak height-derivative pairing.** Definition. Integrate the test derivative against the field and the test against its proposed height derivative. (`linePair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L22)).

**Clamped interval tests lift continuously.** Proved result. Composing a continuous interval test with the clamp to the symmetric exhaustion interval and embedding it into the complex numbers gives a continuous line function. (`lift_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L26)).

**Height pairing is continuous.** Proved result. Under the hypotheses of this declaration, the weak height pairing is continuous. (`linePair_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L30)).

**Rectangle measure is a product measure.** Proved result. Restricting planar volume to a product set equals the product of the restricted line measures. (`rect_restrict`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L69)).

**Compact positive sets avoid zero.** Proved result. Under the declaration's hypotheses, every compact subset of the positive real axis lies in a closed interval whose lower endpoint is strictly positive. (`compact_in_Ioi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L73)).

**Differentiate a separated height test.** Proved result. Under the declaration's hypotheses, the height derivative of a product test differentiates only its height factor. (`fderiv_prod_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L81)).

**Tests vanish outside their segment.** Proved result. Under the declaration's hypotheses, outside an interval containing the topological support of a line test, both the test and its derivative vanish. (`zero_off_seg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L93)).

**The height defect vanishes a.e..** Proved result. Under the declaration's hypotheses, the plane weak derivative identity makes the selected line-test defect zero for almost every positive radius. (`ae_line_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L97)).

**Local integrability on most height lines.** Proved result. Under the declaration's hypotheses, almost every radial slice is integrable on every stated bounded height interval. (`ae_line_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L175)).

**Weak derivatives on most height lines.** Proved result. Under the declaration's hypotheses, a locally integrable plane weak height derivative restricts, for almost every positive radius, to a weak derivative on every symmetric finite height interval. (`slice_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightLineSlice.lean#L183)).

### Breakdown.CertCell.ModeHeightOrbitAverage

Build the time-angle orbit averages and justify the weak radial and height identities under the integrals. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A planar radial direction.** Definition. Embed a planar pair as a vector with zero axial coordinate. (`unitAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L18)).

**Expand the planar radial vector.** Proved result. The planar radial vector is the linear combination of the first two unit vectors with the planar coordinates as coefficients. (`unitAt_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L20)).

**Radial vector is continuous.** Proved result. The planar radial vector is continuous. (`unitAt_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L25)).

**Read a radial derivative component.** Definition. Compose the output functional with evaluation on the planar radial direction. (`radialL`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L31)).

**Read an axial derivative component.** Definition. Compose the output functional with evaluation on the axial unit vector. (`axialL`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L34)).

**Radial evaluator is continuous.** Proved result. Under the hypotheses of this declaration, the radial evaluation functional is continuous. (`radialL_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L37)).

**Axial evaluator is continuous.** Proved result. Under the hypotheses of this declaration, the axial evaluation functional is continuous. (`axialL_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L40)).

**The angular mode average.** Definition. Integrate the chosen moving-frame component against the angular Fourier factor. (`wave`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L43)).

**The temporal Fourier exponential.** Definition. Use the negative exponential at the chosen integer temporal frequency. (`timeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L47)).

**The time-angle mode average.** Definition. Integrate the angular average against the temporal Fourier factor over one period. (`waveAvg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L49)).

**Time-cell-angle product measure.** Definition. Use the product of a time period, a cell rectangle and one angular period. (`boxM`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L52)).

**A point on the time-rotation orbit.** Definition. Send time, radius, height and angle to the corresponding spacetime point. (`orbitPt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L56)).

**Orbit point is measurable.** Proved result. The orbit spacetime point is measurable. (`orbitPt_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L58)).

**The orbit box is restricted volume.** Proved result. The time-cell-angle product measure equals full product volume restricted to the corresponding product box. (`boxM_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L64)).

**Bound an unweighted cylindrical integral.** Proved result. Under the declaration's hypotheses, on a radial interval starting at a positive radius, the cylindrical orbit integral is bounded by the one-period spacetime integral divided by that lower radius. (`cyl_lint_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L70)).

**Orbit coordinates preserve null sets.** Proved result. Under the declaration's hypotheses, the spacetime orbit map pulls null sets back to null sets for the restricted time-cell-angle measure. (`orbit_qmp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L99)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`cylPoint_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L117)).

**The angular phase has period two pi.** Proved result. Adding two pi to angle leaves the negative integer-frequency angular exponential unchanged. (`phase_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L120)).

**The angular averaging integrand.** Definition. Multiply the orbit component by its angular Fourier exponential. (`waveKer`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L125)).

**Angular average on a symmetric interval.** Proved result. Under the declaration's hypotheses, the angular orbit average equals the integral of its orbit kernel over angles between minus pi and pi. (`wave_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L129)).

**circle evaluator is uniformly bounded.** Proved result. Under the declaration's hypotheses, a continuous family of linear evaluators has a common nonnegative operator-norm bound when restricted to the unit circle. (`ker_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L138)).

**Bound points over a positive rectangle.** Proved result. Under the declaration's hypotheses, the norm of a cylindrical point above the rectangle is at most twice the upper radius plus the absolute values of its two height endpoints. (`norm_cyl_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L146)).

**Integrability on cylindrical orbit boxes.** Proved result. Under the declaration's hypotheses, the field evaluated on the cylindrical spacetime orbit is integrable over each bounded time-angle-radius-height box separated from the axis. (`orbit_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L159)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`norm_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L194)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`norm_timeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L198)).

**Temporal phase is continuous.** Proved result. The temporal Fourier factor is continuous. (`timeFactor_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L203)).

**Angular averages integrate on boxes.** Proved result. Under the declaration's hypotheses, the angular orbit average is integrable over one time period and the bounded positive-radius plane rectangle. (`wave_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L207)).

**Time average of angular coefficients.** Proved result. Under the declaration's hypotheses, the time-angle average is the integral over one time period of the angular average multiplied by the temporal Fourier factor. (`waveAvg_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L230)).

**Time-angle averages integrate on cells.** Proved result. Under the declaration's hypotheses, the time-angle orbit average is integrable on the bounded plane rectangle separated from the axis. (`waveAvg_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L234)).

**Interchange a test pairing and time.** Proved result. Under the declaration's hypotheses, pairing a plane test with the time-angle average equals the temporal Fourier integral of its pairing with each angular average. (`avg_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L244)).

**Enclose a supported test in a rectangle.** Proved result. Under the declaration's hypotheses, a compactly supported plane test whose support has positive radius lies in a bounded rectangle separated from the axis. (`rect_of_tsupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L287)).

**Weak derivatives survive orbit averaging.** Proved result. Under the declaration's hypotheses, the radial and axial weak derivatives of the averaged field are the corresponding orbit averages of the derivative field evaluated in those directions. (`plane_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeHeightOrbitAverage.lean#L295)).

### Breakdown.CertCell.ModeOffLattice

Use the symmetry class to show that Fourier coefficients outside the allowed lattice vanish almost everywhere. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A rotation detects the zero vector.** Proved result. If every coordinate of a rotated complex vector is zero, the original vector is zero. (`rot_coeffs_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L23)).

**A.e. vanishing of weak gradients.** Proved result. Under the declaration's hypotheses, a weak gradient of a field that vanishes almost everywhere also vanishes almost everywhere. (`weak_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L40)).

**Zero real and imaginary parts imply zero.** Proved result. Under the declaration's hypotheses, a complex matrix whose real and imaginary parts both vanish is the zero matrix. (`grad_zero_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L54)).

**The real part of zero is zero.** Proved result. Taking coordinatewise real parts of the zero complex vector gives the zero real vector. (`reVec_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L63)).

**The imaginary part of zero is zero.** Proved result. Taking coordinatewise imaginary parts of the zero complex vector gives the zero real vector. (`imVec_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L66)).

**Axial rotations commute.** Proved result. Under the declaration's hypotheses, applying two rotations around the same axis gives the same point in either order. (`rot_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L69)).

**Velocity integrability on an orbit.** Proved result. Under the declaration's hypotheses, the velocity pulled back to a fixed orbit is integrable over the unit time interval crossed with the full angular period. (`orbit_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L73)).

**Symmetry shifts rotate velocity modes.** Proved result. Under the imposed time-rotation symmetry, shifting base time and rotating the spatial point rotates the velocity-mode vector by the same axial rotation. (`shifted_mode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L89)).

**A nontrivial symmetry phase kills a mode.** Proved result. Under the declaration's hypotheses, a velocity mode vanishes almost everywhere if the field is invariant under a time-rotation symmetry whose Fourier phase at that mode is not one. (`velocity_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L150)).

**Nontrivial symmetry phases kill modes.** Proved result. For an admissible perturbation, a time-rotation symmetry whose frequency phase is not one forces its velocity, gradient and Hessian modes to vanish almost everywhere in spacetime. (`modeOffLattice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeOffLattice.lean#L180)).

### Breakdown.CertCell.ModePlaneDerivatives

Identify the first and second plane derivatives of Fourier modes through smooth tensor-coordinate evaluators. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Rotation from planar coordinates.** Definition. Express axial rotation using a planar cosine-sine pair. (`rotAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L16)).

**Planar coordinates for axial rotation.** Proved result. The planar-coordinate rotation formula agrees with axial rotation on a cosine-sine pair. (`rotAt_angle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L19)).

**Planar rotation is smooth.** Proved result. The rotation written in planar coordinates is smooth. (`rotAt_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L21)).

**A gradient-coordinate functional.** Definition. Read a gradient entry with rotated input and output frame directions. (`gradEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L25)).

**A Hessian-coordinate functional.** Definition. Read a second-derivative entry with the chosen rotated frame directions. (`slopeEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L28)).

**Gradient evaluator is smooth.** Proved result. The gradient Fourier evaluator is smooth. (`gradEval_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L31)).

**Hessian evaluator is smooth.** Proved result. The second-derivative Fourier evaluator is smooth. (`slopeEval_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L34)).

**Gradient modes are evaluator averages.** Proved result. A plane gradient-mode entry is the corresponding moving-frame evaluator average divided by 2π. (`grad_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L38)).

**Hessian modes are evaluator averages.** Proved result. A plane second-derivative entry is the corresponding tensor evaluator average divided by 2π, with the stated input order. (`slope_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L45)).

**The mixed mode uses the axial evaluator.** Proved result. The mixed height-radial second derivative is the axial average of the radial-column evaluator divided by 2π. (`mixed_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L53)).

**Almost every slice has a weak gradient.** Proved result. For almost every time, the velocity and the coordinate columns of its gradient are locally integrable and satisfy the spatial weak derivative identities. (`first_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L60)).

**Almost every slice has a weak Hessian.** Proved result. For almost every time, the gradient and the coordinate contractions of its Hessian are locally integrable and satisfy the spatial weak derivative identities. (`second_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L70)).

**Restrict a supported test pairing.** Proved result. Under the declaration's hypotheses, the cell integral of a coefficient times a supported test equals its whole-plane pairing with the factors reversed. (`rect_swap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L81)).

**Restrict a weak identity to a rectangle.** Proved result. Under the declaration's hypotheses, the rectangle pairing of the first coefficient with the derivative test equals minus the rectangle pairing of the derivative coefficient with the original test. (`rect_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L86)).

**Weak plane derivatives of velocity modes.** Proved result. Under the hypotheses of this declaration, velocity modes have radial, axial and mixed weak derivatives given by the matching gradient and Hessian modes on rectangles away from the axis, where the gradient and Hessian modes are integrable. (`modePlaneDerivs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModePlaneDerivatives.lean#L97)).

### Breakdown.CertCell.ModeRadialDerivative

Pass from plane weak identities to radial weak derivatives on almost every height slice. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Smooth supported radial tests.** Definition. Collect smooth radial tests supported in the selected closed interval. (`rayTests`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L15)).

**A radial test and its derivative.** Definition. Package the restricted radial test and derivative as continuous functions. (`rayData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L17)).

**Weak radial-derivative pairing.** Definition. Integrate the radial test derivative against the field and the test against its proposed derivative. (`rayPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L21)).

**Clamped radial tests are continuous.** Proved result. Under the declaration's hypotheses, a continuous interval test composed with clamping to its radial interval remains continuous when viewed as a complex-valued line function. (`ray_lift_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L24)).

**Radial pairing is continuous.** Proved result. Under the hypotheses of this declaration, the weak radial pairing is continuous. (`rayPair_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L28)).

**Differentiate a separated radial test.** Proved result. Under the declaration's hypotheses, the radial derivative of a product test differentiates only its radial factor. (`ray_deriv_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L70)).

**weak radial defect vanishes on most rays.** Proved result. Under the declaration's hypotheses, the plane weak radial derivative identity makes every selected ray-test defect zero for almost every height. (`ae_ray_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L82)).

**Positive exhaustion endpoint.** Definition. Set the inner radius to 1 divided by N plus 1. (`lowEnd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L174)).

**Outer exhaustion endpoint.** Definition. Set the outer radius to N plus 1. (`highEnd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L176)).

**The radial exhaustion starts above zero.** Proved result. Every lower endpoint in the radial exhaustion is strictly positive. (`lowEnd_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L178)).

**radial exhaustion endpoints are ordered.** Proved result. Each lower endpoint of the radial exhaustion is at most its upper endpoint. (`band_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L182)).

**Local integrability on most radial rays.** Proved result. Under the declaration's hypotheses, almost every height slice is integrable on each positive-radius exhaustion interval. (`ae_ray_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L187)).

**Weak derivatives on most radial rays.** Proved result. Under the declaration's hypotheses, a locally integrable plane weak radial derivative restricts, for almost every height, to a weak derivative on every nonempty compact interval of positive radii. (`ray_slice_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L195)).

**Planar frame columns.** Definition. Store the first two coordinate vectors and a zero third column. (`planeCol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L269)).

**Quarter-turn frame columns.** Definition. Store the signed quarter-turn of the two planar coordinate vectors. (`turnCol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L271)).

**The axial frame column.** Definition. Store the axial unit vector in the third column only. (`axisCol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L273)).

**A moving input direction.** Definition. Combine the planar, quarter-turn and axial columns with a planar pair. (`dirAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L275)).

**Moving direction is smooth.** Proved result. The moving input direction is smooth. (`dirAt_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L277)).

**Circle directions as rotated vectors.** Proved result. The direction assigned to a coordinate index on the unit circle is the corresponding coordinate unit vector rotated by the circle angle. (`dirAt_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L280)).

**The first moving column is radial.** Proved result. The first moving input direction equals the planar radial vector. (`dirAt_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L284)).

**Read a moving derivative column.** Definition. Apply a derivative to the moving direction, then read its chosen output coordinate. (`columnMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L288)).

**Column evaluator is smooth.** Proved result. Under the hypotheses of this declaration, the moving-column functional is smooth. (`columnMap_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L291)).

**Represent a gradient column by averaging.** Proved result. The gradient mode equals the corresponding moving-column average divided by 2π. (`grad_col_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L296)).

**Represent a radial Hessian column.** Proved result. The radial second-derivative mode equals the radial derivative-column average divided by 2π. (`second_col_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L303)).

**Weak radial derivatives on most rays.** Proved result. Under the hypotheses of this declaration, for almost every height, velocity and gradient modes have matching gradient and Hessian modes as weak radial derivatives on every bounded interval with positive lower radius. (`modeRadialDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRadialDerivative.lean#L314)).

### Breakdown.CertCell.ModeRotationNorms

Show that the relevant mode norms and curl expressions transform correctly under orthogonal axial rotation. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**axial rotation matrix has planar form.** Proved result. The axial rotation acts by the usual cosine-sine matrix on the first two coordinates and leaves the third coordinate fixed. (`rot_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L19)).

**Rotation matrix columns are orthonormal.** Proved result. The dot product of two columns of the axial rotation matrix is one when their indices agree and zero otherwise. (`rot_col_orth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L24)).

**Rotation matrix rows are orthonormal.** Proved result. The dot product of two rows of the axial rotation matrix is one when their indices agree and zero otherwise. (`rot_row_orth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L29)).

**The alternating tensor respects rotation.** Proved result. Contracting the alternating symbol with inverse and forward rotation entries transforms it by the forward rotation on its remaining index. (`alt_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L34)).

**Complex norms under orthogonal maps.** Proved result. Under the declaration's hypotheses, multiplication by a real orthogonal matrix preserves the sum of squared absolute values of complex coordinates. (`cnormSq_orth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L42)).

**Rotate a third-order tensor.** Definition. Rotate the output coordinate and both input coordinates of a complex tensor. (`rotTensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L65)).

**Rotated averages gain angular phases.** Proved result. Under the declaration's hypotheses, the rotated mode average is the matrix transform of the original averages multiplied by the positive angular-frequency phase. (`modeAverage_rotate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L69)).

**Integrability of frame Hessian entries.** Proved result. Under the declaration's hypotheses, each Hessian entry pulled back along the spacetime orbit and expressed in the rotating frame is integrable on the time-angle box. (`integrable_secondDerivComponent`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L95)).

**Evaluate a weighted vector sum.** Proved result. A coordinate of a doubly indexed weighted vector sum equals the sum of the same weights times that coordinate of each vector. (`coord_sum3`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L123)).

**Rotate a Hessian mode and its phase.** Proved result. Under the declaration's hypotheses, rotating the spatial point multiplies the Hessian Fourier mode by its positive angular phase and rotates all three tensor indices. (`modeSecondDeriv_rotation_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L127)).

**Tensor products preserve orthogonality.** Proved result. Under the declaration's hypotheses, the tensor-product columns formed from two orthogonal matrices are orthonormal under the product index sum. (`orth_prod`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L167)).

**Unit phases preserve square norms.** Proved result. Under the declaration's hypotheses, multiplying every entry by the same complex number of norm one preserves the sum of squared entry norms. (`cnormSq_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L180)).

**Vector rotation preserves square norms.** Proved result. Rotating a complex vector preserves the sum of squared coordinate norms. (`cnormSq_rotC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L185)).

**Matrix rotation preserves square norms.** Proved result. Rotating both indices of a complex matrix preserves its sum of squared entry norms. (`cnormSq_rotCMat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L188)).

**Tensor rotation preserves square norms.** Proved result. Under the declaration's hypotheses, rotating the three tensor indices preserves the sum of squared entry norms. (`cnormSq_rotTensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L201)).

**A common phase passes through curl.** Proved result. Multiplying all gradient entries by a common phase multiplies their curl by the same phase. (`curlOfGrad_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L220)).

**Phase scaling of the vorticity gradient.** Proved result. Under the declaration's hypotheses, multiplying all Hessian entries by a common phase multiplies the resulting vorticity gradient by that phase. (`curlGradOfSecondDeriv_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L228)).

**Curl commutes with coordinate rotation.** Proved result. The curl extracted from a rotated gradient matrix is the rotated curl of the original matrix. (`curlOfGrad_rotCMat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L236)).

**Rotate Hessians and vorticity gradients.** Proved result. Under the declaration's hypotheses, the vorticity gradient extracted from a rotated Hessian is the corresponding rotated matrix. (`curlGradOfSecondDeriv_rotTensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L255)).

**A Hessian mode gains a temporal phase.** Proved result. Under the declaration's hypotheses, the Hessian mode at base time sigma is its time-zero mode multiplied by the exponential of i times two pi times its temporal frequency times sigma. (`modeSecondDeriv_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L276)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`norm_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeRotationNorms.lean#L287)).

### Breakdown.CertCell.ModeShiftRotate

Compute the phase acquired by a velocity mode under time translation. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The phase of a backward time shift.** Proved result. Replacing time tau by tau minus s multiplies the negative Fourier exponential by exp of i times two pi times the temporal frequency times s. (`expFactor_sub_time`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotate.lean#L19)).

**The Fourier phase has unit time period.** Proved result. The negative Fourier exponential at an integer temporal frequency is unchanged by adding one to time. (`expFactor_add_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotate.lean#L27)).

**Time shifts phase velocity modes.** Proved result. Under the declaration's hypotheses, a base-time shift multiplies every velocity-mode component by the positive temporal Fourier phase of the shift. (`modeVel_time_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotate.lean#L36)).

**Integrability for the orbit box measure.** Proved result. Under the declaration's hypotheses, the velocity evaluated at shifted time and rotated position is integrable for the time-angle product measure. (`integrable_box_of_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotate.lean#L75)).

### Breakdown.CertCell.ModeShiftRotateTensor

Extend time and rotation transport to gradient and second-derivative modes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`axialRot_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L19)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`axialRot_neg_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L25)).

**Rotation is matrix multiplication.** Proved result. Each coordinate of a rotated vector is the sum of its original coordinates weighted by the corresponding rotation-matrix row. (`axialRot_component_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L34)).

**Axial rotation is continuous.** Proved result. For each fixed vector v and Cartesian component, the corresponding component of its rotation through θ about the axis is continuous in θ. (`continuous_axialRot_component`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L41)).

**Change the angle of a rotated basis.** Proved result. A coordinate vector rotated by one angle expands in the basis rotated by the sum of two angles using the intermediate rotation coefficients. (`axialRot_unit_recombine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L51)).

**Split an inverse axial rotation.** Proved result. Rotation by minus psi equals rotation by phi after rotation by minus the sum of psi and phi. (`axialRot_neg_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L62)).

**Compensate a time-angle phase shift.** Proved result. The original negative Fourier phase is the shifted negative phase multiplied by the positive phase of the time-angle shift. (`phase_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L68)).

**time-angle phase has unit time period.** Proved result. Adding one to the time coordinate preserves the negative time-angle Fourier phase. (`phase_time_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L77)).

**time-angle phase has full angular period.** Proved result. Adding two pi to the angular coordinate preserves the negative time-angle Fourier phase. (`phase_angle_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L87)).

**Translate a Fourier average by its phase.** Proved result. Under the declaration's hypotheses, translating a periodic component function in time and angle multiplies its mode average by the positive Fourier phase of the translation. (`modeAverage_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L97)).

**Time-angle integral as a rectangle.** Proved result. Under the declaration's hypotheses, the iterated integrals over a unit time interval and a full angular period equal the integral over their closed product rectangle. (`iterated_eq_set`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L128)).

**Fourier averaging commutes with matrices.** Proved result. Under the declaration's hypotheses, the mode average of a fixed real linear combination of components is the same linear combination of their mode averages. (`modeAverage_linear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L141)).

**Integrability of rotated box entries.** Proved result. Under the declaration's hypotheses, a coordinate of an integrable vector field rotated by the negative angular variable is integrable on the time-angle rectangle. (`rotated_component_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L188)).

**Change frame in both gradient indices.** Proved result. A gradient entry in one rotated frame is the sum of entries in the shifted frame weighted by rotation factors for its output and input indices. (`grad_pointwise`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L205)).

**Change frame in all Hessian indices.** Proved result. A Hessian entry in one rotated frame is the sum of entries in the shifted frame weighted by rotation factors for its output and two input indices. (`secondDeriv_pointwise`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L214)).

**Tensor modes follow shifts and rotations.** Proved result. Gradient and second-derivative modes transform with the stated phase and tensor rotation. (`modeShiftRotateTensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeShiftRotateTensor.lean#L230)).

### Breakdown.CertCell.ModeTermFlip

Track reflection through weights, label sums and tensor norms in a mode-energy term. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Coordinate signs describe the reflection.** Proved result. The spatial reflection preserves coordinate zero and negates coordinates one and two. (`flipPoint_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L15)).

**A reflection sign squares to one.** Proved result. Multiplying the coordinate reflection sign by itself gives one. (`frameSign_mul_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L18)).

**Reflection signs have absolute value one.** Proved result. Every coordinate reflection sign has absolute value one. (`abs_frameSign`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L21)).

**Spatial reflection is an involution.** Proved result. Applying the spatial reflection twice returns the original point. (`flipPoint_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L24)).

**Reflection as a linear map.** Definition. Package the spatial reflection as a real linear map. (`flipLinearMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L28)).

**Reflection preserves the spatial norm.** Proved result. The spatial reflection preserves the Euclidean norm. (`norm_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L39)).

**Reflection as a linear isometry.** Definition. Package the involutive spatial reflection as a linear isometric equivalence. (`flipIsometryEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L45)).

**reflection equivalence acts pointwise.** Proved result. The packaged isometric reflection sends each spatial point to the coordinate reflection used in the mode formulas. (`flipIsometryEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L49)).

**The reflected scalar field is a pullback.** Proved result. Under the declaration's hypotheses, the reflected scalar field is the original scalar field composed with the reflection isometry. (`comp_flip_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L51)).

**Reflect the Hessian norm weight.** Proved result. Under the declaration's hypotheses, the Hessian norm weight of a field at the reflected point equals the Hessian norm weight of its reflected pullback at the original point. (`secondDerivNorm_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L55)).

**Reflection transports gradient weights.** Proved result. Under the declaration's hypotheses, the gradient weight of a field at the reflected point equals the gradient weight of its reflected pullback at the original point. (`wtGrad_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L62)).

**Label reflection is an involution.** Proved result. Reflecting the Fourier label twice returns the original label. (`flipLabel_flipLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L70)).

**Label reflection commutes with negation.** Proved result. Reflecting a negated Fourier label gives the negation of its reflected label. (`flipLabel_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L73)).

**Label reflection preserves addition.** Proved result. Reflecting a sum of Fourier labels gives the sum of their reflected labels. (`flipLabel_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L76)).

**Label reflection preserves subtraction.** Proved result. Reflecting a difference of Fourier labels gives the difference of their reflected labels. (`flipLabel_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L80)).

**Reflection of labels is injective.** Proved result. Two Fourier labels with the same reflection are equal. (`flipLabel_injective`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L84)).

**Reflect membership together with its set.** Proved result. A reflected Fourier label belongs to the reflected frequency set exactly when the original label belongs to the original set. (`mem_flip_image`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L87)).

**Reflection preserves piece membership.** Proved result. A reflected label belongs to the reflected harmonic piece exactly when the original label belongs to the original piece. (`inPiece_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L90)).

**Frame frequency under paired reversals.** Proved result. Negating the angular frame parameter and reversing the angular mode label together preserve the moving-frame frequency. (`frameFreq_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L95)).

**Reflect backward interaction sums.** Proved result. Under the declaration's hypotheses, reflecting the frequency set, target label and spatial point preserves the backward interaction-weight sum. (`backSum_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L99)).

**Reflect forward interaction sums.** Proved result. Under the declaration's hypotheses, reflecting the frequency set, target label and spatial point preserves the forward interaction-weight sum. (`fwdSum_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L108)).

**Reflection preserves the inward weight.** Proved result. Under the declaration's hypotheses, reflecting the frequency set, target label and point preserves the inward interaction weight. (`inward_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L117)).

**Reflection preserves the outward weight.** Proved result. Under the declaration's hypotheses, reflecting the frequency set, target label and point preserves the outward interaction weight. (`outward_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L125)).

**Reflection invariance of harmonic sums.** Proved result. Under the declaration's hypotheses, the harmonic amplitude sum has the same value at a point and its spatial reflection. (`harmonicSum_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L133)).

**Coordinate signs preserve square norms.** Proved result. Under the declaration's hypotheses, multiplying each coordinate by a real sign of absolute value one preserves the sum of squared norms. (`cnormSq_sign_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L141)).

**Curl inherits the reflection signs.** Proved result. Applying the prescribed pair of reflection signs to gradient entries gives the corresponding single sign on each curl component. (`curlOfGrad_sign`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L147)).

**Vorticity gradients inherit frame signs.** Proved result. Under the declaration's hypotheses, applying the three reflection signs to Hessian entries gives the corresponding pair of signs on the vorticity-gradient entries. (`curlGradOfSecondDeriv_sign`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ModeTermFlip.lean#L154)).

### Breakdown.CertCell.OwnSolidOrbit

Relate a cell rectangle and its rotated solid while discarding only null boundaries. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Coordinates of a rotated plane point.** Proved result. The rotated plane point has planar coordinates radius times cosine and sine, while its height stays fixed. (`orbit_coords`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/OwnSolidOrbit.lean#L17)).

**An orbit keeps the radial coordinate.** Proved result. Under the declaration's hypotheses, the cylindrical radius of the rotated half-plane point is its original nonnegative radius. (`orbit_radius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/OwnSolidOrbit.lean#L22)).

**Solid membership from planar coordinates.** Proved result. Under the declaration's hypotheses, a cylindrical orbit point belongs to the cell solid exactly when its radial-height point belongs to the cell rectangle. (`orbit_mem_solid_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/OwnSolidOrbit.lean#L29)).

**Cell orbits lie in the owned solid.** Proved result. Under the declaration's hypotheses, the rotated point belongs to the solid region owned by the specified cell. (`orbit_mem_ownSolid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/OwnSolidOrbit.lean#L38)).

**Unique cell ownership almost everywhere.** Proved result. Under the declaration's hypotheses, almost every point of a valid mesh cell has positive radius and belongs to no other cell rectangle. (`ae_own_point`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/OwnSolidOrbit.lean#L46)).

**Almost every point avoids the plane.** Proved result. The height coordinate is nonzero almost everywhere for the measure specified in this declaration. (`ae_off_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/OwnSolidOrbit.lean#L70)).

**An orbit keeps the height coordinate.** Proved result. The height of the rotated half-plane point is its original height. (`orbit_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/OwnSolidOrbit.lean#L80)).

### Breakdown.CertCell.PairingModeIdentity

Recover the real gradient pairing from square-summable Fourier mode pairings by polarization. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Square of a complex matrix difference.** Proved result. The squared entry norm of a complex matrix difference is the sum of their squared norms minus twice the real Hermitian pairing. (`cnormSq_mat_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L23)).

**The square of a real gradient difference.** Proved result. The squared-column norm of a gradient difference is the sum of their squared norms minus twice their real matrix pairing. (`matSq_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L30)).

**Gradient square is nonnegative.** Proved result. The sum of squared norms of the columns of a gradient matrix is nonnegative. (`matSq_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L38)).

**Bound a gradient difference by energies.** Proved result. The squared-column norm of a gradient difference is at most twice the sum of the two squared-column norms. (`matSq_sub_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L41)).

**Mode square norm is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the sum of squared complex entry norms is almost everywhere strongly measurable for the stated measure. (`aestronglyMeasurable_cnormSq_mat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L50)).

**Gradient square norm is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the sum of squared matrix-column norms is almost everywhere strongly measurable for the stated measure. (`aestronglyMeasurable_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L56)).

**Gradient-mode energy is slab integrable.** Proved result. Under the declaration's hypotheses, the squared entry norm of a gradient mode is integrable on the one-period spacetime slab. (`integrable_cnormSq_modeGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L63)).

**Parseval for gradient energy.** Proved result. Under the declaration's hypotheses, the sum of the slab integrals of squared gradient-mode norms equals the real value of the one-period gradient energy integral. (`hasSum_cnormSq_modeGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L78)).

**Local integrability from gradient energy.** Proved result. Under the declaration's hypotheses, the gradient field is locally integrable in spacetime under the assumed local bound on its squared-column norm. (`locallyIntegrable_of_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L97)).

**Gradient mode subtraction a.e..** Proved result. Under the declaration's hypotheses, at almost every slab point, the Fourier modes of a gradient difference are the differences of the gradient modes for every frequency. (`ae_modeGrad_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L108)).

**Matrix pairing equals its mode sum.** Proved result. The one-period spacetime pairing of almost everywhere measurable periodic matrix fields with finite square integrals equals the summable Fourier-mode pairing series. (`pairingModeIdentity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PairingModeIdentity.lean#L118)).

### Breakdown.CertCell.PatchCreditLinks

Transport the patch trace estimate into the quadratic credit inequality. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The upper axial trace is integrable.** Proved result. Under the declaration's hypotheses, the upper weak trace of the axial velocity mode is integrable over the selected closed radial interval. (`upperTrace_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchCreditLinks.lean#L16)).

**Weighted boundary terms are integrable.** Proved result. Under the declaration's hypotheses, the product of the radial coefficient, the boundary test value at height zero and radius is interval integrable between the radial endpoints. (`termwise_intervalIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchCreditLinks.lean#L50)).

**Finite test combinations are Lipschitz.** Proved result. Under the declaration's hypotheses, a finite complex combination of the admissible patch tests, using conjugated coefficients, has a global Lipschitz constant. (`combination_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchCreditLinks.lean#L59)).

**Patch credit uses the inverse Gram form.** Proved result. For the admissible patch, field and test data, a positive definite matrix bounding every reciprocal-weight test-gradient energy gives an inverse quadratic form on the patch traces bounded by the radius-weighted velocity-mode energy. (`patchCredit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchCreditLinks.lean#L80)).

### Breakdown.CertCell.PatchEntryLinks

Identify the trace map of a patch entry with its physical trace, so the local estimate applies to the stored data. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Pull a quadratic form through a real map.** Proved result. The real quadratic form of the pulled-back matrix equals the original quadratic form evaluated on the mapped complex vector. (`realQuad_pullback`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchEntryLinks.lean#L11)).

**Upper trace slices integrate in radius.** Proved result. Under the declaration's hypotheses, the weak upper endpoint trace of the field and its height derivative is integrable over the closed radial interval. (`trace_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchEntryLinks.lean#L26)).

**Finitely many segment endpoints are null.** Proved result. Almost every radial coordinate differs from every endpoint in the finite indexed family. (`ae_ne_all`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchEntryLinks.lean#L43)).

**Segment integrals add across a tiling.** Proved result. Under the declaration's hypotheses, the sum of integrals over consecutively tiled radial segments equals the integral over their full interval. (`sum_segments`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchEntryLinks.lean#L49)).

**Patch datum is an upper trace moment.** Proved result. Under the declaration's hypotheses, a patch datum equals the segment integral of the upper trace of the axial velocity mode against the segment test polynomial. (`data_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchEntryLinks.lean#L79)).

**stored trace map gives physical traces.** Proved result. Under the declaration's hypotheses, applying the stored real trace matrix to the physical patch data produces the patch traces against its test functions. (`trace_data`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchEntryLinks.lean#L107)).

**Patch data receive their trace credit.** Proved result. Under the hypotheses of this declaration, the trace-map evaluation on physical patch data satisfies the entry credit bound. (`patchEntryCredit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchEntryLinks.lean#L183)).

### Breakdown.CertCell.PatchModeWeak

Derive weak divergence and height identities for time-angle modes on a half-plane patch. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Rotate a plane point into a cylinder.** Proved result. Axially rotating the embedded radial-height point by an angle gives the cylindrical point with that radius, angle and height. (`rot_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L25)).

**Frame coordinates undo rotation.** Proved result. A cylindrical-frame coordinate of a vector is the corresponding coordinate after rotation by the negative frame angle. (`rot_frame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L29)).

**Rotation fixes the axial unit vector.** Proved result. Every rotation around the axis leaves the axial coordinate unit vector unchanged. (`rot_axial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L34)).

**Separate temporal and angular phases.** Proved result. The joint negative Fourier exponential factors into its temporal and angular exponentials. (`phase_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L38)).

**Velocity mode from time slices.** Proved result. A plane velocity mode equals the one-period temporal Fourier integral of the angular velocity mode of each time slice. (`planeVel_slices`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L47)).

**Height mode from time slices.** Proved result. The axial height-derivative mode equals the temporal Fourier integral of the axial-axial angular gradient mode. (`planeHeight_slices`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L61)).

**Null sets under cylindrical orbit maps.** Proved result. The map from radius-height-time-angle coordinates to spacetime pulls volume-null sets back to null sets. (`qmp_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L79)).

**A component averaged round an orbit.** Definition. Integrate a chosen field-component evaluator around one complete angular orbit. (`orbitMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L98)).

**A rectangle away from the axis.** Definition. Use a closed radial interval and a symmetric closed height interval. (`box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L101)).

**The orbit kernel is a.e. measurable.** Proved result. Under the declaration's hypotheses, applying the angular evaluator to the field on the cylindrical orbit gives an almost everywhere strongly measurable function of radius, height, time and angle. (`aesm_orbit_kernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L103)).

**Angular orbit modes are a.e. measurable.** Proved result. Under the declaration's hypotheses, the angular orbit-mode function is almost everywhere strongly measurable in its radial-height point and time. (`aesm_orbitMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L114)).

**Bound an orbit mode by the field norm.** Proved result. For a contractive evaluator, the norm of its angular orbit mode is at most the angular integral of the field norm. (`enorm_orbitMode_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L125)).

**Shift a nonnegative periodic integral.** Proved result. For a two-pi-periodic nonnegative function, its integral over the positive angular period equals its integral over the symmetric half-open period. (`lintegral_period_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L133)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`cyl_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L150)).

**The test box stays in the half-plane.** Proved result. Under the declaration's hypotheses, the box with positive inner radius is contained in the positive radial half-plane. (`box_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L153)).

**A cylindrical box fits in a ball.** Proved result. Under the declaration's hypotheses, the cylindrical image of the stated box lies in the closed ball of radius three times the box bound. (`cyl_mem_ball`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L156)).

**Bound a box orbit by a spatial ball.** Proved result. Under the declaration's hypotheses, the angular integral over a box separated from the axis is bounded by the spatial integral over the ball of three times the outer scale, divided by the lower radius. (`box_orbit_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L164)).

**Move a restriction into the product set.** Proved result. Restricting the second factor of a product measure equals restricting the product measure to the corresponding product set. (`prod_restrict_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L212)).

**Finite mass on bounded time slabs.** Proved result. Under the declaration's hypotheses, an almost everywhere strongly measurable and locally integrable spacetime field has a finite norm integral on one time period and any closed spatial ball. (`slab_lintegral_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L217)).

**Weighted orbit modes integrate in time.** Proved result. Under the declaration's hypotheses, the orbit mode multiplied by the compactly supported plane weight is integrable over the plane and one time period. (`integrable_orbitMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L232)).

**Gradient columns are locally integrable.** Proved result. Under the declaration's hypotheses, each coordinate column of the locally integrable gradient field is locally integrable in space. (`loc_col`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L292)).

**Weak derivative of a scalar component.** Proved result. Under the declaration's hypotheses, the directional weak derivative of the chosen scalar component is the matching coordinate of its gradient component. (`weak_scalar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L296)).

**The angular derivative frame correction.** Proved result. Under the declaration's hypotheses, at almost every point of positive radius, radius times the azimuthal diagonal gradient mode equals the imaginary angular frequency times the azimuthal velocity mode plus the radial velocity mode. (`slice_angular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L321)).

**Expand the radial unit vector.** Proved result. The radial unit vector is cosine times the first unit vector plus sine times the second. (`radial_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L344)).

**Expand the angular unit vector.** Proved result. The angular unit vector is minus sine times the first unit vector plus cosine times the second. (`angular_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L347)).

**The cylindrical frame preserves trace.** Proved result. The sum of diagonal entries of a gradient matrix in the cylindrical frame equals its Cartesian trace. (`frameMat_trace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L350)).

**Circle integrability almost everywhere.** Proved result. Under the declaration's hypotheses, a locally integrable spatial field is integrable along the full circle at almost every radial-height point of positive radius. (`ae_orbit_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L362)).

**Velocity Fourier evaluator.** Definition. Multiply a cylindrical velocity component by the angular Fourier exponential. (`velEvaluator`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L403)).

**Gradient Fourier evaluator.** Definition. Multiply a cylindrical gradient entry by the angular Fourier exponential. (`gradEvaluator`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L406)).

**The radial direction is a unit vector.** Proved result. The radial frame vector has norm one at every angle. (`norm_radialUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L409)).

**The angular direction is a unit vector.** Proved result. The azimuthal frame vector has norm one at every angle. (`norm_angularUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L413)).

**The axial direction is a unit vector.** Proved result. The axial coordinate vector has norm one. (`norm_axialUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L417)).

**Every frame vector has norm one.** Proved result. Each of the radial, angular and axial frame vectors has norm one. (`norm_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L421)).

**Continuity of all frame vectors.** Proved result. Each radial, angular or axial frame vector is continuous as a function of the frame angle. (`continuous_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L427)).

**Frame components as vector pairings.** Proved result. A frame coordinate equals the inner product with its radial, angular or axial unit vector. (`frameVec_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L438)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`phase_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L442)).

**Velocity evaluator is norm bounded.** Proved result. The velocity evaluator at any angle has absolute value at most the norm of its vector input. (`velEvaluator_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L446)).

**Gradient evaluator is norm bounded.** Proved result. The gradient evaluator at any angle has absolute value at most the operator norm of its matrix input. (`gradEvaluator_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L452)).

**The negative angular phase is continuous.** Proved result. The complex exponential of minus i times the angular frequency times angle is continuous in angle. (`phase_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L462)).

**Velocity evaluator is continuous.** Proved result. The velocity Fourier evaluator is continuous. (`velEvaluator_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L465)).

**Gradient evaluator is continuous.** Proved result. The gradient Fourier evaluator is continuous. (`gradEvaluator_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L471)).

**Velocity modes through orbit evaluators.** Proved result. An angular velocity coefficient is the normalized integral of its evaluator on the cylindrical orbit. (`modeVec_evaluator`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L478)).

**Gradient modes through orbit evaluators.** Proved result. An angular gradient coefficient is the normalized integral of its evaluator on the cylindrical orbit. (`gradMode_evaluator`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L482)).

**circle evaluator is interval integrable.** Proved result. Under the declaration's hypotheses, applying the continuous angular evaluator to the orbit field gives an interval-integrable function over a full angular period. (`ii_evaluator`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L486)).

**Trace-free gradients and their modes.** Proved result. If the gradient trace vanishes almost everywhere, the three diagonal angular gradient modes sum to zero at almost every positive-radius plane point. (`slice_trace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L494)).

**The radial coordinate functional.** Definition. Read the planar component in the direction specified by a planar pair. (`radialEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L518)).

**The axial coordinate functional.** Definition. Read the third coordinate, independently of the planar pair. (`axialEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L521)).

**Radial evaluator is smooth.** Proved result. The radial coordinate functional is smooth. (`radialEval_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L523)).

**Axial evaluator is smooth.** Proved result. The axial coordinate functional is smooth. (`axialEval_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L526)).

**radial evaluator reads radial velocity.** Proved result. On the unit circle, the radial functional equals the radial frame coordinate. (`radialEval_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L528)).

**The axial evaluator reads axial velocity.** Proved result. On the unit circle, the axial functional equals the axial frame coordinate. (`axialEval_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L531)).

**radial evaluator reads the radial entry.** Proved result. Applying the radial evaluator to the radial column of a matrix gives its radial-radial frame entry. (`radialEval_mat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L534)).

**axial evaluator reads the axial entry.** Proved result. Applying the axial evaluator to the axial matrix column gives its axial-axial frame entry. (`axialEval_mat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L539)).

**The angular period is nonzero.** Proved result. The complex value of 2π is nonzero. (`two_pi_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L544)).

**Circle pairing recovers a velocity mode.** Proved result. Under the declaration's hypotheses, the full-circle velocity pairing against the negative angular phase equals two pi times the selected angular velocity mode. (`circle_vel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L548)).

**Circle pairing recovers a gradient mode.** Proved result. Under the declaration's hypotheses, the full-circle derivative pairing against the negative angular phase equals two pi times the selected diagonal angular gradient mode. (`circle_grad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L556)).

**Scale a weak derivative identity.** Proved result. Under the declaration's hypotheses, multiplying both field entries by the same constant preserves the stated weak derivative pairing. (`scale_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L565)).

**Radial and axial weak mode derivatives.** Proved result. Under the declaration's hypotheses, the radial velocity mode has the radial-radial gradient mode as weak radial derivative, and the axial velocity mode has the axial-axial gradient mode as weak height derivative. (`slice_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L573)).

**Smooth radial weighting of tests.** Proved result. Under the declaration's hypotheses, multiplying a smooth plane test by its radial coordinate gives a smooth plane function. (`radial_weight_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L592)).

**Differentiate a radially weighted test.** Proved result. Under the declaration's hypotheses, the directional derivative of radius times a test is the radial direction component times the test plus radius times the test derivative. (`fderiv_radial_weight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L595)).

**Angular modes have zero weak divergence.** Proved result. Under the declaration's hypotheses, a divergence-free weak gradient gives a radius-weighted plane weak divergence identity with radial and axial test derivatives and the negative imaginary angular-frequency correction. (`slice_div`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L602)).

**Enclose a test away from the axis.** Proved result. Under the declaration's hypotheses, a compactly supported plane test whose support has positive radius vanishes outside a bounded box with positive lower radius. (`exists_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L659)).

**A continuous supported weight is bounded.** Proved result. Under the declaration's hypotheses, a continuous compactly supported complex weight admits a uniform bound on its norm. (`weight_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L672)).

**The temporal Fourier phase.** Definition. Use the negative temporal Fourier exponential over one unit time period. (`phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L676)).

**The normalized phase has norm ≤ 1/2π.** Proved result. The temporal phase multiplied by the averaging factor has norm at most one divided by 2π. (`phase_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L678)).

**Fourier phase is continuous.** Proved result. The complex Fourier phase is continuous. (`phase_cont'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L686)).

**Interchange time averages and pairings.** Proved result. Under the declaration's hypotheses, the weighted plane mode is integrable, its plane integral equals the temporal Fourier integral of the orbit pairing, and the required inner pairings are integrable for almost every time. (`swap_mode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L690)).

**Velocity modes as time orbit averages.** Proved result. A plane velocity mode is the temporal Fourier average of its normalized angular velocity orbit integral. (`planeVel_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L729)).

**Axial derivative as an orbit average.** Proved result. The axial height mode is the temporal Fourier average of its normalized angular gradient orbit integral. (`planeHeight_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L734)).

**Normalize the angular velocity average.** Proved result. The unnormalized velocity orbit average equals 2π times the local velocity mode. (`orbit_vel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L739)).

**Normalize the angular gradient average.** Proved result. The unnormalized gradient orbit average equals 2π times the local gradient mode. (`orbit_grad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L744)).

**The plane weight has compact box support.** Proved result. Under the declaration's hypotheses, the selected plane weight has compact support and vanishes outside the specified positive-radius box. (`weight_support`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L749)).

**Derivatives vanish outside support.** Proved result. Under the declaration's hypotheses, every directional derivative of a function is zero at a point outside its topological support. (`fderiv_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L754)).

**weighted normalized mode is integrable.** Proved result. Under the declaration's hypotheses, the plane weight times the normalized mode is integrable when the corresponding unnormalized orbit pairing is integrable. (`int_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L758)).

**Normalize an angular pairing.** Proved result. If the angular orbit integral is two pi times its normalized mode, the same factor relates their weighted plane integrals. (`integral_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L765)).

**Integral Cauchy-Schwarz with total mass.** Proved result. Under the declaration's hypotheses, the square of a nonnegative integral is at most the total measure times the integral of the square. (`sq_lintegral_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L773)).

**Bound plane-mode energy by slab energy.** Proved result. Under the declaration's hypotheses, the squared plane Fourier average integrated over a box is bounded by two pi divided by its lower radius times the one-period field energy on the containing ball. (`orbit_sq_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L785)).

**A.e. measurable plane Fourier averages.** Proved result. Under the declaration's hypotheses, the normalized temporal Fourier average of the angular orbit mode is almost everywhere strongly measurable on the plane. (`aesm_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L862)).

**Square-integrable plane Fourier averages.** Proved result. Under the declaration's hypotheses, the normalized temporal Fourier average of the orbit mode is square integrable on the specified plane box. (`memLp_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L877)).

**Read an axial column before averaging.** Proved result. Averaging the axial-axial gradient evaluator equals averaging the axial component of the gradient's axial column. (`orbit_grad_column`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L892)).

**Plane velocity modes are locally in L2.** Proved result. Under the declaration's hypotheses, each plane velocity component is square integrable on the selected bounded rectangle away from the axis. (`planeVel_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L898)).

**Axial height modes are locally in L2.** Proved result. Under the declaration's hypotheses, the axial height-derivative mode is square integrable on the selected bounded rectangle away from the axis. (`planeHeight_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L914)).

**Weak divergence-free plane modes.** Proved result. For a perturbation, the radial and axial radius-weighted mode pairings with test derivatives cancel the imaginary angular-frequency pairing with the azimuthal mode. (`planeVel_divergence_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L935)).

**Weighted axial weak derivative.** Proved result. Under the declaration's hypotheses, the radius-weighted axial velocity mode and axial height mode satisfy the weak height derivative identity on the plane. (`planeVel_height_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchModeWeak.lean#L990)).

### Breakdown.CertCell.PatchRoughTest

Extend the weak patch identity from smooth compactly supported tests to the Lipschitz tests used at the boundary. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A bounded half-plane test strip.** Definition. Use a compact rectangle with a positive inner radius for the test support. (`strip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L20)).

**Bounded strip is measurable.** Proved result. The bounded half-plane strip is a measurable set. (`measurableSet_strip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L22)).

**Bounded strip is compact.** Proved result. The bounded half-plane strip is compact. (`isCompact_strip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L24)).

**Integrability with bounded multipliers.** Proved result. Under the declaration's hypotheses, the product of the bounded supported test and the locally integrable coefficient is integrable on the plane. (`integrable_bdd_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L26)).

**Enclose support in a positive strip.** Proved result. Under the declaration's hypotheses, a compactly supported plane function whose support avoids the axis vanishes outside a bounded strip with a strictly positive lower radius. (`exists_strip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L33)).

**Vanishing outside the support strip.** Proved result. If the topological support lies in the strip, the function is zero at every point outside that strip. (`zero_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L46)).

**Derivatives vanish outside the strip.** Proved result. If a function's topological support lies in a strip, each directional derivative vanishes outside the strip. (`fderiv_zero_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L50)).

**Extend real test identities to complex.** Proved result. Under the declaration's hypotheses, a first-order weak identity valid for all real smooth supported tests away from the axis also holds for every complex smooth supported test there. (`smooth_complex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L56)).

**Smooth a test by convolution.** Definition. Convolve the test with a normalized smooth bump. (`mollify`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L119)).

**Mollification as translated convolution.** Proved result. The mollified test at a point is the integral of the normalized bump times the original test translated by the negative integration variable. (`mollify_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L122)).

**Mollified test is smooth.** Proved result. Under the hypotheses of this declaration, the mollified test is smooth. (`mollify_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L127)).

**Mollification preserves a uniform bound.** Proved result. If the original function has norm at most a constant everywhere, convolution with the normalized bump has the same bound. (`mollify_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L131)).

**Support enlargement by mollification.** Proved result. Under the declaration's hypotheses, mollifying a function supported in a strip by a bump of radius at most delta gives zero outside the strip expanded by delta in both directions. (`mollify_zero_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L140)).

**The mollification kernel is integrable.** Proved result. Under the declaration's hypotheses, at every evaluation point, the normalized bump times the translated function is integrable in the convolution variable. (`mollify_integrable_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L159)).

**Differentiate under mollification.** Proved result. Under the declaration's hypotheses, the constant-direction derivative of the mollified test equals the mollification of that derivative. (`fderiv_mollify`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L165)).

**A sequence of shrinking smooth bumps.** Definition. Choose smooth bumps with outer radii tending to zero. (`bumpSeq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L222)).

**Shrinking bumps stay within their scale.** Proved result. Under the declaration's hypotheses, the outer support radius of each shrinking bump is at most the chosen positive scale. (`bumpSeq_rOut_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L231)).

**The bump radii tend to zero.** Proved result. Under the declaration's hypotheses, the outer radii of the chosen smooth bumps tend to zero. (`bumpSeq_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L235)).

**Bump radii eventually have bounded ratio.** Proved result. Under the declaration's hypotheses, eventually the outer radius of each bump is at most twice its inner radius. (`bumpSeq_ratio`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L239)).

**Insert an indicator where the test lives.** Proved result. Under the declaration's hypotheses, a multiplier vanishing outside the set allows the field factor to be replaced by its indicator restriction. (`indicator_eq_of_zero_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L245)).

**Extend weak identities to rough tests.** Proved result. Under the declaration's hypotheses, a first-order weak identity for smooth real tests extends to compactly supported complex Lipschitz tests whose support stays at positive radius. (`weak_identity_rough`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchRoughTest.lean#L255)).

### Breakdown.CertCell.PatchTraceBound

Construct clamped and ramped tests and bound the patch trace by its weighted energy. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Bounded plane boxes have finite measure.** Proved result. Lebesgue measure restricted to the closed radial-height box is a finite measure. (`box_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L17)).

**L2 control gives integrability on a box.** Proved result. Under the declaration's hypotheses, a square-integrable function on the bounded radial-height box is integrable there. (`integrableOn_of_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L20)).

**Box integrability with radial weights.** Proved result. Under the declaration's hypotheses, multiplying an integrable function by radius preserves integrability on a bounded radial-height box. (`integrableOn_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L25)).

**Weak divergence for Lipschitz tests.** Proved result. Under the declaration's hypotheses, the plane velocity modes satisfy their radius-weighted weak divergence identity for every compactly supported complex Lipschitz test away from the axis. (`divergence_rough`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L34)).

**The rough radial weak identity.** Proved result. Under the declaration's hypotheses, the radial test-derivative pairing cancels the test pairing with the imaginary angular-frequency term and the radius-weighted axial height mode. (`radial_rough`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L59)).

**Clamp to a closed interval.** Definition. Replace a scalar by the larger of the lower endpoint and its minimum with the upper endpoint. (`clampTo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L108)).

**Clamping is 1-Lipschitz.** Proved result. Clamping a real number to a closed interval is a 1-Lipschitz function. (`clampTo_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L110)).

**Clamping fixes an interior point.** Proved result. Under the declaration's hypotheses, a point in the closed interval is unchanged by clamping. (`clampTo_of_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L118)).

**Clamping below gives the first endpoint.** Proved result. Under the declaration's hypotheses, a point at or below the lower endpoint clamps to that endpoint. (`clampTo_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L121)).

**Clamping above gives the last endpoint.** Proved result. Under the declaration's hypotheses, a point at or above the upper endpoint clamps to that endpoint. (`clampTo_of_ge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L125)).

**Clamping stays inside the interval.** Proved result. Under the declaration's hypotheses, clamping a real number to an ordered interval gives a value between its two endpoints. (`clampTo_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L128)).

**Bounded Lipschitz products are Lipschitz.** Proved result. Under the declaration's hypotheses, the product of the two bounded Lipschitz functions has a finite Lipschitz constant. (`slope_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L131)).

**Extend a boundary trace by clamping.** Definition. Read the test on the zero-height edge after clamping its radial coordinate. (`edgeValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L149)).

**The clamped linear height cutoff.** Definition. Subtract the clamped height divided by the patch height from one. (`heightWeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L151)).

**A test with its lower trace removed.** Definition. Subtract the lower-edge value times the height cutoff from the clamped test. (`coreTest`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L153)).

**A cutoff ramp near the lower edge.** Definition. Take the minimum of the height cutoff and a truncated affine ramp below zero. (`rampWeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L156)).

**A test concentrated near the edge.** Definition. Multiply the extended boundary trace by the cutoff ramp. (`rampTest`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L158)).

**Clamping preserves the boundary bound.** Proved result. Under the declaration's hypotheses, the extended boundary value inherits the stated Lipschitz constant of the test. (`edgeValue_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L161)).

**Edge tests vanish outside their interval.** Proved result. When the original test vanishes on both radial sides, its clamped lower-edge value is zero outside the closed radial interval. (`edgeValue_side`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L169)).

**Bound the lower-edge value by the width.** Proved result. For a Lipschitz test vanishing on both radial sides, its clamped lower-edge value has norm at most the Lipschitz constant times the radial width. (`edgeValue_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L176)).

**height cutoff lies between zero and one.** Proved result. For positive patch height, the clamped height cutoff takes values between zero and one. (`hw_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L185)).

**The height cutoff is Lipschitz.** Proved result. Under the declaration's hypotheses, the clamped height cutoff has Lipschitz constant one divided by the positive patch height. (`hw_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L193)).

**The height cutoff equals one below zero.** Proved result. Under the declaration's hypotheses, at nonpositive height, the clamped height cutoff equals one. (`hw_of_nonpos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L203)).

**height cutoff vanishes above the patch.** Proved result. For positive patch height, the height cutoff is zero at and above that height. (`hw_of_ge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L206)).

**The cutoff is affine inside the patch.** Proved result. Under the declaration's hypotheses, within the height interval, the cutoff equals one minus height divided by the patch height. (`hw_of_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L209)).

**The core test is Lipschitz.** Proved result. Under the declaration's hypotheses, the clamped test with its lower-edge contribution removed has a finite Lipschitz constant. (`core_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L212)).

**The core test vanishes outside the patch.** Proved result. If the original test vanishes on the radial sides and top, the test after removal of its lower trace vanishes outside the patch. (`core_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L233)).

**Cutoff ramps lie between zero and one.** Proved result. For positive patch height, every boundary cutoff ramp takes values between zero and one. (`ramp_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L248)).

**The boundary ramp is Lipschitz.** Proved result. Under the declaration's hypotheses, each cutoff ramp has a finite Lipschitz constant. (`ramp_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L251)).

**ramp agrees with the cutoff above zero.** Proved result. Under the declaration's hypotheses, at nonnegative height, the cutoff ramp equals the original height cutoff. (`ramp_of_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L259)).

**ramp vanishes below its lower threshold.** Proved result. Under the declaration's hypotheses, the boundary ramp is zero wherever one plus its slope parameter times height is nonpositive. (`ramp_of_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L264)).

**ramp vanishes at and above the patch top.** Proved result. Under the declaration's hypotheses, every boundary ramp is zero at heights at least the positive patch height. (`ramp_of_ge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L269)).

**The ramp test is Lipschitz.** Proved result. Under the declaration's hypotheses, the boundary value multiplied by the cutoff ramp has a finite Lipschitz constant. (`rampTest_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L273)).

**ramp test has a fixed support rectangle.** Proved result. Under the declaration's hypotheses, the ramp test vanishes outside the radial interval crossed with the height interval from minus one to the patch height. (`rampTest_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L287)).

**Differentiate a separated plane test.** Proved result. Under the declaration's hypotheses, the radial and height derivatives of the separated product differentiate their respective factors. (`fderiv_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L299)).

**A fixed vertical line has measure zero.** Proved result. The first planar coordinate differs from the fixed value almost everywhere. (`ae_fst_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L320)).

**A fixed horizontal line has measure zero.** Proved result. The second planar coordinate differs from the fixed value almost everywhere. (`ae_snd_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L326)).

**Lift a radial null set to the plane.** Proved result. Under the declaration's hypotheses, an almost-everywhere property on the real line holds at the first coordinate of almost every planar point. (`ae_fst_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L332)).

**Lift a height null set to the plane.** Proved result. Under the declaration's hypotheses, an almost-everywhere property on the real line holds at the second coordinate of almost every planar point. (`ae_snd_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L335)).

**Edge derivatives vanish off the interval.** Proved result. Under the declaration's hypotheses, the derivative of the clamped edge test is zero strictly below the lower radial endpoint and strictly above the upper endpoint. (`edge_deriv_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L338)).

**Differentiate the core test in the patch.** Proved result. Under the declaration's hypotheses, inside the patch, the core derivative is the original test derivative minus the derivative of its lower-edge correction. (`core_fderiv_in`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L348)).

**Core derivatives vanish off the patch.** Proved result. Under the declaration's hypotheses, with the side and top boundary conditions, the derivative of the core test is zero outside the patch. (`core_fderiv_out`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L367)).

**Bound a pairing by two energies.** Proved result. If an integrand is almost everywhere bounded by the product of square roots of two nonnegative integrable weights, its integral norm squared is at most the product of their integrals. (`norm_integral_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L377)).

**Bound a three-component pairing.** Proved result. The absolute value of the three-term complex pairing is bounded by the product of the two Euclidean component norms. (`sum_three_mul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L414)).

**The affine height cutoff has slope −1/h.** Proved result. The derivative of one minus height divided by h is minus one divided by h. (`deriv_height_line`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L426)).

**Localize an almost everywhere pairing.** Proved result. Under the declaration's hypotheses, agreement almost everywhere on the set and vanishing outside it identify the whole-space integral with the restricted integral. (`integral_eq_set_of_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L431)).

**Weak divergence of the corrected test.** Proved result. Under the declaration's hypotheses, subtracting the lower-edge value times the linear height cutoff from the test gives a zero weak divergence pairing over the patch. (`core_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L436)).

**The radial identity for the edge cutoff.** Proved result. Under the declaration's hypotheses, the linear height cutoff times the edge test gives a zero sum of its radial derivative pairing and its angular-frequency and axial-derivative pairings over the patch. (`ramp_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L497)).

**Express the patch trace in its interior.** Proved result. Under the declaration's hypotheses, the patch trace is the radius-weighted integral of the lower-edge test value times the axial derivative mode with a linear height cutoff minus the axial velocity mode divided by the patch height. (`trace_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L668)).

**Integrability with bounded multipliers.** Proved result. Under the declaration's hypotheses, the product of a bounded measurable multiplier and an integrable coefficient is integrable on the chosen set. (`bdd_on`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L731)).

**Bound the test inside the patch.** Proved result. Under the declaration's hypotheses, a Lipschitz test vanishing on both radial sides has norm at most its Lipschitz constant times the patch width at every point of the patch. (`phi_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L736)).

**Lipschitz bounds control derivatives.** Proved result. Under the declaration's hypotheses, the derivative of a Lipschitz function applied to a vector of norm at most one has norm at most its Lipschitz constant. (`fderiv_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L744)).

**The radial unit vector has bounded norm.** Proved result. The norm of the radial coordinate vector in the plane is at most one. (`norm_unit_r`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L750)).

**The height unit vector has bounded norm.** Proved result. The norm of the height coordinate vector in the plane is at most one. (`norm_unit_z`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L752)).

**Patch trace from weighted divergence.** Proved result. Under the declaration's hypotheses, the patch trace equals the interior pairing with radial and height test derivatives plus the angular-frequency correction involving the azimuthal velocity mode. (`main_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L754)).

**A real scalar squares in the norm.** Proved result. The squared norm of a real scalar times a complex number equals the scalar square times the squared complex norm. (`sq_norm_real_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L868)).

**The angular multiplier contributes k².** Proved result. Multiplication by minus i times the integer angular frequency multiplies the squared norm by the frequency square. (`sq_norm_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L871)).

**Bound the cylindrical test gradient.** Proved result. Under the declaration's hypotheses, the test-gradient square is nonnegative and is bounded by twice the squared Lipschitz constant plus the squared angular frequency times the squared width bound divided by the squared lower radius. (`gradSq_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L874)).

**A product of energies bounds the trace.** Proved result. For the admissible off-axis patch and boundary-vanishing test, a measurable weight bounded above and bounded below by a positive constant makes the trace norm squared at most the product of the radius-weighted velocity-mode energy and the reciprocal-weight test-gradient energy. (`patchTraceBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PatchTraceBound.lean#L895)).

### Breakdown.CertCell.PeriodicSecondOrder

Extract the periodic second-order field package from a perturbation and its proposed derivatives. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A perturbation gives second-order data.** Proved result. Under the declaration's hypotheses, the perturbation and its proposed first and second derivatives satisfy the periodic second-order field conditions. (`periodicSecondOrder_of_perturbation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PeriodicSecondOrder.lean#L16)).

### Breakdown.CertCell.PinHalfPlane

Reduce the pin pairing from time and space to lattice-labelled half-plane modes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Real pairing of gradient modes.** Definition. Take the real part of the Hermitian pairing of two gradient Fourier coefficients. (`pairDensity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L25)).

**A common unit phase cancels in a pairing.** Proved result. Under the declaration's hypotheses, multiplying both matrix arguments by the same complex unit phase leaves their Hermitian pairing unchanged. (`cdotMat_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L28)).

**A unit phase preserves the mode norm.** Proved result. Under the declaration's hypotheses, multiplying all matrix entries by one common unit phase preserves their square norm. (`cnormSq_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L38)).

**Gradient pairings ignore base time.** Proved result. Under the declaration's hypotheses, the real Hermitian pairing density of equal-frequency gradient modes at any base time equals its value at time zero. (`pairDensity_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L44)).

**Gradient norms ignore base time.** Proved result. Under the declaration's hypotheses, the squared entry norm of a gradient Fourier mode at any base time equals its value at time zero. (`cnormSq_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L51)).

**Orthogonal maps preserve pairings.** Proved result. Under the declaration's hypotheses, applying the same real orthogonal matrix to two complex coordinate families preserves their Hermitian pairing. (`sum_orth_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L55)).

**The inverse rotation is the transpose.** Proved result. An entry of the inverse axial rotation matrix equals the transposed entry of the forward rotation matrix. (`rot_transpose`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L73)).

**Orthogonality of rotated basis vectors.** Proved result. The dot product of two rotated coordinate vectors is one for equal indices and zero for distinct indices. (`rot_orth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L77)).

**Orthogonality for two-index rotations.** Proved result. The products of two axial rotation entries form orthonormal columns when summed over both matrix-coordinate indices. (`rot_pair_orth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L82)).

**Rotate both indices of a complex matrix.** Proved result. A rotated complex matrix entry is the sum of original entries weighted by rotation coefficients for each matrix index. (`rotCMat_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L95)).

**Matrix rotations preserve pairings.** Proved result. Applying the same two-index axial rotation to two complex matrices leaves their Hermitian pairing unchanged. (`cdotMat_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L105)).

**gradient pairing is axially invariant.** Proved result. Under the declaration's hypotheses, the real Hermitian gradient-mode pairing density is unchanged when the spatial point is rotated around the axis. (`pairDensity_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L114)).

**Bound a real matrix pairing by energies.** Proved result. The absolute real part of the Hermitian matrix pairing is at most the sum of the two squared entry norms. (`abs_pair_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L122)).

**Reflection reverses rotation.** Proved result. Reflecting before axial rotation equals rotating through the opposite angle before reflecting. (`flip_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L129)).

**Reflection reverses a rotation angle.** Proved result. A rotated coordinate unit vector equals the reflection of the vector rotated by the opposite angle, multiplied by that coordinate's reflection sign. (`rot_unit_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L133)).

**Real scaling of rotated components.** Proved result. A coordinate of the rotation of a scalar multiple is that scalar times the corresponding rotated coordinate. (`rot_smul_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L137)).

**Paired signs for reflected gradients.** Proved result. Under the declaration's hypotheses, a gradient-mode entry at the reflected point and reflected frequency is its original entry multiplied by the two coordinate reflection signs. (`modeGrad_flip_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L142)).

**Reflection preserves a gradient pairing.** Proved result. Under the declaration's hypotheses, reflecting the point and angular frequency together leaves the real Hermitian gradient-mode pairing density unchanged. (`pairDensity_flip_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L188)).

**Remove an unused time variable.** Proved result. Under the declaration's hypotheses, an almost-everywhere product-space property depending only on space holds almost everywhere in space. (`ae_of_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L207)).

**Spatial projection and measurability.** Proved result. If a function pulled back by the spatial projection is almost everywhere strongly measurable on the product, the spatial function is almost everywhere strongly measurable. (`aesm_of_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L212)).

**Mode pairing density is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the real pairing density of two gradient modes is almost everywhere strongly measurable for the stated measure. (`aesm_pairDensity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L218)).

**The time-zero pairing is a.e. measurable.** Proved result. Under the declaration's hypotheses, the real gradient-mode pairing density at time zero is almost everywhere strongly measurable in space. (`aesm_pairDensity_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L228)).

**time-zero mode energy is a.e. measurable.** Proved result. Under the declaration's hypotheses, the nonnegative squared entry norm of the gradient mode at time zero is almost everywhere measurable in space. (`aemeas_cnormSq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L236)).

**Gradient mode energies have finite total.** Proved result. Under the declaration's hypotheses, the sum over all frequencies of the spatial integrals of squared gradient-mode norms is finite. (`modeNorm_tsum_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L247)).

**Square bounds give local integrability.** Proved result. Under the declaration's hypotheses, the operator-valued field is locally integrable in spacetime under the assumed local integrability of its squared-entry sum. (`locallyIntegrable_of_squareSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L262)).

**Points with rotation-invariant modes.** Definition. Collect points where all relevant labelled densities are invariant under axial rotation. (`goodSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L273)).

**Rotation preserves pairing-good points.** Proved result. Rotating a point preserves the condition that all gradient-mode pairing densities are rotation invariant there. (`goodSet_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L276)).

**Pairing invariance almost everywhere.** Proved result. Under the declaration's hypotheses, almost every spatial point satisfies rotation invariance of all the gradient-mode pairing densities. (`ae_goodSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L287)).

**symmetric restriction is a.e. measurable.** Proved result. Under the declaration's hypotheses, the restriction of the rotation-compatible spatial function to embedded radial-height points is almost everywhere strongly measurable on the plane. (`aesm_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L300)).

**Reflection preserves the mode lattice.** Proved result. Under the declaration's hypotheses, a reflected frequency belongs to the allowed harmonic lattice exactly when the original frequency does. (`lattice_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L319)).

**Restrict pairing to lattice labels.** Definition. Keep the mode-pairing density on allowed lattice harmonics and use zero elsewhere. (`latticePart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L330)).

**Split an absolute value into two signs.** Proved result. The nonnegative real embedding of an absolute value equals the sum of the nonnegative embeddings of the value and its negative. (`ofReal_abs_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L333)).

**Nonnegative pin terms on a half-plane.** Proved result. Under the declaration's hypotheses, the sum of spatial integrals of nonnegative pin densities equals four pi times the sum of their radius-weighted half-plane integrals. (`lint_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L338)).

**Positive half-plane is measurable.** Proved result. The positive radial half-plane is a measurable set. (`measurableSet_halfPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L355)).

**Signed pin terms on a half-plane.** Proved result. Under the declaration's hypotheses, the sum of signed spatial integrals equals four pi times the corresponding sum of radius-weighted half-plane integrals. (`signed_reduction`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L359)).

**Reflection of pairings almost everywhere.** Proved result. Under the declaration's hypotheses, almost everywhere in space, the reflected-frequency pairing at the reflected point equals the original pairing at time zero. (`ae_pairDensity_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L448)).

**Off-lattice pairings vanish a.e..** Proved result. Under the declaration's hypotheses, at a frequency outside the perturbation's symmetry lattice, the real gradient-mode pairing with any admissible periodic comparison field vanishes almost everywhere. (`ae_pairDensity_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L460)).

**Remove time from a mode pairing.** Proved result. Under the declaration's hypotheses, the one-period integral of the real Hermitian gradient-mode pairing equals the spatial integral of its pairing density at time zero. (`term_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L472)).

**Pin pairing as labelled plane modes.** Proved result. Under the declaration's hypotheses, the spacetime pin pairing equals four pi times the sum of radius-weighted half-plane Hermitian pairings of the labelled gradient modes. (`pin_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L484)).

**The pin pairing reduces to a half-plane.** Proved result. Under the hypotheses of this declaration, the pin pairing equals the weighted half-plane sum of lattice-mode gradient pairings. (`pinHalfPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PinHalfPlane.lean#L576)).

### Breakdown.CertCell.PlaneDataFlipLinks

Transfer reflection symmetry to the plane velocity, gradient and second-derivative data almost everywhere. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Plane reflection reverses height.** Proved result. Reflecting an embedded radial-height point preserves its radius and negates its height. (`flipPoint_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PlaneDataFlipLinks.lean#L22)).

**Reflection of fields and derivatives.** Proved result. Under the declaration's hypotheses, almost everywhere in spacetime, reflection acts on the velocity output, on the gradient input and output, and on both Hessian inputs and its output. (`ae_field_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PlaneDataFlipLinks.lean#L27)).

**Plane mode reflection has tensor signs.** Proved result. For almost every radius and almost every height, reversing the angular frequency is equivalent to negating height and multiplying velocity, gradient and Hessian entries by one, two and three coordinate reflection signs. (`ae_plane_mode_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PlaneDataFlipLinks.lean#L68)).

**Reflected modes have signed plane traces.** Proved result. Under the hypotheses of this declaration, for almost every positive radius, reversing angular frequency multiplies the equatorial velocity trace by its coordinate reflection sign and its height-derivative trace by the opposite sign. (`planeDataFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PlaneDataFlipLinks.lean#L130)).

### Breakdown.CertCell.PotentialConstant

Prove that a locally integrable scalar with zero weak gradient is almost everywhere constant, then show that two weak potentials of the same field differ almost everywhere by one constant. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Local square bounds give integrability.** Proved result. Under the declaration's hypotheses, a scalar function whose square is locally integrable is itself locally integrable. (`locallyIntegrable_of_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L18)).

**Zero columns determine the zero map.** Proved result. Under the declaration's hypotheses, a continuous linear map that vanishes on every coordinate unit vector is zero. (`clm_eq_zero_of_units`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L26)).

**Reflection changes the derivative sign.** Proved result. Under the declaration's hypotheses, differentiating the test evaluated at x minus y introduces a minus sign in the constant direction. (`reflect_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L31)).

**Weak constants have zero smoothed slope.** Proved result. If a locally integrable scalar function pairs to zero with every test derivative, convolving it with the derivative of a smooth compactly supported kernel gives zero. (`conv_fderiv_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L39)).

**Weak constants smooth to constants.** Proved result. Under the declaration's hypotheses, the smoothed function has the same value at any two points under the stated zero weak-gradient hypotheses. (`conv_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L62)).

**Shrinking normalized-support bumps.** Definition. Choose a smooth bump with inner radius 1 divided by N plus 1 and twice that outer radius. (`shrinkBump`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L73)).

**A zero weak gradient gives a constant.** Proved result. Under local integrability and the weak zero-gradient identities, the function is almost everywhere equal to one real constant. (`ae_const_of_weak_grad_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L81)).

**Potentials differ by a constant.** Proved result. Two weak potentials of the same vector field differ almost everywhere by one real constant. (`potentialConstant`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialConstant.lean#L104)).

### Breakdown.CertCell.PotentialNegation

Check that negating a potential negates its weak gradient. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Negate a potential and its gradient.** Proved result. Negating a weak potential negates its gradient field. (`potentialNegation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialNegation.lean#L15)).

### Breakdown.CertCell.PotentialOfGradient

Supply a weak potential for a gradient field from the chosen potential construction. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A gradient field has a weak potential.** Proved result. For a gradient field, its chosen potential has that field as its weak gradient. (`potentialOfGradient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialOfGradient.lean#L12)).

### Breakdown.CertCell.PotentialShift

Check that adding or subtracting a constant leaves a weak potential gradient unchanged. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Square bounds give local integrability.** Proved result. Under the declaration's hypotheses, local square-integrability of the scalar potential implies its local integrability. (`locallyIntegrable_of_square`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialShift.lean#L18)).

**integral of a test derivative is zero.** Proved result. Under the declaration's hypotheses, the integral of a constant-direction derivative of the supported smooth test is zero. (`integral_directionalDeriv_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialShift.lean#L28)).

**Constant shifts preserve the gradient.** Proved result. Subtracting any real constant from a weak potential preserves its weak gradient. (`potentialShift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PotentialShift.lean#L46)).

### Breakdown.CertCell.PressureModeDerivative

Use weak scalar identities and dense line tests to identify radial and height derivatives of pressure modes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Radial or full-line test domain.** Definition. Select the positive half-line for radial tests and the whole line for height tests. (`dom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L20)).

**Compact sets exhausting the domain.** Definition. Use expanding closed intervals, staying away from zero on the radial branch. (`ex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L22)).

**Smooth tests supported in the domain.** Proposition definition. Require smoothness, compact support and containment of the support in the chosen line domain. (`IsAdm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L25)).

**The selected line domain is open.** Proved result. The line domain, either the positive axis or the whole line according to its flag, is open. (`isOpen_dom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L28)).

**The selected line domain is measurable.** Proved result. The line domain selected by the positivity flag is Lebesgue measurable. (`measurableSet_dom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L31)).

**Line exhaustion intervals are compact.** Proved result. Every closed interval in the selected line-domain exhaustion is compact. (`isCompact_ex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L33)).

**Line exhaustion intervals are measurable.** Proved result. Every interval in the selected line-domain exhaustion is Lebesgue measurable. (`measurableSet_ex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L36)).

**Exhaustion intervals stay in the domain.** Proved result. Each compact exhaustion interval lies in its chosen radial or full-line domain. (`ex_sub_dom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L39)).

**Exhaustion intervals increase.** Proved result. Under the declaration's hypotheses, increasing the natural-number index enlarges the compact exhaustion interval. (`ex_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L48)).

**The intervals exhaust compact subsets.** Proved result. Under the declaration's hypotheses, every compact subset of the chosen line domain is contained in one exhaustion interval. (`exists_ex_of_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L57)).

**Supported tests belong to their domain.** Proved result. Under the declaration's hypotheses, the stated smooth test with its support containment satisfies the admissible-test condition. (`adm_of_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L94)).

**Localize a compactly supported test.** Proved result. Under the declaration's hypotheses, a scalar-mode pairing with a test supported in a set equals the integral restricted to that set. (`integral_eq_setIntegral_of_tsupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L98)).

**Continuous dependence on the test.** Proved result. Under the declaration's hypotheses, pairing an integrable coefficient on the fixed set with a continuous real test embedded in the complex numbers is a continuous functional of that test. (`continuous_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L104)).

**Continuous test-derivative pairs.** Definition. Collect continuous-function pairs arising from a smooth test and its derivative with bounded support. (`pairSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L132)).

**Countable tests determine derivatives.** Proved result. There is a countable family of admissible tests whose weak derivative identities imply the identity for every admissible test whenever both functions are locally integrable on the exhaustion intervals. (`countable_dense_tests`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L135)).

**Restricted rectangle measure factors.** Proved result. Volume restricted to a product set equals the product of the separately restricted line measures. (`restrict_prod_eq'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L173)).

**Integrable boxes have integrable slices.** Proved result. Under the declaration's hypotheses, an integrable function on the product set has integrable first-coordinate slices for almost every retained second coordinate. (`ae_slice_integrableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L177)).

**Every domain point enters the exhaustion.** Proved result. Under the declaration's hypotheses, every point of the selected line domain belongs to some compact exhaustion interval. (`ex_mem_of_dom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L184)).

**Slice integrability on every exhaustion.** Proved result. Under the declaration's hypotheses, almost every admissible second coordinate gives an integrable first-coordinate slice on every compact exhaustion interval. (`ae_slices`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L188)).

**Integrability with separated tests.** Proved result. Under the declaration's hypotheses, multiplying the plane coefficient by the product of admissible radial and height tests gives an integrable function. (`integrable_test_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L196)).

**Weak identities on almost every slice.** Proved result. For almost every transverse coordinate in its domain, the weak derivative identity holds on each slice with the required local integrability. (`ae_slice_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L213)).

**Almost every slice has a weak derivative.** Proved result. For almost every transverse coordinate in its domain, both sliced coefficients are integrable on every exhaustion interval and satisfy the weak identity for every admissible test. (`ae_slice_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L305)).

**A slice identity gives a weak derivative.** Proved result. Under the declaration's hypotheses, the slice integration-by-parts identity gives the stated weak derivative on the interval. (`weak_of_slice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L322)).

**Remove the radial weight off the axis.** Proved result. Under the declaration's hypotheses, integrability of radius times a function on a rectangle with positive lower radius implies integrability of the unweighted function there. (`integrableOn_of_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L338)).

**Local pressure-gradient integrability.** Proved result. Under the declaration's hypotheses, the pressure-gradient field is locally integrable in space under the prescribed local control near every point. (`locInt_of_near`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L354)).

**Pressure modes integrate off the axis.** Proved result. Under the declaration's hypotheses, the pressure Fourier mode is integrable on each bounded rectangle with positive lower radius. (`pres_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L362)).

**Pressure-gradient modes off the axis.** Proved result. Under the declaration's hypotheses, each component of the pressure-gradient Fourier mode is integrable on the bounded rectangle separated from the axis. (`vec_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L372)).

**Weak plane derivatives of pressure modes.** Proved result. Under the declaration's hypotheses, the radial and height weak derivatives of a pressure mode are the radial and axial components of its pressure-gradient mode. (`plane_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L380)).

**Differentiate the first test factor.** Proved result. Under the declaration's hypotheses, the radial derivative of a separated product test is the derivative of its radial factor times its height factor. (`fderiv_test_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L415)).

**Differentiate the second test factor.** Proved result. Under the declaration's hypotheses, the height derivative of a separated product test is its radial factor times the derivative of its height factor. (`fderiv_test_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L426)).

**Products give admissible plane tests.** Proved result. Under the declaration's hypotheses, the product of smooth compactly supported radial and height tests is smooth and compactly supported, with support contained in the product of their supports. (`prod_test_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L437)).

**Pressure modes have weak derivatives.** Proved result. For a weak scalar potential with locally square-integrable gradient, the pressure mode has the radial gradient mode as weak derivative on positive radial intervals at almost every height and the axial gradient mode as weak height derivative at almost every positive radius. (`pressureModeDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeDerivative.lean#L457)).

### Breakdown.CertCell.PressureModeIntegrable

Establish pressure-mode and pressure-gradient integrability on cell rectangles, with the radial weight where needed. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Local square control from near bounds.** Proved result. Under the declaration's hypotheses, the stated near-field bounds imply local integrability of the squared field norm. (`squareNear_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeIntegrable.lean#L17)).

**Weighted pressure gradients at the axis.** Proved result. Under the declaration's hypotheses, radius times a pressure-gradient mode is integrable on the bounded rectangle whose lower radial endpoint is zero. (`weightedMode_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeIntegrable.lean#L26)).

**Pressure modes integrate up to the axis.** Proved result. Under the declaration's hypotheses, the scalar pressure mode is integrable on the bounded radial-height rectangle that includes the axis. (`pressureMode_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeIntegrable.lean#L37)).

**Off-axis gradient-mode integrability.** Proved result. Under the declaration's hypotheses, the pressure-gradient mode is integrable without a radial weight on a bounded strip with positive lower radius. (`offAxisMode_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeIntegrable.lean#L68)).

**Pressure modes are locally integrable.** Proved result. The pressure modes and the stated weighted pressure-gradient modes are integrable on the required rectangles. (`pressureModeIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureModeIntegrable.lean#L91)).

### Breakdown.CertCell.PressurePlaneFlip

Show that reflected pressure has the same normalized potential and the corresponding reflected Fourier modes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Signs of the spatial reflection.** Definition. Keep the first coordinate and negate the second and third coordinates. (`flipSign`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L18)).

**A reflection sign squares to one.** Proved result. Multiplying the coordinate reflection sign by itself gives one. (`flipSign_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L20)).

**The two signs of spatial reflection.** Proved result. The spatial reflection preserves the first coordinate and negates the second and third coordinates. (`flipPoint_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L23)).

**Spatial reflection is an involution.** Proved result. Applying the spatial reflection twice returns the original point. (`flipPoint_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L26)).

**The linear spatial reflection.** Definition. Package the coordinate reflection as a real linear map. (`flipLinear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L30)).

**Reflection preserves the spatial norm.** Proved result. The spatial reflection preserves the Euclidean norm. (`norm_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L41)).

**The isometric spatial reflection.** Definition. Package the norm-preserving reflection as a linear isometric equivalence. (`flipIsometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L50)).

**The pressure reflection isometry.** Proved result. The packaged reflection isometry acts by the same coordinate reflection as the pressure symmetry formulas. (`flipIsometry_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L53)).

**Reflection preserves volume.** Proved result. The spatial reflection preserves Lebesgue measure. (`flip_measurePreserving`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L55)).

**Reflection is a measurable embedding.** Proved result. The spatial reflection is a measurable embedding. (`flip_embedding`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L58)).

**Spatial reflection preserves an integral.** Proved result. Precomposing a spatial integrand by the reflection leaves its Lebesgue integral unchanged. (`integral_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L61)).

**Reflection signs of coordinate vectors.** Proved result. Reflecting a coordinate unit vector multiplies it by its coordinate reflection sign. (`flip_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L64)).

**Read the sign of a reflected coordinate.** Proved result. Pairing a reflected vector with a coordinate unit vector gives the original coordinate multiplied by its reflection sign. (`inner_flip_unit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L69)).

**Reflect a scalar potential.** Proved result. Under the declaration's hypotheses, composing the scalar potential with the spatial reflection gives another weak potential for the reflection-compatible gradient field. (`potential_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L74)).

**scalar potential is reflection invariant.** Proved result. Under the declaration's hypotheses, almost everywhere in space, the scalar potential has the same value at a point and its spatial reflection. (`flip_ae_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L115)).

**Reflection reverses angle and height.** Proved result. Reflecting a cylindrical point preserves its radius and negates both its angular coordinate and height. (`cyl_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L127)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`cyl_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L132)).

**Integer frequencies give full turns.** Proved result. The angular Fourier exponential equals one after a full turn because its angular frequency is an integer. (`azimuth_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L135)).

**Reflect the angular pressure frequency.** Proved result. The pressure mode at reversed angular frequency and height equals the original-frequency mode of the spatially reflected potential. (`presMode_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L141)).

**Shift a periodic integral symmetrically.** Proved result. Under the declaration's hypotheses, the integral of a two-pi-periodic function over the positive full period equals its integral from minus pi to pi. (`interval_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L165)).

**Periodic pressure-mode integrands.** Proved result. The pressure-mode integrand is periodic in angle with period two pi. (`mode_integrand_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L171)).

**Orbit agreement gives equal modes.** Proved result. Under the declaration's hypotheses, potentials that agree at almost every angle along the symmetric cylindrical orbit have the same pressure Fourier mode there. (`presMode_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L184)).

**Pressure reflection holds a.e..** Proved result. For a weak potential with locally square-integrable reflection-compatible gradient, reversing angular mode and height together preserves the pressure mode almost everywhere on the half-plane. (`pressurePlaneFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressurePlaneFlip.lean#L199)).

### Breakdown.CertCell.PressureStripFlipLinks

Transfer pressure reflection through weak line traces and weighted strip moments. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Integrability of a weak derivative pair.** Proved result. Under the declaration's hypotheses, both the function and its weak derivative are integrable on the closed interval. (`weak_integrableOn_Icc`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureStripFlipLinks.lean#L17)).

**weak derivative is interval integrable.** Proved result. Under the declaration's hypotheses, the weak derivative is interval integrable between the two ordered endpoints. (`weak_intervalIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureStripFlipLinks.lean#L25)).

**Split the weak endpoint trace.** Proved result. Under the declaration's hypotheses, the oriented endpoint trace is the orientation sign times the sum of the interval average of the function and the linearly weighted integral of its weak derivative. (`sideTrace_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureStripFlipLinks.lean#L31)).

**Bound a weighted derivative integral.** Proved result. If the affine endpoint weight has absolute value at most one on the interval, the norm of its derivative pairing is at most the integral of the derivative norm. (`weighted_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureStripFlipLinks.lean#L39)).

**Reflected weak traces agree on the plane.** Proved result. Under the declaration's hypotheses, the reflection-related weak endpoint traces at height zero agree even when defined using different admissible opposite endpoints. (`line_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureStripFlipLinks.lean#L48)).

**Weighted strip pairings are integrable.** Proved result. Under the declaration's hypotheses, the strip coefficient multiplied by the radial weight and test polynomial is integrable on the strip rectangle. (`weighted_strip_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureStripFlipLinks.lean#L122)).

**Pressure strips respect reflection.** Proved result. For a weak potential with locally square-integrable reflection-compatible gradient and admissible tests, opposite angular modes have equal pressure strip moments on the equatorial plane, including with different positive auxiliary heights. (`pressureStripFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/PressureStripFlipLinks.lean#L142)).

### Breakdown.CertCell.RadialStripTrace

Close the interface identifying weak radial strip traces. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Weak radial traces give strip moments.** Proved result. The radial weak trace supplies the stated strip-moment identity. (`radialStripTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RadialStripTrace.lean#L15)).

### Breakdown.CertCell.RotationAverage

Justify rotation averaging using measure preservation of axial rotations. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Axial rotation preserves volume.** Proved result. Every fixed axial rotation preserves spatial Lebesgue measure. (`measurePreserving_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RotationAverage.lean#L17)).

**Axial rotation is a measurable embedding.** Proved result. Every fixed axial rotation is a measurable embedding. (`measurableEmbedding_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RotationAverage.lean#L24)).

**Rotation orbits preserve null sets.** Proved result. The joint map taking a spatial point and an angle to the rotated point pulls spatial null sets back to product-measure null sets. (`quasiMeasurePreserving_axialRot_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RotationAverage.lean#L30)).

**Rotation averages preserve integrals.** Proved result. The integral of a nonnegative almost everywhere measurable spatial function equals the integral of its normalized angular rotation average. (`rotationAverage`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RotationAverage.lean#L49)).

### Breakdown.CertCell.RowCouplingLow

Expand the low-mode coupling integral into the finite strain and velocity rows. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Split strain and velocity coupling.** Proved result. The radius-weighted curl coupling separates into coefficients multiplying the gradient entries and coefficients multiplying the velocity entries, expressed through the alternating symbol. (`low_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L19)).

**The radial axis is a null set.** Proved result. The first coordinate is nonzero almost everywhere for planar Lebesgue measure. (`fst_ne_zero_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L29)).

**A radial factor removes the singularity.** Proved result. Under the declaration's hypotheses, multiplying the specified component by the radius agrees off the axis with a continuous function on the plane. (`weighted_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L35)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L69)).

**Cell rectangle is measurable.** Proved result. The cell rectangle is a measurable set. (`rect_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L71)).

**Positive cell radius almost everywhere.** Proved result. Under the declaration's hypotheses, almost every point in a valid cell rectangle has strictly positive radius. (`ae_rect_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L73)).

**Polynomial value is continuous.** Proved result. For a fixed cell and complex polynomial coefficients, evaluating the polynomial in the cell's affine radial and height coordinates gives a continuous function on R². (`eval_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L77)).

**Cell basis value is continuous.** Proved result. The tensor-product cell basis value is continuous. (`basis_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L81)).

**strain coupling integrand is integrable.** Proved result. Under the declaration's hypotheses, the radius-weighted strain-basis term contracted with the background velocity and conjugate test through alternating tensors is integrable on the cell. (`strain_term_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L85)).

**A bounded cell function is integrable.** Proved result. Under the declaration's hypotheses, a measurable function with the stated bound is integrable on the compact cell rectangle. (`bounded_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L103)).

**Integrability of the velocity coupling.** Proved result. Under the declaration's hypotheses, the radius-weighted velocity-basis term paired with the background vorticity and conjugate test is integrable on the cell. (`velocity_term_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L109)).

**Combine real harmonic coefficients.** Proved result. Under the declaration's hypotheses, the complex coefficient is the cosine coefficient plus i times the sine coefficient, and the lifted weighted function is integrable on the cell. (`coef_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L134)).

**Integrate a finite sum term by term.** Proved result. Under the declaration's hypotheses, the integral of a finite family of integrable functions over a set equals the sum of their integrals. (`int_fsum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L158)).

**Low coupling as a finite row.** Proved result. Under the declaration's hypotheses, the low coupling test pairing is the sum of strain and velocity basis coefficients multiplied by their corresponding coupling row entries. (`pairing_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L162)).

**A single supported mode determines a sum.** Proved result. Under the declaration's hypotheses, a finite sum supported on one selected mode equals the prescribed value at that mode. (`sum_single_mode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L250)).

**Low coupling equals its finite row.** Proved result. Under the hypotheses of this declaration, the low-mode coupling pairing equals the corresponding finite strain and velocity row. (`rowCouplingLow_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowCouplingLow.lean#L261)).

### Breakdown.CertCell.RowLowPart

Close the interface identifying the finite low row with its volume and boundary expression. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The low row equals its physical pairing.** Proved result. Under the hypotheses of this declaration, the finite low row equals the volume term minus the gradient boundary term plus the pressure boundary term. (`rowLowPart_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPart.lean#L14)).

### Breakdown.CertCell.RowLowPartBasis

Expand polynomial tests in the triangular one-dimensional and tensor-product cell bases. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A triangular polynomial basis term.** Definition. Form the degree-indexed polynomial from its lower-triangular real coefficient array. (`triPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L17)).

**Span of the first basis polynomials.** Definition. Take the complex linear span of the basis terms below the degree cutoff. (`triSpan`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L19)).

**Triangular polynomial is continuous.** Proved result. The triangular basis polynomial is continuous. (`triPoly_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L22)).

**Polynomial basis spans are increasing.** Proved result. Under the declaration's hypotheses, increasing the number of triangular basis polynomials enlarges their linear span. (`triSpan_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L26)).

**A retained basis term lies in its span.** Proved result. Under the declaration's hypotheses, a basis polynomial below the cutoff belongs to the span of the retained basis terms. (`triPoly_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L31)).

**Monomials lie in the initial basis span.** Proved result. Under the declaration's hypotheses, the monomial of degree n lies in the span of the first n plus one triangular basis polynomials. (`pow_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L34)).

**Basis coefficients from span membership.** Proved result. Under the declaration's hypotheses, a function in the span of the first N triangular basis polynomials has a finite expansion using those polynomials. (`expand_of_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L52)).

**Monomials expand in the triangular basis.** Proved result. Under the declaration's hypotheses, a monomial of degree below the basis cutoff has a finite expansion in the first triangular basis polynomials. (`pow_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L61)).

**Triangular expansions of polynomials.** Proved result. Under the declaration's hypotheses, a polynomial function within the degree cutoff has a finite expansion in the first triangular basis polynomials. (`poly_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L65)).

**Extract one orthonormal coefficient.** Proved result. Under the declaration's hypotheses, integrating a finite weighted basis expansion against its indexed orthonormal basis function recovers that coefficient. (`coef_extract`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L78)).

**Cast a real zero-one selector to complex.** Proved result. Casting a real selector with values zero and one to the complex numbers preserves the selector. (`ofReal_ite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L97)).

**Cell weight is continuous.** Proved result. The cell integration weight is continuous. (`lineWeight_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L100)).

**The cell basis is a product basis.** Proved result. The cell basis value is the product of the radial and height triangular polynomials. (`basisValue_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L106)).

**Cell basis value is continuous.** Proved result. The tensor-product cell basis value is continuous. (`basisValue_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L112)).

**Cell basis products are orthonormal.** Proved result. Under the declaration's hypotheses, the cell-weighted integral of two tensor-product basis functions is one when both indices agree and zero otherwise. (`cell_orthonormal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L118)).

**Extract a cell expansion coefficient.** Proved result. Under the declaration's hypotheses, pairing a finite cell-basis expansion with a basis function using the cell weight recovers its coefficient. (`cell_extract`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L138)).

**Expand a polynomial in the cell basis.** Proved result. A polynomial with the stated degree cutoffs equals its weighted cell-basis expansion. (`cellBasisExpansion`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L156)).

**Expand a polynomial in segment tests.** Proved result. A polynomial below the cutoff equals its orthonormal segment-test expansion. (`segmentTestExpansion`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasis.lean#L205)).

### Breakdown.CertCell.RowLowPartBasisDefs

Name the polynomial classes and the segment and cell basis-expansion interfaces needed for the low row. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Separate polynomial degree bounds.** Proposition definition. Require a finite monomial expansion with radial degree below M and height degree below N. (`IsBivariatePoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasisDefs.lean#L15)).

**A strict polynomial degree cutoff.** Proposition definition. Require a monomial expansion using only powers below N. (`IsUnivariatePoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasisDefs.lean#L19)).

**Expansion in segment test polynomials.** Interface. This interface requires every polynomial below the cutoff to equal its orthonormal segment-test expansion. (`SegmentTestExpansionStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasisDefs.lean#L22)). Proof route: `Breakdown.CertCell.CellCalculus.segmentTestExpansion`.

**Expansion in the weighted cell basis.** Interface. This interface requires a polynomial of the stated separate degree bounds to equal its weighted tensor-basis expansion. (`CellBasisExpansionStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBasisDefs.lean#L29)). Proof route: `Breakdown.CertCell.CellCalculus.cellBasisExpansion`.

### Breakdown.CertCell.RowLowPartBoundary

Recombine real harmonic pressure blocks and prove cancellation of the constant-pressure flux. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The conjugate boundary flux.** Definition. Combine the four oriented face integrals of the conjugated test with the cylindrical radial weight. (`fluxConj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L11)).

**Integrate a height-only function.** Proved result. Under the declaration's hypotheses, the rectangle integral of a function depending only on height is the radial width times its height integral. (`rect_const_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L17)).

**Integrate a radius-only function.** Proved result. Under the declaration's hypotheses, the rectangle integral of a radius-weighted function depending only on radius is the height width times its radial integral. (`rect_const_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L26)).

**Combine radial pressure components.** Proved result. Under the declaration's hypotheses, combining the cosine and sine radial pressure integrals gives the complex pressure integral with the constant gauge contribution subtracted. (`radial_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L36)).

**Combine height pressure components.** Proved result. Under the declaration's hypotheses, combining the cosine and sine radius-weighted height pressure integrals gives the complex pressure integral with the constant gauge contribution subtracted. (`height_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L57)).

**Radial pressure boundary and gauge.** Proved result. Under the declaration's hypotheses, the complex radial pressure side contribution equals its oriented radius-weighted trace pairing minus the corresponding constant gauge pairing. (`radial_pres_side_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L86)).

**An interval ratio gives the orientation.** Proved result. Under the declaration's hypotheses, the interval length divided by the oriented endpoint difference is the weak-trace orientation sign. (`edge_factor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L130)).

**Height pressure boundary and gauge.** Proved result. Under the declaration's hypotheses, the complex height pressure side contribution equals its oriented radius-weighted trace pairing minus the corresponding constant gauge pairing. (`height_pres_side_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L144)).

**Group pressure segments by their faces.** Proved result. The sum over all pressure segments equals the sum over the four faces of the segments assigned to each face. (`sum_presFiber`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L172)).

**Cell integrability with radial weights.** Proved result. Under the declaration's hypotheses, multiplying an integrable cell function by its radial coordinate preserves integrability on the cell rectangle. (`w_int_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L176)).

**Assemble four pressure face integrals.** Proved result. Under the declaration's hypotheses, the sum of the pressure row moments equals the two radial and two height face integrals with their cylindrical weights and conjugate normal test components. (`pres_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L180)).

**Pressure moments give the boundary row.** Proved result. Under the declaration's hypotheses, the pressure row paired with the complex combination of cosine and sine pressure moments equals the pressure boundary contribution. (`pres_block`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L225)).

**Constant pressure contributes zero flux.** Proved result. Under the declaration's hypotheses, the conjugate boundary flux of the admissible divergence-free test is zero. (`flux_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartBoundary.lean#L300)).

### Breakdown.CertCell.RowLowPartCore

Assemble the volume, gradient-boundary and pressure-boundary pieces of the low row. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**full low row matches its field pairing.** Proved result. Under the declaration's hypotheses, the volume term minus the gradient boundary term plus the pressure boundary term equals the own-row evaluation on harmonic field data. (`rowLow_core`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartCore.lean#L11)).

**Equivalent profiles give equal low rows.** Proved result. Under the declaration's hypotheses, the specified agreement of two profiles preserves their combined volume and boundary pairing. (`transfer_profile`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartCore.lean#L109)).

**The low row equals its physical pairing.** Proved result. For a periodic second-order field, the finite low row equals the volume term minus the gradient boundary term plus the pressure boundary term. (`rowLowPart_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartCore.lean#L151)).

### Breakdown.CertCell.RowLowPartLift

Lift real cosine and sine cell data to complex harmonic rows and verify integrability of each block. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Split the eight datum families.** Proved result. A sum over the cell datum type separates into sums over its eight constituent index families. (`datum_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L13)).

**Only four datum blocks enter the own row.** Proved result. The own-row evaluation splits into its strain, velocity, side-gradient and side-pressure coordinate sums. (`own_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L23)).

**The cell fits in its enclosing strip.** Proved result. Under the declaration's hypotheses, the cell rectangle is contained in the strip extending from radius zero to its outer radius. (`rect_sub_strip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L36)).

**The cell fits in a symmetric height box.** Proved result. Under the declaration's hypotheses, the cell rectangle is contained in the stated bounded box with symmetric height limits. (`rect_sub_square`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L40)).

**Cell rectangle is measurable.** Proved result. The cell rectangle is a measurable set. (`rect_meas`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L47)).

**Weighted cell Hessian integrability.** Proved result. Under the declaration's hypotheses, each Hessian mode multiplied by radius is integrable on the cell rectangle. (`third_weighted_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L49)).

**Gradient modes integrate on cells.** Proved result. Under the declaration's hypotheses, every local gradient Fourier coefficient is integrable on the cell rectangle. (`grad_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L62)).

**Velocity modes integrate on cells.** Proved result. Under the declaration's hypotheses, every local velocity Fourier coefficient is integrable on the cell rectangle. (`vel_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L67)).

**Recover the lattice label from its time.** Proved result. Decoding the temporal label and angular integer back into a harmonic mode recovers the original lattice label. (`harmonicMode_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L73)).

**A lattice label has the required parity.** Proved result. The angular label plus its decoded time label is even. (`even_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L82)).

**Positive radius holds almost everywhere.** Proved result. Under the declaration's hypotheses, almost every point in a valid cell rectangle has strictly positive radius. (`ae_rect_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L86)).

**Complex modes split into cosine and sine.** Proved result. Under the declaration's hypotheses, almost everywhere on the cell, the labelled velocity, gradient and Hessian modes equal their cosine modes plus i times their sine modes. (`lift_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L91)).

**Lift the pressure-gradient harmonics.** Proved result. Under the declaration's hypotheses, almost everywhere on the cell, the labelled pressure-gradient mode equals its cosine mode plus i times its sine mode. (`pres_lift_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L106)).

**Cell integrability of gradient modes.** Proved result. The labelled plane gradient mode is integrable on the cell rectangle. (`gradAt_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L124)).

**Cell integrability of velocity modes.** Proved result. The labelled plane velocity mode is integrable on the cell rectangle. (`velAt_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L130)).

**Integrable weighted labelled Hessians.** Proved result. The labelled plane Hessian mode multiplied by radius is integrable on the cell rectangle. (`slopeAt_w_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L136)).

**Cell-weighted gradient modes integrate.** Proved result. The labelled gradient mode multiplied by the cell line weight is integrable on the cell rectangle. (`lw_gradAt_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L145)).

**Cell-weighted velocity modes integrate.** Proved result. The labelled velocity mode multiplied by the cell line weight is integrable on the cell rectangle. (`lw_velAt_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L154)).

**Cell modes of the chosen potential.** Proved result. Under the declaration's hypotheses, the pressure Fourier mode of the chosen weak potential is integrable on the cell rectangle. (`pres_int_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L170)).

**Cell integrability of pressure modes.** Proved result. The labelled pressure mode is integrable on the cell rectangle. (`labelPressure_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L177)).

**Integrable weighted pressure gradients.** Proved result. The labelled velocity transform of the pressure-gradient field, multiplied by radius, is integrable on the cell rectangle. (`presVel_w_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L182)).

**Constant shifts of pressure modes.** Proved result. Under the declaration's hypotheses, almost everywhere on the plane, subtracting a constant from the potential subtracts that constant times the Fourier mode of the unit function from the pressure mode. (`presMode_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L193)).

**A nonzero pressure mode kills constants.** Proved result. Under the nonzero-mode hypothesis, the Fourier coefficient of the constant pressure function is zero. (`presMode_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartLift.lean#L213)).

### Breakdown.CertCell.RowLowPartPoly

Track polynomial degrees of test fields and absorb the radial weight into the low-row basis. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Polynomial cutoffs can be increased.** Proved result. Under the declaration's hypotheses, increasing the two degree cutoffs preserves the bivariate polynomial condition. (`bi_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L11)).

**Addition preserves polynomial cutoffs.** Proved result. Under the declaration's hypotheses, adding two functions with the same separate polynomial degree cutoffs preserves those cutoffs. (`bi_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L37)).

**Scalar multiplication preserves cutoffs.** Proved result. Under the declaration's hypotheses, multiplying a polynomial function by a constant preserves its separate degree cutoffs. (`bi_const_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L48)).

**A radial factor raises one degree cutoff.** Proved result. Under the declaration's hypotheses, multiplication by the first coordinate raises the radial cutoff by one and keeps the height cutoff. (`bi_mul_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L58)).

**A height factor raises one degree cutoff.** Proved result. Under the declaration's hypotheses, multiplication by the second coordinate raises the height cutoff by one and keeps the radial cutoff. (`bi_mul_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L69)).

**Zero satisfies every polynomial cutoff.** Proved result. The zero function satisfies the stated separate polynomial degree cutoffs. (`bi_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L80)).

**A polynomial test is differentiable.** Proved result. Under the declaration's hypotheses, a function with the specified finite bivariate polynomial expansion is continuously differentiable. (`bi_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L83)).

**radial slice derivative is radialDeriv.** Proved result. Under the declaration's hypotheses, the one-variable derivative of a fixed-height slice is the defined radial derivative. (`hasDerivAt_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L93)).

**height slice derivative is heightDeriv.** Proved result. Under the declaration's hypotheses, the one-variable derivative of a fixed-radius slice is the defined height derivative. (`hasDerivAt_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L99)).

**Read the radial Fréchet direction.** Proved result. Under the declaration's hypotheses, the radial derivative equals the Fréchet derivative applied to the first planar unit vector. (`radialDeriv_eq_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L105)).

**Read the height Fréchet direction.** Proved result. Under the declaration's hypotheses, the height derivative equals the Fréchet derivative applied to the second planar unit vector. (`heightDeriv_eq_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L112)).

**The radial derivative is continuous.** Proved result. Under the declaration's hypotheses, the radial partial derivative of the continuously differentiable plane function is continuous. (`continuous_radialDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L119)).

**The height derivative is continuous.** Proved result. Under the declaration's hypotheses, the height partial derivative of the continuously differentiable plane function is continuous. (`continuous_heightDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L124)).

**Differentiate a complex-cast real power.** Proved result. The derivative of the complex cast of the ith real power is i times the power with exponent reduced by one. (`ofReal_pow_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L129)).

**A height slice keeps its degree cutoff.** Proved result. Under the declaration's hypotheses, fixing the radial coordinate of a bivariate polynomial leaves the stated height polynomial cutoff. (`bi_slice_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L135)).

**A radial slice keeps its degree cutoff.** Proved result. Under the declaration's hypotheses, fixing the height coordinate of a bivariate polynomial leaves the stated radial polynomial cutoff. (`bi_slice_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L144)).

**Radial differentiation preserves cutoffs.** Proved result. Under the declaration's hypotheses, the radial derivative retains the stated, possibly nonminimal, separate polynomial degree cutoffs. (`bi_radialDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L154)).

**Height differentiation preserves cutoffs.** Proved result. Under the declaration's hypotheses, the height derivative retains the stated, possibly nonminimal, separate polynomial degree cutoffs. (`bi_heightDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L178)).

**Factor out a vanishing radial coordinate.** Proved result. Under the declaration's hypotheses, a polynomial satisfying the stated zero-axis condition can be factored by the first coordinate with the recorded degree cutoffs. (`bi_div_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L204)).

**Gradient plus drift test coefficient.** Definition. Add half the frame weight times the test component to the test gradient. (`gTot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L238)).

**Test components have separate cutoffs.** Proved result. Under the declaration's hypotheses, the test components satisfy the recorded separate degree cutoffs, with sharper cutoffs for the radial and axial components. (`shape_polys`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L241)).

**Subtraction preserves polynomial cutoffs.** Proved result. Under the declaration's hypotheses, subtracting two functions with the same separate polynomial degree cutoffs preserves those cutoffs. (`bi_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L270)).

**The angular test preserves its cutoff.** Proved result. Under the declaration's hypotheses, the cylindrical angular transformation of the test has the stated separate polynomial degree cutoffs. (`turn_poly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L275)).

**The axis cell uses radial weight.** Proved result. For a cell whose inner radius is zero, the line weight is the radial coordinate. (`lw_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L284)).

**An off-axis cell has unit line weight.** Proved result. For a cell with nonzero inner radius, the line weight is one. (`lw_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L287)).

**Radial weights in velocity tests.** Proved result. Under the declaration's hypotheses, the radially weighted velocity test can be written as the cell line weight times a polynomial below the two Q cutoffs. (`vel_shape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L290)).

**Radial weights in strain tests.** Proved result. Under the declaration's hypotheses, on the cell, the radially weighted gradient-drift test is the line weight times a polynomial below the two Q plus one cutoffs. (`strain_shape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPoly.lean#L297)).

### Breakdown.CertCell.RowLowPartPressure

Group pressure and gradient segments by cell side and convert their moments into boundary terms. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Pressure segments on one cell side.** Definition. Select pressure segments whose side index is the specified cell side. (`presFiber`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L15)).

**Pressure segments on radial faces.** Proved result. Under the declaration's hypotheses, a pressure segment assigned to a radial face is radial, lies at that face with the opposite radial endpoint, and has height endpoints within the cell. (`pres_radial_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L18)).

**Pressure segments on height faces.** Proved result. Under the declaration's hypotheses, a pressure segment assigned to a height face is axial, lies at that face with the opposite height endpoint, and has radial endpoints within the cell. (`pres_height_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L40)).

**Pressure moments on one radial side.** Proved result. Under the declaration's hypotheses, the pressure row moments on a radial side sum to the side radius times the radial weak-trace integral paired with the conjugate radial test component. (`pres_radial_side`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L62)).

**Pressure moments on one height side.** Proved result. Under the declaration's hypotheses, the pressure row moments on a height side sum to the radius-weighted height weak-trace integral paired with the conjugate axial test component. (`pres_height_side`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L149)).

**Expand the radial vector trace pairing.** Proved result. Under the declaration's hypotheses, the radial boundary pairing equals the side radius and orientation sign times the sum of componentwise rectangle weak-trace pairings. (`radial_bdry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L225)).

**Expand the height vector trace pairing.** Proved result. Under the declaration's hypotheses, the height boundary pairing equals the orientation sign times the sum of radius-weighted componentwise rectangle weak-trace pairings. (`height_bdry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L242)).

**Ordered endpoints have opposite signs.** Proved result. Under the declaration's hypotheses, the lower endpoint has orientation sign minus one and the upper endpoint has sign plus one. (`edgeSign_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L268)).

**Gradient moments give the boundary row.** Proved result. Under the declaration's hypotheses, the sum of side-gradient row coefficients times the corresponding normal trace moments equals minus the gradient boundary contribution. (`grad_block`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartPressure.lean#L272)).

### Breakdown.CertCell.RowLowPartSegment

Express segment moments as strip integrals and sum them along each radial or height side. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The radial weak trace integrand.** Definition. Combine the field and radial derivative with the affine weights for a weak endpoint trace. (`radialIntegrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L12)).

**The height weak trace integrand.** Definition. Combine the field and height derivative with the affine weights for a weak endpoint trace. (`heightIntegrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L15)).

**Radial trace moment as an area integral.** Proved result. A radial strip moment is the orientation sign times the weak radial trace integrand integrated over the strip rectangle against its height test. (`radialStripMoment_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L18)).

**Height trace moment as an area integral.** Proved result. A height strip moment is the orientation sign times the weak height trace integrand integrated over the strip rectangle against its weighted radial test. (`heightStripMoment_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L22)).

**Endpoint signs have square one.** Proved result. The weak-trace orientation sign squares to one when the two endpoints differ. (`edgeSign_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L27)).

**Reconstruct a radial segment pairing.** Proved result. Under the declaration's hypotheses, the finite sum of gradient moments times conjugate test moments equals the oriented radial strip integral paired with the conjugate boundary polynomial. (`grad_seg_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L31)).

**Reconstruct a height segment pairing.** Proved result. Under the declaration's hypotheses, the finite sum of gradient moments times conjugate test moments equals the oriented radius-weighted height strip integral paired with the conjugate boundary polynomial. (`grad_seg_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L58)).

**Remove radius weights off the axis.** Proved result. Under the declaration's hypotheses, a function whose radius multiple is integrable on a cell separated from the axis is itself integrable there. (`int_div_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L92)).

**The radial trace integrand is integrable.** Proved result. Under the declaration's hypotheses, the weak radial trace integrand is integrable on the cell rectangle. (`radialIntegrand_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L103)).

**Integrability of weighted height traces.** Proved result. Under the declaration's hypotheses, the weak height trace integrand multiplied by radius is integrable on the cell rectangle. (`heightIntegrand_w_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L117)).

**Integrate a weighted radial trace.** Proved result. Under the declaration's hypotheses, the weighted radial-face trace is integrable along height, and its integral is the oriented rectangle integral of the radial trace integrand with the same weight. (`trace_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L128)).

**Integrate a weighted height trace.** Proved result. Under the declaration's hypotheses, the radius-weighted height-face trace is integrable along radius, and its integral is the oriented rectangle integral of the weighted height trace integrand. (`trace_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L149)).

**Identify one of the four cell sides.** Definition. Classify a segment by its radial or height orientation and whether it lies at the lower endpoint. (`segSide`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L179)).

**A side segment decodes to its side.** Proved result. Under the declaration's hypotheses, a segment stored on a given cell side is classified as that same side. (`segSide_of_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L186)).

**The side fibre is the stored segment set.** Proved result. Under the declaration's hypotheses, filtering all segments by their decoded side gives exactly the stored segments for that side. (`segSide_fiber`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L202)).

**Geometry of a radial face segment.** Proved result. Under the declaration's hypotheses, a radial-face segment lies at the corresponding nonzero cell radius, uses the opposite radial endpoint, and has height endpoints inside the cell. (`seg_radial_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L214)).

**Geometry of a height face segment.** Proved result. Under the declaration's hypotheses, a height-face segment lies at the corresponding cell height, uses the opposite height endpoint, and has radial endpoints inside the cell. (`seg_height_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L228)).

**Recover the ordered pair of endpoints.** Proved result. If c is one endpoint of the interval, the minimum and maximum of c and the opposite endpoint recover the interval bounds. (`minmax_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L252)).

**Assemble a radial gradient side.** Proved result. Under the declaration's hypotheses, the gradient row contributions from all segments of a radial side equal minus the side radius times the sum of componentwise rectangle weak-trace pairings. (`grad_radial_side`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L260)).

**Assemble a height gradient side.** Proved result. Under the declaration's hypotheses, the gradient row contributions from all segments of a height side equal minus the sum of radius-weighted componentwise rectangle weak-trace pairings. (`grad_height_side`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartSegment.lean#L331)).

### Breakdown.CertCell.RowLowPartStrip

Use rectangle integration and polynomial basis expansion to turn finite moments into volume and boundary integrals. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Product measure on a rectangle.** Proved result. Restricted planar volume on a rectangle is the product of the two restricted line measures. (`rect_restrict`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L11)).

**Integrate height after radius.** Proved result. Under the declaration's hypotheses, an integrable function on a product rectangle can be integrated first over radius and then over height. (`rect_iter_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L15)).

**Integrate radius after height.** Proved result. Under the declaration's hypotheses, an integrable function on a product rectangle can be integrated first over height and then over radius. (`rect_iter_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L21)).

**Continuous functions integrate on cells.** Proved result. Under the declaration's hypotheses, a continuous function is integrable on any compact closed rectangle. (`cont_int_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L27)).

**Derivative integrals give endpoint jumps.** Proved result. Under the declaration's hypotheses, the integral of the derivative over the ordered closed interval equals the value at the upper endpoint minus the value at the lower endpoint. (`icc_ftc`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L31)).

**Radial derivative gives two face values.** Proved result. Under the declaration's hypotheses, integrating a radial derivative over a rectangle gives the height integral of the difference between its two radial face values. (`rect_ftc_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L36)).

**Height derivative gives two face values.** Proved result. Under the declaration's hypotheses, integrating a height derivative over a rectangle gives the radial integral of the difference between its two height face values. (`rect_ftc_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L44)).

**Smooth radial traces are pointwise.** Proved result. For a smooth function, its weak radial strip moment equals the height integral of its value on the selected radial face against the test. (`radialStrip_of_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L52)).

**Smooth height traces are pointwise.** Proved result. For a smooth function, its weak height strip moment equals the radial integral of its value on the selected height face against the weighted test. (`heightStrip_of_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L89)).

**Segment polynomial tests are continuous.** Proved result. Every segment test polynomial is continuous as a function of its line coordinate. (`test_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L127)).

**Cell basis value is continuous.** Proved result. The tensor-product cell basis value is continuous. (`basisValue_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L131)).

**Cell basis values are real.** Proved result. Complex conjugation leaves the tensor-product cell basis value unchanged. (`conj_basisValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L135)).

**Reconstruct a polynomial height pairing.** Proved result. Under the declaration's hypotheses, the finite sum of coefficient pairings in the segment basis equals the rectangle pairing with the conjugate height polynomial. (`seg_expand_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L140)).

**Reconstruct a polynomial radial pairing.** Proved result. Under the declaration's hypotheses, the finite sum of coefficient pairings in the segment basis equals the rectangle pairing with the conjugate radial polynomial. (`seg_expand_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L167)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L194)).

**Reconstruct a cell polynomial pairing.** Proved result. Under the declaration's hypotheses, the finite sum of products of cell coefficients and conjugate test coefficients equals their weighted cell pairing. (`cell_expand_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartStrip.lean#L196)).

### Breakdown.CertCell.RowLowPartVolume

Identify the strain and velocity blocks of the finite row with the physical volume pairing. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Frame weights are real.** Proved result. Complex conjugation leaves each cylindrical frame weight unchanged. (`conj_frameWeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L11)).

**strain integrand is a conjugate product.** Proved result. The strain-row integrand is the conjugate of the radially weighted gradient-drift coefficient times the real cell basis. (`strain_row_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L15)).

**Bounded sums as natural-number sums.** Proved result. A double sum over two finite index types equals the double sum over the corresponding natural-number ranges. (`sum_fin_range2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L25)).

**Cell rows recover complex pairings.** Proved result. Under the declaration's hypotheses, a finite cell row applied to the combined cosine and sine coefficients equals the weighted integral of their complex combination against the conjugate test. (`cell_block`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L30)).

**Separate gradient and velocity terms.** Proved result. The cylindrical volume integrand splits into a gradient pairing against the gradient-plus-drift test and a velocity pairing multiplied by one half plus the imaginary temporal frequency. (`volume_point`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L58)).

**A singleton mode removes the mode sum.** Proved result. When the mode set contains only one mode, summing over mode-data pairs reduces to summing the data indices at that mode. (`sum_modes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L70)).

**Read the low-strain harmonic datum.** Proved result. The low-strain datum is the cosine gradient coefficient plus i times its sine gradient coefficient. (`data_lowStrain`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L85)).

**Read the low-velocity harmonic datum.** Proved result. The low-velocity datum is the cosine velocity coefficient plus i times its sine velocity coefficient. (`data_lowVelocity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L91)).

**Read the side-pressure harmonic datum.** Proved result. The side-pressure datum combines cosine and sine weighted pressure moments into one complex value. (`data_sidePressure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L97)).

**Normalize the cosine pressure potential.** Proved result. The cosine pressure mode uses the cosine gradient's potential after subtracting its real gauge normalization. (`pressMode_cos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L105)).

**Normalize the sine pressure potential.** Proved result. The sine pressure mode uses the sine gradient's potential after subtracting its real gauge normalization. (`pressMode_sin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L109)).

**Read the cosine pressure-gradient mode.** Proved result. The pressure-gradient datum of the cosine field tuple is the local mode of the cosine pressure gradient. (`pgm_cos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L113)).

**Read the sine pressure-gradient mode.** Proved result. The pressure-gradient datum of the sine field tuple is the local mode of the sine pressure gradient. (`pgm_sin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L116)).

**Strain rows recover the gradient pairing.** Proved result. Under the declaration's hypotheses, the strain block of harmonic field data evaluates to the sum of weighted cell pairings of gradient-mode entries with their conjugate test coefficients. (`strain_block_data`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L125)).

**Velocity rows recover the drift pairing.** Proved result. Under the declaration's hypotheses, the velocity block evaluates to the weighted velocity-mode test pairing multiplied by one half plus the imaginary temporal frequency. (`vel_block_data`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L155)).

**Volume row splits into two pairings.** Proved result. Under the declaration's hypotheses, the volume row equals the gradient test pairing plus the velocity test pairing multiplied by one half plus the imaginary temporal frequency. (`volume_data`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowLowPartVolume.lean#L206)).

### Breakdown.CertCell.RowProfileDefs

Define the strip traces and complex harmonic profile that the low-row calculation evaluates. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A weak trace on a radial face.** Definition. Integrate the affine weak-trace formula in the radial variable with the orientation sign. (`radialStripTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowProfileDefs.lean#L15)).

**A weak trace on a height face.** Definition. Integrate the affine weak-trace formula in the height variable with the orientation sign. (`heightStripTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowProfileDefs.lean#L19)).

**The opposite radial endpoint.** Definition. Select the radial endpoint opposite the chosen face. (`otherRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowProfileDefs.lean#L23)).

**The opposite height endpoint.** Definition. Select the height endpoint opposite the chosen face. (`otherHeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowProfileDefs.lean#L25)).

**Pressure at a harmonic label.** Definition. Combine cosine and sine pressure potentials into the pressure mode indexed by the harmonic label. (`labelPressure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowProfileDefs.lean#L27)).

**The harmonic row profile.** Definition. Collect the harmonic velocity, gradient, pressure and boundary-trace data in one row profile. (`labelRowProfile`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowProfileDefs.lean#L31)).

### Breakdown.CertCell.RowSharesInstance

Preserve pairing under reflection averaging and show that the represented row fields have the required square integrability. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Reflection preserves vector addition.** Proved result. The reflection of a sum of spatial vectors is the sum of their reflections. (`flipPoint_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L20)).

**Reflection commutes with real scaling.** Proved result. The reflection of a real scalar multiple is the same scalar multiple of the reflected vector. (`flipPoint_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L23)).

**Reflection moves across an inner product.** Proved result. The real inner product of a reflected first vector with a second vector equals the inner product of the first vector with the reflected second vector. (`inner_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L26)).

**Reflection preserves volume.** Proved result. The spatial reflection preserves Lebesgue measure. (`flip_measurePreserving`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L31)).

**Reflection is a measurable embedding.** Proved result. The spatial reflection is a measurable embedding. (`flip_measurableEmbedding`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L34)).

**The equatorial plane has measure zero.** Proved result. The set of spatial points with zero height has Lebesgue measure zero. (`plane_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L37)).

**Almost every point avoids the plane.** Proved result. The height coordinate is nonzero almost everywhere for the measure specified in this declaration. (`ae_off_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L48)).

**Averages enforce reflection symmetry.** Proved result. The reflection average at a reflected spatial point is the reflection of its value at the original point. (`flipAverage_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L51)).

**Periodic reflection averages.** Proved result. Under the declaration's hypotheses, the reflection average of a time-periodic field is time-periodic. (`flipAverage_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L57)).

**Bound the reflected average energy.** Proved result. The squared norm of the average of a vector and a reflected vector is at most the sum of their squared norms. (`norm_sq_average_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L63)).

**Restrict measurability to a period slab.** Proved result. Under the declaration's hypotheses, an almost everywhere strongly measurable spacetime field remains so for the product of the restricted unit-time measure and spatial Lebesgue measure. (`restrict_prod_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L74)).

**Most time slices are measurable.** Proved result. Under the declaration's hypotheses, almost every time slice in one period is almost everywhere strongly measurable in space. (`ae_slice_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L81)).

**Most time slices are square integrable.** Proved result. Under the declaration's hypotheses, almost every time slice in one period belongs to the spatial L² space. (`ae_slice_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L86)).

**Reflection average is a.e. measurable.** Proved result. Under the hypotheses of this declaration, the reflection-averaged field is almost everywhere strongly measurable for the stated measure. (`flipAverage_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L101)).

**Finite energy of reflection averages.** Proved result. Under the declaration's hypotheses, the squared norm of the reflection-averaged field has finite nonnegative integral over one time period and all space. (`flipAverage_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L113)).

**Reflection averaging preserves a pairing.** Proved result. Under the declaration's hypotheses, pairing a field averaged with its reflected copy against a reflection-compatible test gives the original spatial pairing. (`slice_pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L138)).

**Reflection averages preserve pairings.** Proved result. Under the declaration's hypotheses, pairing the reflection-averaged field with a reflection-compatible test over one period gives the original pairing. (`pairing_flipAverage`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L163)).

**Generator labels are reflection closed.** Proved result. Reflecting any generator label gives another label of that generator in the cell. (`generator_labels_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L173)).

**Row fields reflect almost everywhere.** Proved result. Almost everywhere in space, the row field at the reflected point equals the reflection of its original value. (`rowField_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L184)).

**Row fields have square-integrable slices.** Proved result. Under the declaration's hypotheses, almost every time slice of the represented row field belongs to the spatial L² space. (`rowField_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L196)).

**Instance row shares have valid fields.** Proved result. Under the hypotheses of this declaration, the represented instance row shares have the required pairing and regularity properties. (`rowSharesOfInstance_of_regular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowSharesInstance.lean#L207)).

### Breakdown.CertCell.RowsMatchAssemble

Reduce row-field agreement to the key, split, flux, derived and normal row cases. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Expand a row evaluation in coordinates.** Proved result. A row value is the finite sum of complex row entries multiplied by the corresponding real field coordinates embedded in the complex numbers. (`rowValue_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L19)).

**Read real and imaginary coordinates.** Proved result. A complex-part row with both coordinates present returns the real coordinate plus the imaginary coordinate times i, with the sign of i reversed when conjugation is selected. (`sum_partVec_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L26)).

**Read a lone real coordinate.** Proved result. A complex-part row with only its real coordinate present returns that coordinate. (`sum_partVec_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L33)).

**Read a real or imaginary cell coordinate.** Proved result. Under the declaration's hypotheses, an assembled cell variable reads the selected real or imaginary part of its shifted physical datum. (`fieldData_cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L40)).

**Gauge directions of cell variables.** Proved result. Under the declaration's hypotheses, the gauge direction of an assembled cell variable is the gauge direction of its corresponding cell datum. (`varDir_cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L49)).

**Head and gauge parts of cell data.** Proved result. A gauge-shifted cell datum equals its normalized head harmonic value plus the sum of its gauge directions weighted by the field gauge coefficients. (`fieldShifted_cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L54)).

**datum gauge comes from its skeleton key.** Proved result. The gauge direction of a cell datum is the stored key direction at its label and skeleton key. (`gaugeDir_cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L62)).

**The cell gauge direction is real.** Proved result. Complex conjugation leaves the selected cell gauge direction unchanged. (`conj_gaugeDir`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L66)).

**A harmonic layout has one angular mode.** Proved result. Under the declaration's hypotheses, the harmonic layout has the cell layer's azimuth order and contains only the angular integer of its label. (`layout_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L72)).

**Zero-label gauge corrections are real.** Proved result. Under the declaration's hypotheses, the weighted gauge correction for a zero lattice label has zero imaginary part. (`gaugeSum_zeroLabel_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L80)).

**Zero-label shifted data are real.** Proved result. Under the declaration's hypotheses, the gauge-shifted field datum at a zero lattice label has zero imaginary part. (`fieldShifted_zeroLabel_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L100)).

**Conjugation swaps gauge classes.** Proved result. Under the declaration's hypotheses, replacing each gauge direction by that of its conjugate class gives the complex conjugate of the original weighted gauge sum. (`conj_gaugeSum_swap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L111)).

**Conjugate deleted-key gauge corrections.** Proved result. Under the declaration's hypotheses, the gauge correction for the deleted conjugate key is the complex conjugate of the gauge correction for its surviving key. (`gaugeSum_deleted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L126)).

**Conjugate transport of gauge directions.** Proved result. Under the declaration's hypotheses, the conjugate datum has the original gauge direction with the gauge class replaced by its conjugate class. (`gaugeDir_transport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L163)).

**A leaf row reads the shifted datum.** Proved result. Under the declaration's hypotheses, evaluating the leaf row on assembled field coordinates returns the corresponding gauge-shifted physical datum. (`leafRow_fields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L184)).

**Agreement for a selected row type.** Proposition definition. Require every row of the selected type to evaluate to its corresponding shifted field datum. (`RowKindMatch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L264)).

**Rows that directly read a key.** Proposition definition. Select the key-row constructor of the row representation. (`IsKeyRow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L273)).

**Rows assembled from segment splits.** Proposition definition. Select the split-row constructor of the row representation. (`IsSplitRow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L276)).

**Rows representing a flux relation.** Proposition definition. Select row constructors that evaluate zero-mode flux relations. (`IsFluxRow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L279)).

**Rows derived from other data.** Proposition definition. Select the derived-row constructor of the row representation. (`IsDerivedRow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L282)).

**Rows for normal derivative data.** Proposition definition. Select the normal-row constructor of the row representation. (`IsNormalRow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L285)).

**Hypotheses for physical row matching.** Proposition structure. Package the symmetry, mesh, cell-calculus and field-relation assumptions used to match rows to fields. (`RowMatchHypotheses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L290)).

**Key-row agreement interface.** Interface. Require the key-row matching result for all admissible cell-layer inputs. (`KeyRowsMatchHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L312)). Proof route: `Breakdown.CertCell.Assembly.keyRowsMatchHolds_of`.

**Split-row agreement interface.** Interface. Require the split-row matching result for all admissible cell-layer inputs. (`SplitRowsMatchHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L316)). Proof route: `Breakdown.CertCell.Assembly.splitRowsMatchHolds_of`.

**Flux-row agreement interface.** Interface. Require the flux-row matching result for all admissible cell-layer inputs. (`FluxRowsMatchHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L320)). Proof route: `Breakdown.CertCell.Assembly.fluxRowsMatchHolds_of`.

**Derived-row agreement interface.** Interface. Require the derived-row matching result for all admissible cell-layer inputs. (`DerivedRowsMatchHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L324)). Proof route: `Breakdown.CertCell.Assembly.derivedRowsMatchHolds_of`.

**Normal-row agreement interface.** Interface. Require the normal-row matching result for all admissible cell-layer inputs. (`NormalRowsMatchHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L328)). Proof route: `Breakdown.CertCell.Assembly.normalRowsMatchHolds_of`.

**Combine the five row-matching cases.** Proved result. Under the declaration's hypotheses, agreement for key, split, flux, derived and normal rows gives agreement for every represented row. (`rowsMatchFields_of_kinds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L332)).

**All rows agree with physical field data.** Proved result. Under the hypotheses of this declaration, all row types evaluate to the corresponding shifted physical field data. (`rowsMatchFieldsHolds_of_kinds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L362)).

**The field state satisfies row matching.** Proved result. The state constructed from fields satisfies the complete row-matching condition. (`rowsMatchStateOfFields_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchAssemble.lean#L371)).

### Breakdown.CertCell.RowsMatchConj

Track negation and complex conjugation through cell data and harmonic keys, including the zero-mode imaginary part. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Field negation negates cell coefficients.** Proved result. The cell-basis coefficient of a negated field is the negative of the original coefficient. (`coef_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L18)).

**Extra values change sign with the field.** Proved result. Negating the field tuple negates each extra velocity value. (`extraValue_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L27)).

**Head data change sign with the field.** Proved result. Negating the field tuple negates its normalized head datum. (`headData_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L34)).

**The zero field has zero head data.** Proved result. Every normalized head datum of the zero field tuple is zero. (`headData_zeroField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L66)).

**Negating a pressure mode conjugates it.** Proved result. The pressure Fourier coefficient at the negative angular mode is the complex conjugate of the original coefficient. (`presMode_negMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L76)).

**Conjugate head data.** Proved result. Under the declaration's hypotheses, the head datum for the matched opposite mode and layout is the complex conjugate of the original head datum. (`headData_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L81)).

**Negated harmonic data are conjugate.** Proved result. Under the declaration's hypotheses, the conjugate datum at negative temporal frequency equals the conjugate of the original head harmonic. (`headHarmonic_negLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L148)).

**A zero mode is its own conjugate datum.** Proved result. Under the declaration's hypotheses, the stated zero-mode datum is a valid conjugate partner of itself. (`conjDatum_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L157)).

**zero temporal and angular datum is real.** Proved result. For a layout containing only angular mode zero, its temporal-frequency-zero head harmonic has zero imaginary part. (`headHarmonic_zero_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L161)).

**Conjugate data share gauge directions.** Proved result. Under the declaration's hypotheses, the skeleton keys of the conjugate data have the same gauge direction under the stated zero-mode conditions. (`dir_keyOf_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L168)).

**Zero-mode conjugate data have one key.** Proved result. Under the declaration's hypotheses, conjugate cell data at angular mode zero have the same skeleton key. (`keyOf_conj_of_modeZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchConj.lean#L180)).

### Breakdown.CertCell.RowsMatchDerived

Show that a derived row evaluates correctly once its non-pressure source data already match. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Finite assembled coordinate indices.** Instance. Install the finite enumeration of the tree entry's assembled coordinate type. (`slavedFintypeInst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerived.lean#L18)).

**Non-pressure head data need no shift.** Proved result. For a non-pressure datum, the normalized head value equals the true local datum. (`headData_of_not_pres`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerived.lean#L20)).

**Nonpressure head harmonics are unchanged.** Proved result. For a non-pressure datum, the head harmonic equals the ordinary harmonic cell datum. (`headHarmonic_of_not_pres`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerived.lean#L24)).

**Nonpressure gauge directions vanish.** Proved result. Under the declaration's hypotheses, the gauge direction of a cell datum is zero whenever that datum is not a pressure datum. (`gaugeDir_of_not_pres`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerived.lean#L31)).

**Expand a finite row value.** Proved result. A row evaluation equals the sum of its complex entries multiplied by the real input coordinates viewed as complex numbers. (`rowValue_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerived.lean#L46)).

**A derived row reads its source data.** Proved result. When its input rows already match, the derived row evaluates to the prescribed derived datum. (`derived_match`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerived.lean#L53)).

**Derived rows match shifted field data.** Proved result. Under the declaration's hypotheses, evaluating a derived row on assembled field coordinates returns its shifted physical datum. (`derived_row_fields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerived.lean#L96)).

### Breakdown.CertCell.RowsMatchDerivedNormal

Express normal rows using side and corner data and reduce their correctness to a normal-segment identity. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Evaluate side-velocity data.** Definition. Read the side-velocity quantity from a datum vector using the layout's side convention. (`velVal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L18)).

**Evaluate corner velocity data.** Definition. Read the corner quantity from the datum vector with the layout's corner convention. (`cornerVal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L21)).

**A valid segment endpoint.** Proposition definition. Require the chosen corner to be an endpoint compatible with the segment. (`EndOK`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L26)).

**The normal-segment relation.** Proposition definition. Require the stated normal derivative moment to agree with its velocity, tangential and endpoint terms. (`NormalSegmentIdentity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L31)).

**Normal-segment identity interface.** Interface. Require the normal-segment relation for the admissible harmonic field data. (`NormalSegmentHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L54)). Proof route: `Breakdown.CertCell.SegmentNormal.normalSegmentHolds_of`.

**Pair a row with assembled data.** Definition. Package evaluation against the assembled field data as a complex linear functional. (`valOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L65)).

**A row value is a linear evaluation.** Proved result. The row value is the evaluation functional applied to the stored row vector. (`rowValue_eq_valOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L70)).

**Velocity rows read side values.** Proved result. Evaluating the velocity row equals the layout's side-velocity expression formed from the evaluated datum rows. (`valOf_velRow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L73)).

**Corner rows read corner values.** Proved result. Evaluating the corner row equals the layout's corner expression formed from the evaluated datum rows. (`valOf_cornerRow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L81)).

**Agreement preserves velocity values.** Proved result. Under the declaration's hypotheses, two data functions that agree on the inputs used by a velocity value produce the same side-velocity value. (`velVal_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L88)).

**No gauge shift for nonpressure data.** Proved result. For a nonpressure datum, the shifted field coordinate equals the original harmonic datum. (`fieldShifted_of_not_pres`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L96)).

**Normal-row corners are valid endpoints.** Proved result. Under the declaration's hypotheses, the corner used in the normal row satisfies the segment endpoint condition. (`normal_end_ok`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L107)).

**Matching data preserve the normal corner.** Proved result. Under the declaration's hypotheses, the two datum assignments used in the normal-row proof have equal values at the required corner. (`normal_corner_val`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L121)).

**Normal rows match shifted field data.** Proved result. Under the declaration's hypotheses, evaluating a normal row on assembled field coordinates returns its shifted physical datum. (`normal_row_fields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchDerivedNormal.lean#L136)).

### Breakdown.CertCell.RowsMatchFlux

Identify flux rows through zero-mode stream identities, including tiled segment fluxes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Zero-mode key flux identities.** Interface. Require the radial and height zero-mode side keys to equal the specified stream and higher-moment expressions. (`KeyFluxHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L19)). Proof route: `Breakdown.CertCell.Assembly.keyFluxHolds_of_lift`.

**Side data agree with harmonic keys.** Proposition definition. Require a side-velocity harmonic datum to equal the harmonic value of its corresponding key. (`SideVelocityKeyMatch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L32)).

**Radial flux is a stream difference.** Proved result. Under the declaration's hypotheses, the zero-mode radial side harmonic equals minus the constant test coefficient divided by the radius times the endpoint stream difference. (`radial_harmonic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L44)).

**Height flux from moments and streams.** Proved result. Under the declaration's hypotheses, the constant height-side harmonic is recovered from its linear test moment and the endpoint stream difference with the recorded test coefficients. (`height_harmonic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L58)).

**Stream keys have no gauge direction.** Proved result. Every gauge direction evaluates to zero on a stream-function key. (`dir_stream`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L73)).

**Velocity keys have no gauge direction.** Proved result. Every gauge direction evaluates to zero on a side-velocity key. (`dir_velocity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L77)).

**A zero-width interval has zero moment.** Proved result. The height strip moment over the degenerate radial interval from zero to zero vanishes. (`strip_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L82)).

**Axis stream harmonics vanish.** Proved result. Every harmonic stream-function key at radius zero has value zero. (`keyHarmonic_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L93)).

**An optional-index sum selects its entry.** Proved result. A finite sum that is nonzero only when its index matches one specified optional index equals the matching entry. (`sum_ite_some`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L103)).

**Evaluate an optional complex-part row.** Proved result. The complex-part row returns the optional real entry plus i times the optional imaginary entry, changing the sign of i for conjugation and using zero for an absent entry. (`sum_partVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L112)).

**A key variable reads one complex part.** Proved result. Under the declaration's hypotheses, the assembled key variable is the selected real or imaginary part of its gauge-shifted field key. (`fieldData_keyVar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L118)).

**shifted stream key vanishes on the axis.** Proved result. The gauge-shifted field value of a stream-function key at radius zero is zero. (`fieldKey_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L126)).

**Stream keys have no gauge contribution.** Proved result. The shifted stream key equals the physical harmonic stream value. (`fieldKey_stream`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L132)).

**Velocity keys have no gauge contribution.** Proved result. The shifted velocity key equals the physical harmonic velocity value. (`fieldKey_velocity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L138)).

**Read an optional real or imaginary part.** Proved result. Under the declaration's hypotheses, the optional assembled coordinate reads exactly the selected real or imaginary part of the shifted key value. (`part_elim`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L146)).

**Shifted keys from field coordinates.** Proved result. Under the declaration's hypotheses, evaluating the complex-part row on assembled real field data gives the shifted harmonic key value or its conjugate according to the row flag. (`partVec_fieldData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L167)).

**Label negation reverses time frequency.** Proved result. Negating the lattice label negates its decoded temporal frequency. (`labelTime_negate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L184)).

**stream row recovers its harmonic value.** Proved result. Under the declaration's hypotheses, evaluating the stream complex-part row on field data gives the harmonic stream-function key value at its point. (`partVec_stream`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L188)).

**A flux row is a coordinate sum.** Proved result. The flux row value is the finite sum of its entries times the real field coordinates embedded in the complex numbers. (`rowValue_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L205)).

**Evaluate a scaled row difference.** Proved result. Pairing a scalar multiple of a row difference with field coordinates gives the scalar times the difference of the two row pairings. (`pair_smul_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L216)).

**Evaluate nested scaled row differences.** Proved result. The pairing of a scaled row minus a scaled difference expands into the corresponding scalar combination of three row pairings. (`pair_smul_sub_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L221)).

**Side velocity data equal key values.** Proved result. Under the declaration's hypotheses, the shifted side-velocity coordinate equals the harmonic velocity key value with the segment geometry, component and polynomial index of that datum. (`fieldShifted_side`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L227)).

**Flux rows match shifted field data.** Proved result. Under the declaration's hypotheses, evaluating a flux row on assembled field coordinates returns its shifted physical datum. (`fluxRow_fields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L251)).

**Recover a zero-mode harmonic key.** Proved result. Under the declaration's hypotheses, at zero mode, the complex-part row applied to field data gives the harmonic key value. (`partVec_modeZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L300)).

**Tile starts lie above the first endpoint.** Proved result. For a consecutively joined chain of nonempty intervals, each tile lower endpoint is at least the first lower endpoint. (`tile_lo_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L320)).

**Normal keys have zero angular mode.** Proved result. Under the declaration's hypotheses, a normal velocity key has angular mode zero, selects the radial or axial normal component, and has nonnegative half-plane segment geometry. (`side_geometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L333)).

**A tile flux row reads its retiled key.** Proved result. Under the declaration's hypotheses, evaluating the tile flux row on field data gives the harmonic value of the corresponding retiled degree-zero normal velocity key. (`tileFlux_fields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchFlux.lean#L383)).

### Breakdown.CertCell.RowsMatchKeyData

Relate local cell data to layout-independent harmonic keys and transport key evaluation under conjugation. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Harmonic traces ignore auxiliary ends.** Proposition definition. Require side and corner harmonic traces to be independent of the auxiliary opposite endpoints. (`HarmonicTraceIndependence`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L21)).

**Both radial endpoints are nonnegative.** Proved result. Under the declaration's hypotheses, choosing either endpoint of a nonempty nonnegative radial interval makes the reflected opposite endpoint distinct and leaves both endpoints and their minimum nonnegative. (`pair_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L51)).

**A key segment is a valid face segment.** Proved result. Under the declaration's hypotheses, the segment rebuilt from the key's geometry and coefficients satisfies the face-segment conditions. (`keySeg_face`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L57)).

**Head pressure ignores layout choices.** Proved result. Under the declaration's hypotheses, two layouts with the same angular symmetry order produce the same normalized pressure-mode function for the same field tuple and mode. (`headPressure_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L61)).

**Side moments agree with skeleton keys.** Proved result. Under the declaration's hypotheses, the velocity, gradient and pressure moments of a valid segment equal the corresponding skeleton-key values. (`side_match`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L66)).

**A head datum equals its key value.** Proved result. Under the declaration's hypotheses, a non-private head datum equals the physical value of its corresponding skeleton key in the common layout. (`head_key`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L115)).

**Local head data match skeleton keys.** Proved result. Under the declaration's hypotheses, the harmonic value of every admissible non-private head datum agrees with the value of its skeleton key. (`keyHeadMatch_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L203)).

**Common-layout side keys agree.** Proved result. Under the declaration's hypotheses, a side-velocity head harmonic equals the harmonic value of its skeleton key in the common key layout. (`sideVelocityKeyMatch_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L210)).

**Conjugation reverses the key mode.** Proved result. Under the declaration's hypotheses, replacing a key's angular mode by its negative conjugates the physical key value. (`keyValue_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L226)).

**Negation of frame vector coordinates.** Proved result. The moving-frame coordinates of a negated vector are the negatives of its original coordinates. (`frameVec_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L261)).

**Negation of frame matrix coordinates.** Proved result. Negating a gradient matrix negates each of its moving-frame entries. (`frameMat_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L265)).

**Negation of frame Hessian coordinates.** Proved result. Negating the Hessian tensor negates each of its moving-frame entries. (`frameThird_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L268)).

**Velocity modes preserve field negation.** Proved result. Every angular velocity mode of the negated field is the negative of the corresponding original mode. (`modeVec_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L272)).

**Gradient modes preserve field negation.** Proved result. Every angular gradient mode of the negated field is the negative of the corresponding original mode. (`modeMat_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L276)).

**Hessian modes preserve field negation.** Proved result. Every angular Hessian mode of the negated field is the negative of the corresponding original mode. (`modeThird_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L280)).

**Negate a radial trace pair.** Proved result. Negating both the field and its radial derivative negates the radial strip moment. (`radial_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L284)).

**Negate a height trace pair.** Proved result. Negating both the field and its height derivative negates the height strip moment. (`height_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L288)).

**Negate a segment trace triple.** Proved result. Negating the field and both derivative inputs negates the segment trace moment. (`moment_neg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L292)).

**Negate a corner trace quadruple.** Proved result. Negating the field, its two first derivatives and its mixed derivative negates the corner moment. (`corner_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L299)).

**A.e. agreement preserves moments.** Proved result. Under the declaration's hypotheses, replacing the field input by one that agrees almost everywhere on the trace rectangle leaves the segment moment unchanged. (`moment_congr_ae'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L303)).

**Normalized pressure is odd a.e..** Proved result. Under the declaration's hypotheses, almost everywhere on the plane, the pressure mode of the normalized potential for the negated gradient field is the negative of the original normalized pressure mode. (`headPotential_neg_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L317)).

**Tuple negation negates velocity modes.** Proved result. Negating the field tuple negates each cell velocity mode. (`velMode_negTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L362)).

**Tuple negation negates gradient modes.** Proved result. Negating the field tuple negates each cell gradient mode. (`gradModeOf_negTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L367)).

**Tuple negation negates Hessian modes.** Proved result. Negating the field tuple negates each cell Hessian mode. (`secondModeOf_negTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L372)).

**Negate pressure-gradient modes.** Proved result. Negating the field tuple negates each pressure-gradient mode. (`pressureGradMode_negTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L377)).

**Tuple negation negates all key values.** Proved result. Under the declaration's hypotheses, negating the field tuple negates the physical value of each skeleton key. (`keyValue_negTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L382)).

**Cosine harmonics are even in frequency.** Proved result. The cosine time harmonic at a negated frequency equals the original cosine harmonic. (`harmonicCos_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L404)).

**Sine harmonics are odd in frequency.** Proved result. The sine time harmonic at a negated frequency is the negative of the original sine harmonic. (`harmonicSin_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L409)).

**Cosine tuples are even in frequency.** Proved result. Negating the temporal frequency leaves the complete cosine harmonic field tuple unchanged. (`cosTuple_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L414)).

**Sine field tuples are odd in frequency.** Proved result. Negating the temporal frequency negates the complete sine harmonic field tuple. (`sinTuple_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L419)).

**Conjugate both harmonic key frequencies.** Proved result. Under the declaration's hypotheses, negating the temporal frequency and the key's angular mode conjugates the harmonic key value. (`keyHarmonic_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L424)).

**Keep a key's existing mode.** Proved result. Under the declaration's hypotheses, a key whose mode is n is unchanged when its mode is replaced by n. (`keyWithMode_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L440)).

**The last key-mode replacement wins.** Proved result. Replacing a key's mode twice has the same effect as keeping only the last replacement. (`keyWithMode_twice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L444)).

**Read the mode of a relabelled key.** Proved result. Under the declaration's hypotheses, a key with replaced mode either records that new mode or is a stream key, which has no mode field. (`keyMode_withMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L447)).

**Negating a label negates its time index.** Proved result. The temporal index decoded from a negated lattice label is the negative of the original index. (`labelTime_negLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L454)).

**Reflection preserves temporal frequency.** Proved result. Reflecting a lattice label leaves its decoded temporal frequency unchanged. (`labelTime_flipLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L458)).

**Opposite harmonic values are conjugates.** Proved result. Under the declaration's hypotheses, evaluation at opposite temporal and angular frequencies gives the complex conjugate of the original harmonic key evaluation. (`conj_evaluation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L462)).

**Harmonic key values respect evaluation.** Proved result. Under the declaration's hypotheses, the key evaluation sign, label and conjugation transfer correctly to the physical harmonic key value. (`keyEvalTransfer_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L475)).

**Key interfaces imply row matching.** Proved result. Under the declaration's hypotheses, the head-key and evaluation-transfer interfaces imply that the key row evaluates to its shifted physical datum. (`keyRow_fields_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L505)).

**Split interfaces imply row matching.** Proved result. Under the declaration's hypotheses, the key and segment-splitting interfaces imply that the split row evaluates to its shifted physical datum. (`splitRow_fields_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyData.lean#L518)).

### Breakdown.CertCell.RowsMatchKeyFlip

Discharge the reflection interfaces for harmonic keys, including odd stream values on the equatorial plane. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Local modes from time harmonics.** Proved result. Under the declaration's hypotheses, at almost every positive-radius point, a spacetime velocity or gradient mode with angular frequency equal to the symmetry order times the mode index splits into its cosine local mode plus the imaginary unit times its sine local mode. (`timeMode_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlip.lean#L20)).

**Odd stream harmonics vanish on the plane.** Proved result. Under the declaration's hypotheses, every admissible stream key of odd temporal frequency vanishes at zero height. (`oddStreamKeyZero_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlip.lean#L54)).

**Signed reflection of plane keys.** Proved result. Under the declaration's hypotheses, admissible non-private keys on the equatorial plane satisfy the signed reflected-harmonic identity. (`keyPlaneFlip_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlip.lean#L88)).

### Breakdown.CertCell.RowsMatchKeyFlipMain

Assemble reflected side, gradient, corner and pressure keys into the key reflection rule. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Invert a sign relation.** Proved result. Under the declaration's hypotheses, a relation multiplied by a real sign of square one can be reversed using the same sign. (`back`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipMain.lean#L19)).

**Strip velocity reflection signs.** Proved result. Under the declaration's hypotheses, reversing angular frequency multiplies an equatorial strip-velocity moment by its coordinate reflection sign. (`stripVel_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipMain.lean#L22)).

**Strip gradient reflection signs.** Proved result. Under the declaration's hypotheses, reversing angular frequency multiplies an equatorial strip-gradient moment by minus its output coordinate reflection sign. (`stripGrad_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipMain.lean#L35)).

**Corner velocity reflection signs.** Proved result. Under the declaration's hypotheses, reversing angular frequency multiplies a corner-velocity value by its coordinate reflection sign. (`cornerVal_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipMain.lean#L49)).

**Equatorial pressure is angularly even.** Proved result. Under the declaration's hypotheses, the pressure key on the height-zero plane has equal values at opposite angular frequencies. (`presKey_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipMain.lean#L57)).

**Odd stream modes vanish on the plane.** Proposition definition. Require odd temporal stream harmonics to vanish at zero height. (`OddStreamKeyZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipMain.lean#L78)).

**Assemble reflection for plane keys.** Proved result. Under the declaration's hypotheses, the component reflection and odd-stream conditions imply the complete plane-key reflection rule. (`keyPlaneFlip_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipMain.lean#L84)).

### Breakdown.CertCell.RowsMatchKeyFlipParts

Express cosine and sine strip data as plane-mode traces before applying reflection. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Negating the mode preserves parity.** Proved result. Under the declaration's hypotheses, replacing the angular integer by its negative preserves the required even parity with the temporal integer. (`even_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L21)).

**Angular reversal reflects lattice labels.** Proved result. Under the declaration's hypotheses, decoding a harmonic pair with negated angular frequency gives the reflected physical Fourier label of the original pair. (`label_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L25)).

**A reflection sign squares to one.** Proved result. Multiplying the coordinate reflection sign by itself gives one. (`frameSign_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L33)).

**Integrable local velocity and gradients.** Proved result. Under the declaration's hypotheses, all local velocity and gradient components are integrable on the specified cell rectangle. (`mode_int_n`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L37)).

**Integrable weighted Hessian squares.** Proved result. Under the declaration's hypotheses, a local Hessian mode is almost everywhere strongly measurable on the cell, and its radius-weighted squared norm is integrable there. (`third_sq_n`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L46)).

**Integrable radius-weighted Hessians.** Proved result. Under the declaration's hypotheses, the local Hessian mode multiplied by radius is integrable on the cell rectangle. (`third_weighted_n`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L58)).

**Off-axis Hessian mode integrability.** Proved result. Under the declaration's hypotheses, the local Hessian mode is integrable without a radial weight on the specified cell rectangle. (`third_plain_n`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L76)).

**Lift compatible harmonic data locally.** Proved result. For a compatible temporal and angular frequency pair, the cosine and sine harmonics are local second-order fields and their complex combination recovers the labelled velocity, gradient and Hessian modes almost everywhere at positive radius. (`lift_gen`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L94)).

**A harmonic side-velocity moment.** Definition. Combine cosine and sine weak strip moments of velocity into one complex harmonic moment. (`stripVel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L117)).

**A harmonic side-gradient moment.** Definition. Combine cosine and sine weighted strip moments of the height-gradient column. (`stripGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L124)).

**A harmonic corner-velocity moment.** Definition. Combine cosine and sine corner moments into one complex harmonic value. (`cornerVal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L131)).

**Harmonic velocity strips as plane traces.** Proved result. Under the declaration's hypotheses, the combined cosine-sine strip-velocity moment equals the corresponding plane-mode height trace. (`stripVel_as_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L140)).

**Harmonic gradient strips as plane traces.** Proved result. Under the declaration's hypotheses, the combined cosine-sine weighted gradient moment equals the corresponding plane-mode height trace. (`stripGrad_as_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L156)).

**Harmonic corners as plane-mode corners.** Proved result. Under the declaration's hypotheses, the combined cosine-sine corner value equals the corner moment of the plane velocity, gradient and mixed Hessian modes. (`cornerVal_as_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipParts.lean#L176)).

### Breakdown.CertCell.RowsMatchKeyFlipStatement

State the reflection rule for non-private keys on the half-plane boundary. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Reflection of keys on the plane.** Proposition definition. Require the stated signed reflection rule for admissible non-private harmonic keys on the equatorial plane. (`KeyPlaneFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlipStatement.lean#L15)).

### Breakdown.CertCell.RowsMatchKeyFlux

Derive zero-mode side fluxes from stream differences and pass the local identities to harmonic keys. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Zero-mode axial data are integrable.** Proved result. Under the declaration's hypotheses, the zero-angular-frequency axial velocity mode and its axial gradient mode are integrable on the specified radial-height rectangle. (`rect_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L26)).

**zero-mode height pair is weakly valid.** Proved result. Under the declaration's hypotheses, the axial zero-mode velocity and axial gradient coefficient form the unweighted height weak derivative pair. (`height_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L36)).

**Height traces ignore the opposite end.** Proved result. Under the declaration's hypotheses, the weighted zero-mode height trace is unchanged when its auxiliary opposite height is changed. (`trace_indep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L53)).

**Factor out a constant radial test.** Proved result. The radial strip moment against a constant test is that constant times the moment against one. (`radial_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L63)).

**Radial keys from stream differences.** Proved result. Under the declaration's hypotheses, the zero-mode radial velocity key equals minus its test coefficient divided by the radius times the endpoint stream difference. (`radial_key`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L69)).

**Separate the height weight and test.** Proved result. The height strip integrand equals the unweighted unit-test integrand multiplied by the radial weight and test value. (`strip_term_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L93)).

**Split a height strip at an inner radius.** Proved result. Under the declaration's hypotheses, the height strip moment on an interval equals the sum of its moments on the two adjacent subintervals. (`strip_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L100)).

**Recover a constant height-velocity key.** Proved result. Under the declaration's hypotheses, the constant height-velocity key is determined by its linear moment and the endpoint stream difference. (`height_key`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L127)).

**Normal moments from stream differences.** Proved result. Under the declaration's hypotheses, local zero-angular-frequency normal velocity moments are determined by stream-function endpoint differences, with the axial case also using the first polynomial moment. (`keyFlux_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L215)).

**Lift zero-mode fluxes to harmonic keys.** Proved result. Under the declaration's hypotheses, the local flux identities and harmonic lift give the radial and height key-flux interfaces. (`keyFluxHolds_of_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyFlux.lean#L231)).

### Breakdown.CertCell.RowsMatchKeyRows

Evaluate key and split rows by separating their harmonic values from gauge shifts. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Apply a key evaluation sign.** Definition. Apply the evaluation sign and optional complex conjugation to a key value. (`evalValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L19)).

**Head data agree with their keys.** Proposition definition. Require a non-private cell datum and its layout-independent harmonic key to have the same harmonic value. (`KeyHeadMatch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L22)).

**Transport harmonic key evaluation.** Proposition definition. Require key evaluation to respect its recorded sign, label and optional conjugation. (`KeyEvalTransfer`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L30)).

**Harmonic keys split over segments.** Proposition definition. Require a side key to equal the sum of the retiled subsegment keys with their basis-change coefficients. (`KeySplitAdditive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L39)).

**Evaluate complex key coordinates.** Proved result. The complex-part row forms the optional real coordinate plus or minus i times the optional imaginary coordinate according to its conjugation flag. (`sum_partVec_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L55)).

**Real and imaginary parts are additive.** Proved result. The selected real or imaginary part of a complex sum is the sum of the selected parts. (`keyPart_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L73)).

**Real and imaginary parts recover a value.** Proved result. The real part plus the chosen sign of i times the imaginary part recovers the complex value or its conjugate. (`parts_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L77)).

**The selected gauge direction is real.** Proved result. Complex conjugation fixes the gauge direction for the specified key and class. (`dir_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L82)).

**Conjugate gauge sums by swapping classes.** Proved result. Under the declaration's hypotheses, replacing each gauge class by its conjugate class in the direction sum gives the conjugate of the original gauge correction. (`gauge_sum_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L86)).

**Extract a gauge real or imaginary part.** Proved result. Under the declaration's hypotheses, the real or imaginary part of the summed gauge correction is the sum of gauge coefficients times the symmetric or antisymmetric combinations of conjugate-class directions. (`gauge_part`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L97)).

**Remove gauge shifts from field data.** Definition. Subtract the gauge-direction contribution from each assembled field coordinate. (`harmData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L116)).

**Ungauged data read a harmonic key part.** Proved result. Under the declaration's hypotheses, removing the gauge contribution leaves the selected real or imaginary part of the physical harmonic key value. (`harmData_key`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L122)).

**A degenerate strip has zero moment.** Proved result. A height strip moment whose radial endpoints are both zero vanishes. (`strip_null_moment`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L147)).

**Axis stream harmonics vanish.** Proved result. Under the declaration's hypotheses, the harmonic stream-function key value is zero at every radial-height point with radius zero. (`keyHarmonic_stream_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L158)).

**Nonzero angular gauge directions vanish.** Proved result. If the first lattice-label coordinate is nonzero, every gauge direction at that label is zero. (`dir_eq_zero_of_not_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L167)).

**Nonpressure keys have no gauge direction.** Proved result. Under the declaration's hypotheses, a skeleton key that is not a pressure key has zero value in every gauge direction. (`dir_eq_zero_of_not_pressure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L173)).

**Omitted key parts have zero gauge shift.** Proved result. Under the declaration's hypotheses, an omitted real or imaginary key part that is not omitted through the deleted-key case has zero contribution from the summed gauge correction. (`gauge_keyPart_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L180)).

**Read an optional ungauged harmonic part.** Proved result. Under the declaration's hypotheses, the optional ungauged coordinate equals the complex cast of the selected harmonic key part. (`harmData_part`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L213)).

**Recover a key from ungauged data.** Proved result. Under the declaration's hypotheses, the complex-part row on ungauged harmonic data returns the harmonic key value, conjugated exactly when its flag requests it. (`partVec_harmData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L232)).

**Separate row data from gauge corrections.** Proved result. A row applied to physical field coordinates equals its application to ungauged harmonic data plus the sum of its evaluations on gauge directions weighted by the gauge coefficients. (`transport_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L244)).

**Row evaluation is a coordinate pairing.** Proved result. A row value is the sum of its complex coefficients times the real field coordinates embedded in the complex numbers. (`rowValue_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L259)).

**Deleted keys are zero-mode pressure keys.** Proved result. Under the declaration's hypotheses, an omitted deleted key is a zero-angular-mode pressure key, and its negated label is deleted as well. (`deleted_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L266)).

**Evaluation may negate the label.** Proved result. Under the declaration's hypotheses, a valid key evaluation records either the original lattice label or its negative. (`evaluation_labels`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L281)).

**Angular labels agree up to sign.** Proved result. Under the declaration's hypotheses, the evaluated label's first coordinate equals the original first coordinate or its negative. (`evaluation_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L293)).

**Evaluation preserves deleted keys.** Proved result. Under the declaration's hypotheses, the evaluated label and relabelled key retain the omitted-deleted-key condition. (`deleted_evaluation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L302)).

**Detect deletion from an evaluated key.** Proved result. Under the declaration's hypotheses, the deleted-key condition of the evaluation implies deletion of the original labelled key. (`evaluation_deleted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L314)).

**Read evaluation signs and conjugation.** Proved result. The evaluation value is its real sign times either the original complex number or its conjugate. (`evalValue_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L340)).

**Cell keys retain nonstream modes.** Proved result. Under the declaration's hypotheses, a cell datum's skeleton key either stores the layout's angular mode or is a stream key. (`key_mode_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L347)).

**Key rows match shifted physical values.** Proved result. Under the declaration's hypotheses, evaluating a key row on assembled field data gives its shifted physical datum. (`keyRow_fields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L378)).

**The three families of side keys.** Proved result. Under the declaration's hypotheses, a key with the stated side geometry is a velocity, gradient or pressure key with that geometry. (`side_cases`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L435)).

**Retiling preserves key metadata.** Proved result. Under the declaration's hypotheses, retiling a side key preserves its mode, equatorial-plane condition and reflection sign, produces a nonprivate key, and preserves half-plane validity when the new lower endpoint is no smaller. (`retile_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L457)).

**Retiling preserves key evaluation.** Proved result. Under the declaration's hypotheses, the recorded key evaluation remains valid after restricting the key to the stated subsegment and basis term. (`evaluation_retile`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L469)).

**Evaluation signs square to one.** Proved result. Under the declaration's hypotheses, the complex cast of a valid key-evaluation sign has square one. (`sign_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L477)).

**Cancel a sign whose square is one.** Proved result. Under the declaration's hypotheses, a sign whose square is one can be inserted twice without changing the product. (`sign_cancel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L498)).

**Tile starts exceed the first endpoint.** Proved result. Under the declaration's hypotheses, in a consecutive nonempty interval tiling, every lower tile endpoint is at least the initial lower endpoint. (`tile_lo_ge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L501)).

**Pairing a doubly indexed row sum.** Proved result. A row pairing distributes over a scalar multiple of a doubly indexed finite linear combination, preserving all scalar coefficients. (`sum_smul_double`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L515)).

**Gauge-free rows annihilate gauge shifts.** Proved result. If a key has zero gauge direction in every class and label, its complex-part row annihilates every variable-part gauge direction. (`partVec_gauge_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L525)).

**Every stream gauge direction is zero.** Proved result. A stream-function key has zero gauge direction for every class and label. (`dir_stream_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L541)).

**Every velocity gauge direction is zero.** Proved result. A side-velocity key has zero gauge direction for every class and label. (`dir_velocity_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L545)).

**Split rows match shifted physical values.** Proved result. Under the declaration's hypotheses, evaluating a split row on assembled field data gives its shifted physical datum. (`splitRow_fields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeyRows.lean#L553)).

### Breakdown.CertCell.RowsMatchKeySplit

Show that a key moment is additive under a valid segmentation and change of test basis. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A radial or height strip pairing.** Definition. Choose the radial or height weak strip moment according to the side orientation. (`stripJ`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L25)).

**Key moments as oriented strip pairings.** Proved result. The moment of a key segment equals the radial or height strip pairing selected by its orientation and weight flag. (`moment_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L28)).

**Retiled segment tests are continuous.** Proved result. The polynomial test of the segment associated with a side key is continuous. (`test_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L32)).

**Integrability needed for strip pairing.** Proposition definition. Require the field and its appropriate weighted derivative to be integrable on every relevant strip. (`StripInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L37)).

**Order the unit-width trace endpoints.** Proved result. The smaller of a level and that level plus one is the level, and the larger is the level plus one. (`min_max_succ`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L43)).

**Radial strip terms are integrable.** Proved result. Under the declaration's hypotheses, the radial weak-trace term is integrable over the rectangle between the selected level and level plus one, crossed with the segment interval. (`radial_term_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L46)).

**Height strip terms are integrable.** Proved result. Under the declaration's hypotheses, the weighted height weak-trace term is integrable over the segment interval crossed with the interval between the selected level and level plus one. (`height_term_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L58)).

**Both strip orientations are integrable.** Proved result. Under the declaration's hypotheses, the radial branch has an integrable radial trace integrand and the height branch has an integrable weighted height trace integrand. (`term_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L76)).

**Add strip moments across an interval.** Proved result. Under the declaration's hypotheses, a strip moment on an interval equals the sum of its moments on the two adjacent subintervals with the same test. (`stripJ_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L85)).

**Strip moments are additive in tests.** Proved result. Under the declaration's hypotheses, the oriented strip moment of the sum of two tests is the sum of their moments. (`stripJ_lin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L95)).

**Scale a strip test by a real constant.** Proved result. Multiplying the strip test by a real constant multiplies its complex moment by that constant. (`stripJ_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L119)).

**Tile an additive interval value.** Proved result. Under the declaration's hypotheses, an interval quantity additive across adjacent intervals equals the sum over a consecutive tiling, whose lower endpoints all lie above the initial endpoint. (`tile_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L125)).

**Expand a tiled test in local bases.** Proved result. Under the declaration's hypotheses, an interval functional applied to a global test equals the sum of its local-basis evaluations on every tile multiplied by the local expansion coefficients. (`tile_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L171)).

**Split a weak strip moment over tiles.** Proved result. Under the declaration's hypotheses, a strip trace moment equals the sum of its retiled strip moments weighted by the coefficients expressing the original test in each tile basis. (`strip_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L190)).

**Unweight integrals on positive strips.** Proved result. Under the declaration's hypotheses, an integrable radius-weighted function is integrable without that weight on a bounded strip with positive lower radius. (`unweight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L205)).

**Integrable weighted Hessian strip modes.** Proved result. Under the declaration's hypotheses, multiplying the local Hessian mode by radius gives an integrable function on the selected bounded rectangle. (`third_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L218)).

**Velocity modes meet strip integrability.** Proved result. Under the declaration's hypotheses, the velocity mode and its radial and height derivative modes satisfy the unweighted strip-integrability condition. (`vel_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L235)).

**Integrability for radial gradient traces.** Proved result. Under the declaration's hypotheses, the radial gradient column and its derivatives satisfy the radially weighted radial-strip condition. (`grad_radial_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L253)).

**Integrability for height gradient traces.** Proved result. Under the declaration's hypotheses, the height gradient column and its derivatives satisfy the radially weighted height-strip condition. (`grad_height_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L264)).

**Integrability for radial pressure traces.** Proved result. Under the declaration's hypotheses, the normalized pressure mode and pressure-gradient modes satisfy the weighted radial-strip condition. (`pres_radial_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L278)).

**Integrability for height pressure traces.** Proved result. Under the declaration's hypotheses, the normalized pressure mode and pressure-gradient modes satisfy the weighted height-strip condition. (`pres_height_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L287)).

**Split a side key into retiled keys.** Proved result. Under the declaration's hypotheses, the physical value of a side key equals the sum of retiled key values weighted by their test-polynomial expansion coefficients. (`keyValue_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L297)).

**Harmonic side keys split additively.** Proved result. Under the declaration's hypotheses, the harmonic lift and local strip splitting imply the additive retiled-key expansion. (`keySplitAdditive_of_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKeySplit.lean#L342)).

### Breakdown.CertCell.RowsMatchKinds

Combine the separate row-type proofs into the complete row-field matching interface. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Key rows match field data.** Proved result. Under the hypotheses of this declaration, the key rows evaluate to their corresponding physical field data. (`keyRowsMatchHolds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKinds.lean#L16)).

**Flux rows match field data.** Proved result. Under the hypotheses of this declaration, the flux rows evaluate to their corresponding physical field data. (`fluxRowsMatchHolds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKinds.lean#L26)).

**Split rows match field data.** Proved result. Under the hypotheses of this declaration, the segment-split rows evaluate to their corresponding physical field data. (`splitRowsMatchHolds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKinds.lean#L36)).

**Derived rows match field data.** Proved result. For a periodic second-order field, the derived rows evaluate to their corresponding physical field data. (`derivedRowsMatchHolds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKinds.lean#L52)).

**Normal rows match field data.** Proved result. Under the hypotheses of this declaration, the normal derivative rows evaluate to their corresponding physical field data. (`normalRowsMatchHolds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKinds.lean#L64)).

**All rows agree with physical field data.** Proved result. For a periodic second-order field, all row types evaluate to the corresponding shifted physical field data. (`rowsMatchFieldsHolds_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchKinds.lean#L71)).

### Breakdown.CertCell.RowsMatchNormalField

Prove the normal-segment identity for actual field data. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**True data satisfy the normal relation.** Proved result. Under the declaration's hypotheses, the true local field datum vector satisfies the normal-segment identity. (`normalSegmentIdentity_trueData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalField.lean#L13)).

### Breakdown.CertCell.RowsMatchNormalHeight

Derive the normal height-side formula from trace-freeness and integration by parts. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Trace-freeness splits a height moment.** Proved result. Under the declaration's hypotheses, the height moment of one diagonal entry is minus the sum of the other two diagonal moments. (`height_trace_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalHeight.lean#L15)).

**Recover normal height-gradient moments.** Proved result. Under the declaration's hypotheses, the normal height-gradient moment is recovered from radial corner values, a differentiated radial-velocity test and the angular velocity moment. (`height_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalHeight.lean#L40)).

### Breakdown.CertCell.RowsMatchNormalLine

Package the one-dimensional integration-by-parts calculation used by normal rows. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A linear weak line pairing.** Definition. Integrate the two coefficient fields against a test and a companion test along a chosen coordinate. (`lineForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalLine.lean#L10)).

**Decompose a linear weak line pairing.** Proved result. Under the declaration's hypotheses, the pairing of the stated linear combination of test pairs is the same linear combination of their pairings. (`lineForm_comb`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalLine.lean#L13)).

**Line pairings from endpoint values.** Proved result. Under the declaration's hypotheses, the weak pairing against a test and its derivative equals the endpoint-weighted pairings against the two affine endpoint tests. (`lineForm_byParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalLine.lean#L39)).

### Breakdown.CertCell.RowsMatchNormalPoly

Control the degree and derivative of the segment test polynomials used in normal rows. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Integrable velocity-gradient strip terms.** Proved result. Under the declaration's hypotheses, a constant multiple of a velocity mode plus a weighted gradient mode is integrable on the selected strip rectangle. (`strip_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L17)).

**Radial moments are linear in the test.** Proved result. Under the declaration's hypotheses, a radial strip moment of a finite real linear combination of tests is the same combination of their moments. (`radialStripMoment_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L29)).

**Height moments are linear in the test.** Proved result. Under the declaration's hypotheses, a height strip moment of a finite real linear combination of tests is the same combination of their moments. (`heightStripMoment_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L53)).

**The segment test polynomial.** Definition. Build the polynomial whose coefficients are the segment test coefficients. (`testPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L78)).

**polynomial evaluates to the segment test.** Proved result. Evaluating the reconstructed polynomial gives the original segment test function. (`testPoly_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L81)).

**Test polynomial degree bound.** Proved result. The natural degree of the segment test polynomial of index d is at most d. (`testPoly_natDegree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L84)).

**Test coefficients vanish above degree.** Proved result. Under the declaration's hypotheses, the coefficient of the segment test polynomial at an index greater than its degree parameter is zero. (`testPoly_coeff_gt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L89)).

**Read the leading test coefficient.** Proved result. The coefficient at the nominal degree equals the stored diagonal test coefficient. (`testPoly_coeff_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L92)).

**No excess triangular basis coefficients.** Proved result. For a polynomial of degree at most D expanded in a triangular test basis with nonzero leading coefficients, every retained coefficient above D vanishes. (`coef_zero_above`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L95)).

**The derivative test polynomial.** Definition. Multiply each test coefficient by its exponent and lower that exponent by one. (`slopePoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L123)).

**Evaluate the derivative polynomial.** Proved result. The slope polynomial evaluates to the sum of each test coefficient times its power index and the variable to one less than that index. (`slopePoly_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L126)).

**The slope polynomial has bounded degree.** Proved result. The natural degree of the segment slope polynomial of index d is at most d. (`slopePoly_natDegree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L130)).

**Segment polynomial tests are smooth.** Proved result. Every polynomial test attached to a face segment is smooth. (`test_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L136)).

**Differentiate a segment test polynomial.** Proved result. The derivative of a segment test is the finite power sum obtained by multiplying each coefficient by its power index and lowering that power by one. (`test_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalPoly.lean#L140)).

### Breakdown.CertCell.RowsMatchNormalRadial

Derive the normal radial-side formula from trace-freeness and cylindrical differentiation. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Trace-freeness splits a radial moment.** Proved result. Under the declaration's hypotheses, the radial moment of one diagonal entry is minus the sum of the other two diagonal moments. (`radial_trace_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalRadial.lean#L15)).

**Recover normal radial-gradient moments.** Proved result. Under the declaration's hypotheses, the normal radial-gradient moment is recovered from radial and angular velocity moments, axial corner values and the differentiated axial-velocity test. (`radial_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalRadial.lean#L38)).

### Breakdown.CertCell.RowsMatchNormalSegment

Combine real normal-segment identities into the complex harmonic identity. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Combine real normal relations.** Proved result. Under the declaration's hypotheses, the normal-segment identity is preserved when two valid real datum assignments are combined as a complex harmonic. (`normalSegmentIdentity_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalSegment.lean#L10)).

**The harmonic normal-segment identity.** Proved result. Under the hypotheses of this declaration, the harmonic field data satisfy the normal-segment identity. (`normalSegmentHolds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalSegment.lean#L42)).

### Breakdown.CertCell.RowsMatchNormalTurn

Use the angular relation to rewrite radial strip moments with the correct orientation signs. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The endpoint orientation squares to one.** Proved result. The orientation sign has square one for distinct endpoints. (`edgeSign_mul_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L21)).

**The upper endpoint has positive sign.** Proved result. When the first endpoint exceeds the second, its orientation sign is one. (`edgeSign_of_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L25)).

**The lower endpoint has negative sign.** Proved result. When the first endpoint is below the second, its orientation sign is minus one. (`edgeSign_of_gt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L27)).

**The radial axis is a null set.** Proved result. The first coordinate is nonzero almost everywhere for planar Lebesgue measure. (`ae_fst_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L29)).

**Cell rectangle is measurable.** Proved result. The cell rectangle is a measurable set. (`rect_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L36)).

**Cell rectangle is compact.** Proved result. For every cell box, its closed rectangle of radial and height coordinates is compact in R². (`rect_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L38)).

**Positive-radius facts hold on the cell.** Proved result. Under the declaration's hypotheses, the stated property valid away from radius zero holds almost everywhere on the cell rectangle. (`ae_pos_on`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L40)).

**Integrable offset-weighted pairings.** Proved result. Under the declaration's hypotheses, the product of the coefficient, the test and radius minus the opposite endpoint is integrable on the cell rectangle. (`offset_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L47)).

**Separate the angular trace correction.** Proved result. Under the declaration's hypotheses, the affine radial trace integrand splits into the scaled angular-relation term and the explicit endpoint-vanishing correction. (`turn_point`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L62)).

**angular relation rewrites a radial trace.** Proved result. Under the declaration's hypotheses, the angular relation expresses the radial strip moment as the stated linear combination of velocity strip moments divided by the face radius. (`strip_turn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchNormalTurn.lean#L79)).

### Breakdown.CertCell.RowsMatchTrace

Show that weak segment and corner traces do not depend on the auxiliary opposite endpoint. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Weak traces ignore the opposite endpoint.** Proved result. Under the declaration's hypotheses, the weak trace value is unchanged when the auxiliary opposite endpoint is moved under the stated weak-pairing hypotheses. (`tent_move`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L15)).

**Split a rectangle at a radial interface.** Proved result. Under the declaration's hypotheses, the integral of a function defined piecewise across a radial interface is the sum of its two rectangle integrals. (`split_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L26)).

**Split a rectangle at a height interface.** Proved result. Under the declaration's hypotheses, the integral of a function defined piecewise across a height interface is the sum of its two rectangle integrals. (`split_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L49)).

**Symmetrically enclose a trace rectangle.** Proved result. Under the declaration's hypotheses, the trace rectangle lies in the stated box beginning at radius zero and symmetric in height. (`big_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L72)).

**Enclose an off-axis trace rectangle.** Proved result. The trace rectangle lies in the stated box with the same radial range and symmetric height limits. (`off_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L79)).

**Radial trace integrability on rectangles.** Proved result. Under the declaration's hypotheses, the radial weak-trace integrand multiplied by the line test is integrable on the selected radial-height rectangle. (`radial_term_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L84)).

**Radial traces ignore the auxiliary tent.** Proved result. Under the declaration's hypotheses, using the left or right auxiliary radial endpoint gives the same radial strip trace. (`radial_tent`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L104)).

**Equal face data give equal moments.** Proved result. Under the declaration's hypotheses, two valid face segments with the same face geometry and test coefficients have the same weak moment. (`seg_indep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L117)).

**The corner trace term is integrable.** Proved result. Under the declaration's hypotheses, the mixed weak-corner integrand is integrable on the selected rectangle. (`corner_term_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L149)).

**Corner trace as a rectangle integral.** Proved result. The weak corner value is the rectangle integral of its mixed trace integrand multiplied by the two endpoint orientation signs. (`corner_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L181)).

**A corner ignores its opposite radius.** Proved result. Under the declaration's hypotheses, the weak corner value is unchanged by replacing the auxiliary opposite radial endpoint. (`corner_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L186)).

**A corner ignores its opposite height.** Proved result. Under the declaration's hypotheses, the weak corner value is unchanged by replacing the auxiliary opposite height endpoint. (`corner_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L201)).

**Normalize auxiliary corner endpoints.** Proved result. Under the declaration's hypotheses, the weak corner value can use auxiliary endpoints one unit beyond the corner in each coordinate. (`corner_normal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L222)).

**The true weight flag selects radius.** Proved result. Under the declaration's hypotheses, the true weight flag produces the radial weight in the height weak derivative pair. (`wt_true`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L248)).

**false weight flag selects unit weight.** Proved result. Under the declaration's hypotheses, the false weight flag produces the unit weight in the height weak derivative pair. (`wt_false`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L252)).

**The radial derivative of head pressure.** Proved result. Under the declaration's hypotheses, the normalized pressure mode and its radial pressure-gradient mode form a radial weak derivative pair. (`head_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L256)).

**The height derivative of head pressure.** Proved result. Under the declaration's hypotheses, the normalized pressure mode and its axial gradient form the radially weighted height weak derivative pair. (`head_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L260)).

**Local traces ignore auxiliary endpoints.** Proved result. For local second-order data with a gradient pressure field, side, corner and zero-mode axial trace moments are independent of the auxiliary opposite endpoints whenever the stated face geometry agrees. (`trace_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L265)).

**Harmonic traces ignore the auxiliary end.** Proved result. Under the declaration's hypotheses, the local trace-independence results and harmonic lift give the harmonic trace-independence interface. (`harmonicTraceIndependence_of_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTrace.lean#L322)).

### Breakdown.CertCell.RowsMatchTracePairs

Supply the weak derivative pairs needed for velocity, gradient, corner and pressure trace independence. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**trace data have the integrability.** Proved result. Under the declaration's hypotheses, the velocity and gradient modes and the radially weighted Hessian modes are integrable on the required rectangle. (`modes_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L27)).

**Integrable bounded radial products.** Proved result. Under the declaration's hypotheses, multiplying the function by radius preserves integrability on the selected set under the stated radial bound. (`weight_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L53)).

**Remove weighted integrability off axis.** Proved result. Under the declaration's hypotheses, integrability of the radius-weighted coefficient implies integrability of the coefficient on the bounded strip away from the axis. (`off_of_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L57)).

**Velocity and its radial weak derivative.** Proved result. Under the declaration's hypotheses, a velocity mode and its radial gradient coefficient form a radial weak derivative pair. (`vel_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L63)).

**Velocity and its height weak derivative.** Proved result. Under the declaration's hypotheses, a velocity mode and its height gradient coefficient form an unweighted height weak derivative pair. (`vel_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L70)).

**Weak slopes of radial gradient modes.** Proved result. Under the declaration's hypotheses, the radial gradient mode and its radial second-derivative mode form a radial weak derivative pair. (`grad_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L86)).

**Height gradient and its weak derivative.** Proved result. Under the declaration's hypotheses, the height-gradient mode and its height second derivative form the radially weighted height weak derivative pair. (`grad_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L92)).

**Mixed weak derivatives of velocity modes.** Proved result. Under the declaration's hypotheses, the velocity mode, its two first derivatives and mixed second derivative satisfy the mixed weak-corner conditions. (`corner_quad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L110)).

**Local pressure-gradient integrability.** Proved result. Under the declaration's hypotheses, pairing the pressure-gradient field with a fixed coordinate unit vector gives a locally integrable scalar function. (`inner_cols_locInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L120)).

**Constant shifts keep local integrability.** Proved result. Under the declaration's hypotheses, subtracting a constant from the chosen weak potential preserves local integrability. (`shifted_locInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L131)).

**Radial derivatives of shifted pressure.** Proved result. Under the declaration's hypotheses, subtracting a constant from the potential preserves the radial weak derivative relation with the pressure-gradient mode. (`pres_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L136)).

**Height derivatives of shifted pressure.** Proved result. Under the declaration's hypotheses, subtracting a constant from the potential preserves the weighted height weak derivative relation with the pressure-gradient mode. (`pres_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/RowsMatchTracePairs.lean#L159)).

### Breakdown.CertCell.ScalarHeightCylinderMeasure

Set up cylindrical measures and polynomial angular tests for weak scalar height derivatives. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Rotate a half-plane point cylindrically.** Proved result. Axial rotation of the embedded half-plane point equals the cylindrical coordinate map at the same radius and height. (`axialRot_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L17)).

**Cylindrical coordinates from polar data.** Proved result. The cylindrical point is the spatial embedding of the inverse planar polar coordinates and the height. (`cylPoint_eq_toSpace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L22)).

**Cylindrical point is continuous.** Proved result. The cylindrical coordinate point is continuous. (`continuous_cylPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L28)).

**Cylindrical point is measurable.** Proved result. Under the hypotheses of this declaration, the cylindrical coordinate point is measurable. (`measurable_cylPoint_comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L38)).

**One time period of spacetime measure.** Definition. Use product volume restricted to one unit time period. (`slabMeasure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L45)).

**Time-angle-height product measure.** Definition. Use one time period, one angular period and the full height line. (`boxMeasure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L47)).

**Cylindrical product measure.** Definition. Add the positive radial coordinate to the time-angle-height product measure. (`cellMeasure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L50)).

**Cylindrical coordinates in spacetime.** Definition. Map radius, time, angle and height to the corresponding spacetime point. (`cellMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L52)).

**Cylindrical map is measurable.** Proved result. The cylindrical spacetime coordinate map is measurable. (`measurable_cellMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L55)).

**Nonnegative cylindrical integration.** Proved result. Under the declaration's hypotheses, the nonnegative cylindrical integral with radial Jacobian equals the one-period spacetime integral. (`lintegral_cellMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L62)).

**Radius is the cylindrical volume density.** Proved result. The cylindrical spacetime map preserves measure when the product coordinate measure is weighted by the radius. (`cellMap_measurePreserving`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L117)).

**Positive cylindrical radius a.e..** Proved result. The cylindrical product measure assigns positive radius to almost every point. (`cell_ae_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L126)).

**Cylindrical change of variables.** Proved result. Under the declaration's hypotheses, the one-period spacetime integral equals the cylindrical-coordinate integral of the pulled-back function multiplied by radius. (`integral_slab_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L130)).

**Integrability with the radial Jacobian.** Proved result. Under the declaration's hypotheses, the spacetime integrand pulled back to cylindrical coordinates and multiplied by radius is integrable for the cylindrical product measure. (`integrable_cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L140)).

**Integrable slices at almost every radius.** Proved result. For almost every positive radius, the pulled-back spacetime function is integrable over time, angle and height. (`ae_integrable_slice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L151)).

**Separate radius in a spacetime integral.** Proved result. Under the declaration's hypotheses, the one-period spacetime integral equals the positive-radius integral of radius times the inner time-angle-height integral. (`integral_slab_iter`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L158)).

**radial iterated integral is integrable.** Proved result. Under the declaration's hypotheses, the inner time-angle-height integral multiplied by radius is integrable over the positive radial axis. (`integrable_slab_iter`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L163)).

**Restricted measure on one time period.** Proved result. The period-slab measure equals spacetime volume restricted to the unit time interval. (`slab_eq_restrict`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L168)).

**Measurability on the time slab.** Proved result. Under the declaration's hypotheses, the spacetime function is almost everywhere strongly measurable for the one-period slab measure. (`aestronglyMeasurable_slab`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L171)).

**Integrable scalar-gradient pairings.** Proved result. Under the declaration's hypotheses, the weighted sum of the scalar field and its axial derivative is integrable over the one-period spacetime slab. (`integrable_slab_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L176)).

**Distance to the axis.** Definition. Take the square root of the sum of the first two coordinate squares. (`planeRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L256)).

**The signed angular imaginary unit.** Definition. Choose minus i for nonnegative angular frequency and plus i otherwise. (`turnSign`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L258)).

**A polynomial angular Fourier test.** Definition. Raise the signed complex planar coordinate to the absolute angular frequency. (`turnPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L260)).

**Smooth spatial coordinate projections.** Proved result. Each coordinate projection from three-dimensional space to the reals is smooth. (`contDiff_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L262)).

**Axis distance is continuous.** Proved result. The distance from the axis is continuous. (`continuous_planeRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L265)).

**The angular polynomial is smooth.** Proved result. The complex angular polynomial of every integer frequency is smooth on all of space. (`contDiff_turnPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L269)).

**first cylindrical coordinate is r cos θ.** Proved result. The first spatial coordinate of the cylindrical point is radius times the cosine of its angle. (`cylPoint_apply_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L274)).

**second cylindrical coordinate is r sin θ.** Proved result. The second spatial coordinate of the cylindrical point is radius times the sine of its angle. (`cylPoint_apply_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L277)).

**third cylindrical coordinate is height.** Proved result. The third spatial coordinate of the cylindrical point is its height parameter. (`cylPoint_apply_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L280)).

**Recover a nonnegative cylindrical radius.** Proved result. Under the declaration's hypotheses, the distance to the axis of a cylindrical point equals its nonnegative radial parameter. (`planeRadius_cylPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L283)).

**angular test separates radius and phase.** Proved result. On a cylindrical point, the angular polynomial equals radius to the absolute frequency times the negative angular Fourier exponential. (`turnPoly_cylPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L292)).

**Every coordinate is bounded by the norm.** Proved result. The absolute value of each spatial coordinate is at most the vector norm. (`abs_coord_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L327)).

**Bound the angular polynomial by radius.** Proved result. The norm of the angular polynomial of frequency k is at most the absolute angular-frequency power of twice the spatial norm. (`norm_turnPoly_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L331)).

**Bound norm by planar radius and height.** Proved result. The spatial norm is at most the distance from the axis plus the absolute height. (`norm_le_planeRadius_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L347)).

**Axial translation changes only height.** Proved result. Adding a multiple of the axial unit vector changes the third spatial coordinate by that multiple and leaves the other coordinates unchanged. (`shift_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L357)).

**Axial shifts preserve planar radius.** Proved result. Translating a spatial point along the axis leaves its distance from the axis unchanged. (`planeRadius_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L361)).

**Angular polynomials ignore axial shifts.** Proved result. The angular polynomial has the same value after any translation along the axis. (`turnPoly_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightCylinderMeasure.lean#L365)).

### Breakdown.CertCell.ScalarHeightDerivative

Obtain the scalar-mode weak height derivative on almost every radial slice using dense test pairs. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Integrable scalar slices.** Proposition definition. Require the scalar and height derivative to be integrable on every bounded height part of the time-angle slice. (`sliceGood`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L16)).

**Almost every scalar slice is integrable.** Proved result. Under the declaration's hypotheses, almost every positive-radius slice satisfies the bounded-height integrability conditions for the scalar and its height derivative. (`ae_sliceGood`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L23)).

**The angular Fourier factor is periodic.** Proved result. The time-angle Fourier factor is periodic with angular period 2π. (`modeFactor_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L86)).

**A full turn leaves the point unchanged.** Proved result. Adding 2π to the angular parameter leaves the corresponding rotated or cylindrical point unchanged. (`cylPoint_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L96)).

**Scalar plane mode on a symmetric orbit.** Proved result. The scalar plane average equals the normalized temporal and angular Fourier integral along the cylindrical orbit with angle between minus pi and pi. (`modeAverage_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L100)).

**Separate time and angular integration.** Proved result. Under the declaration's hypotheses, at fixed height, the product-measure integral equals the iterated integral over one time period and the symmetric full angular period. (`box_slice_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L116)).

**Pair Fourier averages with height tests.** Proved result. Under the declaration's hypotheses, the fixed-radius scalar mode is integrable on the height interval, and pairing it with a continuous supported height test equals the corresponding full time-angle-height integral divided by two pi. (`slice_mode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L126)).

**Height pairing is continuous in the test.** Proved result. Under the declaration's hypotheses, integrating a fixed integrable height coefficient against a continuous real test over the closed interval gives a continuous complex-valued functional of the test. (`continuous_setIntegral_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L199)).

**Compact smooth height-test pairs.** Definition. Collect continuous pairs consisting of a smooth supported height test and its derivative. (`testPairs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L224)).

**Countable tests determine height slopes.** Proved result. There is a countable set of smooth compactly supported height tests whose weak identities imply the identity for all such tests for locally integrable function and derivative candidates. (`line_test_density`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L227)).

**Height defect as a line pairing.** Proved result. Under the declaration's hypotheses, the line moment equals two pi times the sum of the scalar-mode pairing with the height test derivative and the height-mode pairing with the test. (`lineMoment_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L277)).

**Weak height derivatives of scalar modes.** Proved result. Scalar plane modes have the stated weak height derivatives on almost every radial slice. (`scalarHeightDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightDerivative.lean#L299)).

### Breakdown.CertCell.ScalarHeightRadialTest

Localize the scalar weak derivative with radial and angular tests before passing to individual radial slices. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Vanishing near the radial origin.** Proved result. If a function's topological support lies in the positive real axis, it vanishes below some strictly positive radius. (`eq_zero_near_origin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L18)).

**Smooth radial cutoffs away from the axis.** Proved result. Under the declaration's hypotheses, a smooth radial cutoff supported away from radius zero remains smooth when composed with distance from the axis. (`contDiff_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L29)).

**Differentiate a height-invariant factor.** Proved result. Under the declaration's hypotheses, the axial derivative of the product differentiates only the height test when the other factor is height invariant. (`fderiv_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L46)).

**Function f is locally integrable.** Proved result. Under the hypotheses of this declaration, the function f is locally integrable. (`locallyIntegrable_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L69)).

**Local integrability of the axial slope.** Proved result. Under the declaration's hypotheses, the axial coordinate of the scalar gradient is locally integrable in space. (`locallyIntegrable_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L76)).

**Real weak axial differentiation.** Proved result. Under the declaration's hypotheses, the integral of a scalar test times the axial derivative equals minus the integral of the scalar field times the axial test derivative. (`weak_height_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L85)).

**Bound the support of a height test.** Proved result. Under the declaration's hypotheses, the height test's topological support lies in the specified symmetric closed interval. (`tsupport_subset_Icc`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L101)).

**Test derivatives vanish far away.** Proved result. If a line test is zero whenever absolute height exceeds N, its derivative is also zero at every such height. (`deriv_eq_zero_of_far`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L111)).

**Weighted height integration by parts.** Proved result. Under the declaration's hypotheses, the supported weighted sum of the scalar axial derivative times the height test and the scalar field times the test derivative is integrable and has zero integral. (`weak_height_part`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L120)).

**The temporal Fourier exponential.** Definition. Use the negative exponential at the chosen integer temporal frequency. (`timeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L158)).

**The time-angle Fourier exponential.** Definition. Use the negative exponential combining temporal and angular frequency. (`modeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L160)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`norm_timeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L163)).

**Complex Fourier phases have norm one.** Proved result. The complex exponential of the stated imaginary real phase has norm one. (`norm_modeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L168)).

**Temporal phase is continuous.** Proved result. The temporal Fourier factor is continuous. (`continuous_timeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L173)).

**Time-angle phase is continuous.** Proved result. The time-angle Fourier factor is continuous. (`continuous_modeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L177)).

**Multiply time and angular Fourier phases.** Proved result. Multiplying the temporal Fourier factor by the angular Fourier exponential gives the joint time-angle factor. (`timeFactor_mul_turn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L181)).

**The localized scalar weak derivative.** Definition. Multiply the scalar weak height-derivative expression by the radial cutoff and angular polynomial. (`radialIntegrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L188)).

**The scalar weak height moment.** Definition. Integrate the Fourier-weighted scalar weak derivative expression over time, angle and height. (`lineMoment`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L193)).

**The complex radial-height test identity.** Proved result. Under the declaration's hypotheses, multiplying the scalar weak height derivative identity by the supported radial cutoff and angular polynomial gives a zero complex spatial integral. (`weak_height_complex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L198)).

**The radial defect has zero slab integral.** Proved result. Under the declaration's hypotheses, the radial test integrand has zero one-period spacetime integral when almost every time slice satisfies the scalar weak gradient identity. (`integral_radialIntegrand_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L230)).

**Compact line support has a finite radius.** Proved result. Under the declaration's hypotheses, a compactly supported line test vanishes outside some symmetric interval with nonnegative radius. (`exists_support_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L249)).

**Bounded support gives compact support.** Proved result. Under the declaration's hypotheses, a line function that vanishes outside a bounded symmetric interval has compact support. (`hasCompactSupport_of_far`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L257)).

**Slab integrability of radial weak tests.** Proved result. Under the declaration's hypotheses, the radial cutoff, angular phase and height weak-derivative combination is integrable on the one-period spacetime slab. (`integrable_radialIntegrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L265)).

**Cylindrical coordinates for scalar tests.** Proved result. Under the declaration's hypotheses, the localized scalar weak-derivative integrand separates into the radial cutoff times its frequency power and the time-angle-height integrand. (`radialIntegrand_cellMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L331)).

**Radial test isolates the height defect.** Proved result. Under the declaration's hypotheses, integrating the radial test integrand over time, angle and height gives the radial test value times radius to the absolute angular frequency times the height line moment. (`integral_cell_radialIntegrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L341)).

**Height defects vanish at most radii.** Proved result. Under the declaration's hypotheses, the scalar Fourier height-test defect vanishes at almost every positive radius under local spacetime square integrability and the slice weak-gradient assumptions. (`ae_lineMoment_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarHeightRadialTest.lean#L348)).

### Breakdown.CertCell.ScalarPlaneFlip

Transfer scalar reflection and the sign change of the weak height derivative to plane modes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Height reversal reflects angular modes.** Proved result. Under the declaration's hypotheses, the scalar plane mode at opposite height equals the mode with reflected angular frequency at the original point. (`planeScalar_neg_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneFlip.lean#L22)).

**Scalar modes reflect by reversing height.** Proved result. For almost every positive radius and almost every height, the reflected-frequency scalar mode equals the original-frequency scalar mode at the opposite height. (`ae_planeScalar_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneFlip.lean#L61)).

**Negate a symmetric interval integrand.** Proved result. Composing an integrand with negation leaves its integral over the symmetric open interval unchanged. (`setIntegral_symm_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneFlip.lean#L78)).

**Integrability under interval negation.** Proved result. Under the declaration's hypotheses, an integrable function on the symmetric open interval remains integrable there after precomposition with negation. (`integrableOn_symm_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneFlip.lean#L89)).

**Reflection negates the height derivative.** Proved result. Under the declaration's hypotheses, almost everywhere on the symmetric interval, the weak derivative of the reflected function is minus the original derivative evaluated at negative height. (`weakDeriv_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneFlip.lean#L100)).

**Scalar modes and derivatives reflect.** Proved result. Under the hypotheses of this declaration, scalar modes reflect in height and their weak height derivatives acquire the corresponding minus sign. (`scalarPlaneFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneFlip.lean#L161)).

### Breakdown.CertCell.ScalarPlaneMin

Verify measurability and symmetry of the lower equatorial chart value and its scalar enclosure. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Upper chart value is measurable.** Proved result. For any chart parameters and piecewise constant datum, the scalar value obtained from the upper chart is a measurable function of y ∈ R³. (`upperValue_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L21)).

**Lower chart value is measurable.** Proved result. For any chart parameters and piecewise constant datum, the scalar value obtained from the lower chart is a measurable function of y ∈ R³. (`lowerValue_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L27)).

**Rotation-invariant upper chart values.** Proved result. Axial rotation leaves the upper chart value unchanged. (`upperValue_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L33)).

**Rotation-invariant lower chart values.** Proved result. Axial rotation leaves the lower chart value unchanged. (`lowerValue_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L37)).

**Reflection swaps upper and lower charts.** Proved result. The upper chart value of mirrored step data at a reflected point equals the original lower chart value. (`mirror_upperValue_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L41)).

**Reflection swaps lower and upper charts.** Proved result. The lower chart value of mirrored step data at a reflected point equals the original upper chart value. (`mirror_lowerValue_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L46)).

**Lower equatorial value is measurable.** Proved result. The lower equatorial chart value is measurable. (`planeMinEval_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L51)).

**The lower equatorial bound is invariant.** Proved result. Axial rotation leaves the lower equatorial chart value unchanged. (`planeMinEval_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L60)).

**Reflection preserves chart minima.** Proved result. Mirroring the step data and reflecting the point together preserve the lower equatorial chart evaluation. (`planeMinEval_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L64)).

**Rotation is zero only at the origin.** Proved result. An axial rotation of a spatial point is zero exactly when the original point is zero. (`axialRot_eq_zero_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L75)).

**Reflection is zero only at the origin.** Proved result. A reflected spatial point is zero exactly when the original point is zero. (`flipPoint_eq_zero_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L78)).

**Lower chart values respect symmetry.** Proved result. The lower equatorial chart value is measurable and obeys rotation and reflection symmetry. (`planeMinEvalFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L85)).

**Scalar chart enclosures are valid.** Proved result. The scalar chart enclosures have the required measurability and symmetry properties. (`chartBoundFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ScalarPlaneMin.lean#L88)).

### Breakdown.CertCell.SecondDerivEnergyIdentity

Prove equality of the full Hessian energy and the trace energy by smoothing and passage to the limit. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A coordinate directional derivative.** Definition. Apply the Fréchet derivative to the selected coordinate unit vector. (`partialOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L14)).

**Scalar convolution for smoothing.** Definition. Convolve the two scalar functions with respect to spatial volume. (`conv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L17)).

**Partial derivative is smooth.** Proved result. Under the hypotheses of this declaration, the coordinate directional derivative is smooth. (`partialOf_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L20)).

**Partial derivative has compact support.** Proved result. Under the hypotheses of this declaration, the coordinate directional derivative has compact support. (`partialOf_hasCompactSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L24)).

**Coordinate derivatives commute.** Proved result. Under the declaration's hypotheses, the two coordinate directional derivatives of a smooth test commute. (`partialOf_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L28)).

**Differentiate convolution in its kernel.** Proved result. Under the declaration's hypotheses, the coordinate directional derivative of the convolution equals convolution with the corresponding derivative of the smooth factor. (`conv_hasLineDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L43)).

**Transfer weak derivatives to the kernel.** Proved result. Under the declaration's hypotheses, convolving the weak derivative with the test equals convolving the original function with the test's coordinate derivative. (`conv_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L57)).

**Weighted integral Cauchy-Schwarz.** Proved result. For nonnegative measurable weights, the square of the integral of their product is bounded by the first weight's integral times the integral of that weight multiplied by the square of the second. (`lintegral_mul_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L76)).

**Convolution has the squared L1 bound.** Proved result. Under the declaration's hypotheses, the integral of the squared convolution norm is at most the squared L1 kernel norm times the integral of the squared input norm. (`conv_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L103)).

**Finite squared norm gives L2 membership.** Proved result. Under the declaration's hypotheses, an almost everywhere measurable scalar function with finite integral of its squared norm belongs to spatial L2. (`memLp_two_of_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L135)).

**Finite mass for supported smooth tests.** Proved result. Under the declaration's hypotheses, the nonnegative integral of the norm of the supported smooth factor is finite. (`lintegral_enorm_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L139)).

**Convolution keeps square integrability.** Proved result. Under the declaration's hypotheses, convolution of a square-integrable function with the admissible integrable kernel remains square integrable. (`conv_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L143)).

**Convolve a finite sum term by term.** Proved result. Under the declaration's hypotheses, convolving a finite sum of integrable terms with a fixed kernel gives the sum of their convolutions. (`conv_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L151)).

**Embed a real square in extended norms.** Proved result. For a real scalar, the squared extended norm equals the nonnegative-real embedding of its square. (`enorm_sq_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L158)).

**Exchange derivatives in a smooth pairing.** Proved result. Under the declaration's hypotheses, the integral of the square of one differentiated convolution equals the integral of the corresponding pair of diagonal differentiated convolutions. (`smooth_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L161)).

**Equal smoothed Hessian and trace energy.** Proved result. Under the declaration's hypotheses, the integral of the sum of squared mollified Hessian entries equals the integral of the squared sum of its mollified diagonal entries. (`mollified_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L205)).

**A sequence of shrinking smooth bumps.** Definition. Choose smooth bumps with outer radii tending to zero. (`bumpSeq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L251)).

**A normalized shrinking mollifier.** Definition. Normalize the shrinking smooth bump to obtain the mollifier. (`mollifier`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L257)).

**Mollifier is smooth.** Proved result. The normalized mollifier is smooth. (`mollifier_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L259)).

**Mollifier has compact support.** Proved result. The normalized mollifier has compact support. (`mollifier_hasCompactSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L262)).

**The mollifier has unit mass.** Proved result. The nonnegative integral of the norm of each mollifier is one. (`mollifier_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L265)).

**Mollification decreases L2 energy.** Proved result. Under the declaration's hypotheses, convolution with the unit-mass mollifier does not increase the integral of the squared function norm. (`mollifier_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L274)).

**Mollified values converge a.e..** Proved result. Under the declaration's hypotheses, convolution with the normalized shrinking mollifiers tends to the original function almost everywhere. (`mollifier_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L280)).

**A.e. limits keep integral bounds.** Proved result. If nonnegative measurable functions converge almost everywhere and their integrals share an upper bound, the limit integral has the same bound. (`lintegral_le_of_ae_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L290)).

**Scalar Hessian and trace energies agree.** Proved result. Under the declaration's hypotheses, the integral of the sum of squared weak Hessian entries equals the integral of the squared trace. (`scalar_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L298)).

**Local integrability under linear maps.** Proved result. Under the declaration's hypotheses, applying a fixed continuous linear map to a locally integrable function preserves local integrability. (`locallyIntegrable_clm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L345)).

**Extract scalar weak derivative formulas.** Proved result. Under the declaration's hypotheses, each coordinate of a vector weak derivative satisfies the corresponding scalar test-function integration by parts identity. (`coord_weak`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L353)).

**Norm squared as a coordinate square sum.** Proved result. The squared Euclidean norm equals the sum of the squares of its coordinates. (`norm_sq_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L369)).

**A coordinate square is norm bounded.** Proved result. The square of any coordinate is bounded by the squared Euclidean norm. (`coord_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L373)).

**A coordinate commutes with a finite sum.** Proved result. Taking one coordinate of a finite vector sum equals summing that coordinate. (`coord_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L377)).

**Embed finite sums of nonnegative squares.** Proved result. Embedding a finite triple sum of real squares into the extended nonnegative reals equals the triple sum of their embeddings. (`ofReal_triple_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L380)).

**Hessian and Laplacian energies agree.** Proved result. Under the declaration's hypotheses, the spatial integral of the Hessian Frobenius square equals the spatial integral of the squared norm of its trace. (`slice_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L390)).

**Hessian and trace have equal energy.** Proved result. For an admissible perturbation, the one-period spacetime integral of the full Hessian square equals the one-period spacetime integral of its trace square. (`secondDerivEnergyIdentity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SecondDerivEnergyIdentity.lean#L442)).

### Breakdown.CertCell.ShapeActuator

Turn compact shaped forcing fields into the actuator regularity and energy facts required by the certificate. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Restrict derivatives to spatial inputs.** Proved result. Under the declaration's hypotheses, the derivative of a fixed-time spatial slice is the joint derivative composed with the spatial inclusion. (`partial_fderiv_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeActuator.lean#L16)).

**Compact support gives finite period mass.** Proved result. Under the declaration's hypotheses, a real density bounded above everywhere and nonpositive outside a fixed spatial ball has finite nonnegative one-period integral. (`periodLIntegral_lt_top_of_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeActuator.lean#L21)).

**Decay gives a uniform upper bound.** Proved result. Under the declaration's hypotheses, the stated estimate by a nonnegative quantity divided by one plus a nonnegative term implies the same uniform upper bound. (`le_of_le_div_one_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeActuator.lean#L47)).

**Bound entry energy by the operator norm.** Proved result. The sum of squared matrix-column norms is bounded by the squared operator norm times the sum of squared basis-vector norms. (`matSq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeActuator.lean#L54)).

**classical derivative is a weak gradient.** Proved result. Under the declaration's hypotheses, a continuously differentiable field has its Fréchet derivative as its weak gradient. (`isWeakGradient_of_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeActuator.lean#L62)).

**Regularity from shape interfaces.** Proved result. Under the declaration's hypotheses, the listed shape proofs supply the regularity, symmetry and integrability facts required of a forcing field. (`actuatorFacts_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeActuator.lean#L80)).

**Shaped forcing fields meet the interface.** Proved result. Under the hypotheses of this declaration, the shaped forcing fields satisfy the actuator regularity and support requirements. (`actuatorShape_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeActuator.lean#L131)).

### Breakdown.CertCell.ShapeAngularFactor

Prove that the polar vanishing factor removes the angular singularity with the stated differentiability order. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Derivative decay removes the origin.** Proved result. A function vanishing at the origin is n times continuously differentiable globally if it has that regularity off the origin and each derivative of order a at most n is bounded by a constant times radius to the power n plus one minus a. (`contDiff_of_bounds_off_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L23)).

**Homogeneity bounds derivatives.** Proved result. Under the declaration's hypotheses, a positively homogeneous function of degree d with a continuous derivatives off the origin has its derivative of order a bounded there by a constant times radius to the power d minus a when a is at most d. (`norm_iteratedFDeriv_le_of_homogeneous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L84)).

**Homogeneity removes the singularity.** Proved result. Under the declaration's hypotheses, a function homogeneous of degree n plus one, zero at the origin and n times continuously differentiable away from it is n times continuously differentiable everywhere. (`contDiff_of_homogeneous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L140)).

**Radial fourth powers smooth angular data.** Proved result. The complex function given by the fourth power of the modulus times any natural-number power of the normalized complex direction has three continuous derivatives on the whole plane. (`homogeneousPower_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L146)).

**Regularity of the complex coordinate.** Proved result. Combining the first two spatial coordinates as a complex number defines a function with three continuous derivatives. (`planeCoord_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L161)).

**Cartesian form of the angular factor.** Proved result. Under the declaration's hypotheses, the polar vanishing factor times its angular phase equals the Cartesian homogeneous expression with fourth-power radial cancellation. (`angularFactor_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L168)).

**Three derivatives of the angular phase.** Proved result. Under the declaration's hypotheses, at every nonzero spatial point, the polar vanishing factor times the integer angular phase has three continuous derivatives locally. (`angularFactor_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L214)).

**Angular regularity away from the origin.** Proved result. The polar vanishing factor times the angular phase has three continuous derivatives on space with the origin removed. (`angularFactor_contDiffOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L243)).

**The polar factor kills the nonzero axis.** Proved result. Under the declaration's hypotheses, at a nonzero point on the axis, the polar vanishing factor times any integer angular phase is zero. (`angularFactor_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeAngularFactor.lean#L248)).

### Breakdown.CertCell.ShapeClosureData

Complete representative harmonic amplitudes under conjugation and reflection while preserving spline compatibility. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Conjugate-key negation is an involution.** Proved result. Negating the harmonic key twice returns the original key. (`negKey_negKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L19)).

**Key reflection is an involution.** Proved result. Reflecting the harmonic key twice returns the original key. (`flipKey_flipKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L23)).

**Key reflection commutes with negation.** Proved result. Reflecting and negating a harmonic key commute. (`flipKey_negKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L28)).

**Reflection fixes zero angular keys.** Proved result. Under the declaration's hypotheses, a field key whose first label coordinate is zero equals its reflected key. (`flipKey_of_fst_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L37)).

**Move a key in its symmetry orbit.** Definition. Apply the selected combination of key negation and spatial reflection. (`orbitMove`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L43)).

**Move amplitudes by the same symmetry.** Definition. Apply the selected combination of complex conjugation and spline reflection to the amplitude data. (`ampMove`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L49)).

**An exclusive-or operation cancels twice.** Proved result. Applying exclusive-or twice with the same Boolean value returns the original Boolean value. (`xor_xor_cancel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L55)).

**An exclusive-or operation cancels twice.** Proved result. Applying exclusive-or twice with the same Boolean value returns the original Boolean value. (`xor_xor_cancel_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L58)).

**Compose key symmetries by exclusive-or.** Proved result. Composing two key symmetry actions combines their conjugation and reflection flags by exclusive-or. (`orbitMove_orbitMove`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L61)).

**Each key symmetry is an involution.** Proved result. Applying the same selected key symmetry twice returns the original key. (`orbitMove_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L66)).

**Key symmetries compose by exclusive-or.** Proved result. Applying the conjugation and reflection switches after an existing key symmetry composes their Boolean flags by exclusive-or. (`orbitMove_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L69)).

**Key symmetries keep zero angular mode.** Proved result. A key transformed by any conjugation-reflection switches has zero first label coordinate exactly when the original key does. (`fst_orbitMove_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L73)).

**Zero angular keys ignore reflection.** Proved result. For a key with first label coordinate zero, the reflection flag has no effect on its symmetry action. (`orbitMove_of_fst_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L77)).

**Membership in the key symmetry closure.** Proved result. A key belongs to the orbit closure exactly when one of its conjugation-reflection transforms belongs to the original finite key set. (`mem_orbitClosure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L81)).

**The completed orbit is symmetry closed.** Proved result. Under the declaration's hypotheses, applying a key symmetry keeps the key in the completed symmetry orbit. (`orbitMove_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L105)).

**Closed amplitudes from representatives.** Proved result. Under the declaration's hypotheses, every closed amplitude is obtained by applying a recorded symmetry to the amplitude of a representative key. (`closureAmp_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L110)).

**Distinct representatives share no orbit.** Proved result. Under the declaration's hypotheses, a symmetry taking one chosen representative to another must fix that representative under the uniqueness hypothesis. (`orbitMove_eq_of_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L125)).

**A symmetry-compatible amplitude relation.** Proposition structure. Require an equivalence relation on amplitudes compatible with conjugation, reflection and their group identities. (`IsAmpRel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L133)).

**Amplitude symmetry preserves agreement.** Proved result. Under the declaration's hypotheses, equivalent amplitudes remain equivalent after the selected conjugation and reflection. (`ampMove_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L143)).

**Compose amplitude symmetries by parity.** Proved result. Under the declaration's hypotheses, two amplitude symmetry actions agree, in the stated relation, with the action obtained by combining their Boolean parities. (`ampMove_ampMove`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L151)).

**Closure respects representatives.** Proved result. Under the declaration's hypotheses, the amplitude chosen by closure is equivalent to the transformed amplitude of any valid representative. (`closureAmp_rel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L180)).

**Amplitude closure respects key symmetry.** Proved result. Under the declaration's hypotheses, closing amplitudes after moving the key agrees with moving the already closed amplitude. (`closureAmp_move_rel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L194)).

**Amplitude symmetry keeps the lower order.** Proved result. Conjugation and reflection leave the amplitude's lower endpoint order unchanged. (`ampMove_lowOrder`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L207)).

**Amplitude symmetry keeps the upper order.** Proved result. Conjugation and reflection leave the amplitude's upper endpoint order unchanged. (`ampMove_highOrder`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L210)).

**Spline agreement is reflexive.** Proved result. Every spline agrees with itself on its active pieces. (`agrees_refl'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L218)).

**Spline agreement is symmetric.** Proved result. Under the declaration's hypotheses, agreement of two splines on their active pieces holds in either order. (`agrees_symm'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L220)).

**Spline agreement is transitive.** Proved result. Under the declaration's hypotheses, two successive agreements on active spline pieces imply agreement of the first and third splines. (`agrees_trans'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L222)).

**Conjugation preserves spline agreement.** Proved result. Under the declaration's hypotheses, conjugating both splines preserves their agreement on active pieces. (`agrees_conj'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L225)).

**Reflection preserves spline agreement.** Proved result. Under the declaration's hypotheses, reflecting both splines with the same parity preserves agreement on active pieces. (`agrees_reflect'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L228)).

**Double conjugation recovers the spline.** Proved result. Conjugating a spline twice agrees with the original spline on active pieces. (`agrees_conj_conj'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L232)).

**Double reflection recovers the spline.** Proved result. Reflecting a spline twice with the same parity agrees with the original spline on active pieces. (`agrees_reflect_reflect'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L234)).

**Reflect and conjugate splines.** Proved result. Reflecting then conjugating agrees on active pieces with conjugating then reflecting. (`agrees_reflect_conj'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L237)).

**Spline agreement preserves joining.** Proved result. Under the declaration's hypotheses, agreement on active pieces transfers the specified derivative-joining conditions. (`joined_of_agrees'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L240)).

**Agreement of type-one amplitudes.** Proposition definition. Require radial and polar spline agreement and equal endpoint orders. (`TypeOneRel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L245)).

**Agreement of type-two amplitudes.** Proposition definition. Require stream and swirl spline agreement, equal axis coefficients and equal endpoint orders. (`TypeTwoRel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L249)).

**Type-one agreement respects symmetry.** Proved result. Under the declaration's hypotheses, agreement of radial and polar amplitudes with their endpoint orders is compatible with the amplitude symmetries. (`isAmpRel_typeOne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L253)).

**Type-two agreement respects symmetry.** Proved result. Under the declaration's hypotheses, agreement of stream and swirl amplitudes with axis coefficients and endpoint orders is compatible with amplitude symmetries. (`isAmpRel_typeTwo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L264)).

**Type-one stabilizers preserve amplitudes.** Proved result. Under the declaration's hypotheses, a symmetry fixing a nonzero-angular representative leaves its type-one amplitude unchanged up to spline agreement. (`stab_typeOne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L276)).

**Type-two stabilizers preserve amplitudes.** Proved result. Under the declaration's hypotheses, a symmetry fixing a zero-angular representative leaves its type-two amplitude unchanged up to spline agreement and its axis coefficient. (`stab_typeTwo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L291)).

**A full mesh has at least one cell.** Proved result. Under the declaration's hypotheses, the radial breakpoint list of a full tensor mesh determines a strictly positive number of cells. (`fullMesh_cellCount_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L310)).

**Conjugate before zero substitution.** Proved result. Conjugating all polynomial coefficients commutes with substituting zero for the first variable. (`atFirst_zero_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L323)).

**Transfer spline vanishing at the origin.** Proved result. If two splines agree and the comparison mesh is full, vanishing of its first radial pieces at radial coordinate zero transfers to the other spline. (`origin_of_agrees`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L331)).

**Conjugation preserves origin vanishing.** Proved result. Under the declaration's hypotheses, coefficientwise conjugation preserves vanishing of the first radial spline pieces at radial coordinate zero. (`origin_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L342)).

**Symmetry preserves derivative joins.** Proved result. Under the declaration's hypotheses, conjugation, reflection and their combination preserve the stated radial and polar joining orders. (`joined_reflect_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L353)).

**Symmetry preserves radial spline joins.** Proved result. Under the declaration's hypotheses, the radial amplitude retains its stated derivative-joining orders after the chosen symmetry action. (`ampMove_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L358)).

**Symmetry preserves polar spline joins.** Proved result. Under the declaration's hypotheses, the polar amplitude retains its stated derivative-joining orders after the chosen symmetry action. (`ampMove_polar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L367)).

**Symmetry preserves stream spline joins.** Proved result. Under the declaration's hypotheses, the stream amplitude retains its stated derivative-joining orders after the chosen symmetry action. (`ampMove_stream`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L376)).

**Symmetry preserves swirl spline joins.** Proved result. Under the declaration's hypotheses, the swirl amplitude retains its stated derivative-joining orders after the chosen symmetry action. (`ampMove_swirl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L385)).

**Symmetry closure preserves valid data.** Proved result. Under the hypotheses of this declaration, completing representative amplitudes by conjugation and reflection yields valid full harmonic data. (`closureDataValid_of_rules`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L401)).

**Symmetry closure preserves valid data.** Proved result. Completing representative amplitudes by conjugation and reflection yields valid full harmonic data. (`closureDataValid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeClosureData.lean#L506)).

### Breakdown.CertCell.ShapeCompactSupport

Convert vanishing final spline cells into compact spatial support of the shaped field. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Cell index after a passed breakpoint.** Proved result. If a point is at or beyond a valid breakpoint in a strictly increasing list, its selected cell index is at least that breakpoint index. (`le_cellIndex_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L15)).

**Later sorted entries keep a lower bound.** Proved result. Under the declaration's hypotheses, a lower bound for one entry of a strictly increasing list also bounds every later entry, including the fallback value one under the extra bound by one. (`le_getD_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L42)).

**Spline vanishing beyond a breakpoint.** Proved result. Under the declaration's hypotheses, a spline satisfying the prescribed vanishing condition evaluates to zero at and beyond any qualifying radial breakpoint below one. (`evalHalf_eq_zero_of_break`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L54)).

**Vanishing before the chart boundary.** Proved result. Under the declaration's hypotheses, a compactly supported spline has a radial chart level strictly below one beyond which all its half-chart evaluations vanish. (`exists_vanish_level`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L69)).

**Locally zero functions have zero slope.** Proved result. Under the declaration's hypotheses, a function that is zero on a neighborhood of a point has derivative zero at that point. (`deriv_zero_of_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L75)).

**Nonzero-mode amplitudes vanish far away.** Proved result. For a nonzero angular key, vanishing of the radial and polar spline amplitudes beyond a chart threshold forces all reduced components to vanish strictly beyond that threshold. (`reducedComps_typeOne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L80)).

**Zero-mode amplitudes vanish far away.** Proved result. For a zero angular key with zero axis coefficient, vanishing of the stream and swirl amplitudes beyond a threshold forces all reduced components to vanish strictly beyond it. (`reducedComps_typeTwo_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L102)).

**Large radius passes a chart breakpoint.** Proved result. For positive chart length and a breakpoint below one, radius greater than its inverse compactification threshold implies that the compactified radius exceeds that breakpoint. (`lt_chartCoord_of_radius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L124)).

**Each compact key vanishes outside a ball.** Proved result. For compact time-field data, every retained harmonic key field vanishes outside one fixed spatial ball uniformly in time. (`keyVector_vanish_far`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L133)).

**Final spline vanishing gives support.** Proved result. Vanishing final spline pieces give a compactly supported shaped field. (`compactFieldSupport_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeCompactSupport.lean#L159)).

### Breakdown.CertCell.ShapeDecayNear

Bound a continuously differentiable key field, its gradient and its totalized second derivative on closed balls using local Lipschitz bounds on the gradient. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Bounds through the totalized Hessian.** Proved result. Under the declaration's hypotheses, a continuously differentiable key field with locally Lipschitz gradient has a common bound on the field, its gradient and its totalized second Fréchet derivative on each closed ball. (`bounded_on_ball`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDecayNear.lean#L11)).

### Breakdown.CertCell.ShapeDefs

Define derivative splines, the logarithmic radial phase and the representative harmonic data conditions. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Differentiate the radial spline pieces.** Definition. Differentiate each spline piece once in its first chart variable while retaining the mesh. (`tDerivSpline`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDefs.lean#L22)).

**Differentiate the polar spline pieces.** Definition. Differentiate each spline piece once in its second chart variable while retaining the mesh. (`xDerivSpline`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDefs.lean#L24)).

**The logarithmic radial phase.** Definition. Use half the phase rate times the logarithm of one plus the squared-radius variable divided by the base scale squared. (`logRadialPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDefs.lean#L38)).

**Keys at one physical harmonic.** Definition. Filter the finite key set by its physical harmonic label. (`keysOfHarmonic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDefs.lean#L40)).

**Rotate a complex spatial vector.** Definition. Rotate the first two complex coordinates by a real angle and keep the third coordinate fixed. (`rotateVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDefs.lean#L43)).

**Reflect a complex spatial vector.** Definition. Keep the first complex coordinate and negate the second and third coordinates. (`flipVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDefs.lean#L46)).

**Valid representative harmonic data.** Proposition structure. Require one representative per symmetry orbit together with the spline classes, endpoint orders and symmetry conditions of its amplitudes. (`IsGivenKeyData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeDefs.lean#L48)).

### Breakdown.CertCell.ShapeFieldClass

Transfer the harmonic key symmetries to the real field symmetry class. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The real-part map acts coordinatewise.** Proved result. The selected coordinate of the real-part vector is the real part of the selected complex coordinate. (`realPartVec_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L14)).

**Real parts commute with reflection.** Proved result. Taking coordinatewise real parts of a reflected complex vector gives the spatial reflection of its real-part vector. (`realPartVec_flipVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L16)).

**Real parts commute with real rotation.** Proved result. Taking real parts after complex-vector axial rotation equals rotating the real-part vector. (`realPartVec_rotateVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L20)).

**Reflection distributes over finite sums.** Proved result. Reflecting a finite sum of complex vectors gives the sum of their reflections. (`flipVec_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L25)).

**Complex rotation distributes over sums.** Proved result. Rotating a finite sum of complex vectors gives the sum of their rotations. (`rotateVec_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L30)).

**Key reflection is an involution.** Proved result. Reflecting the harmonic key twice returns the original key. (`flipKey_flipKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L36)).

**Whole-turn phases equal one.** Proved result. Under the declaration's hypotheses, the complex exponential of an integer multiple of a full angular turn is one. (`exp_whole_turns`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L40)).

**Reflection of the complex harmonic field.** Proved result. Under the declaration's hypotheses, the finite complex harmonic field at a reflected point is the complex reflection of its original value. (`complexField_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L47)).

**A symmetry shift rotates one key field.** Proved result. Under the declaration's hypotheses, the admissible combined time shift and spatial rotation transforms the key field by the corresponding vector rotation. (`keyVector_turn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L65)).

**A symmetry shift rotates the whole field.** Proved result. Under the declaration's hypotheses, the admissible combined time shift and spatial rotation transforms the finite complex field by vector rotation. (`complexField_turn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L78)).

**shaped field has the symmetry.** Proved result. Under the hypotheses of this declaration, the represented real field lies in the prescribed symmetry class. (`fieldClassInvariant_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L89)).

**shaped field has the symmetry.** Proved result. Under the hypotheses of this declaration, the represented real field lies in the prescribed symmetry class. (`fieldClassInvariant_of_keyFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClass.lean#L110)).

### Breakdown.CertCell.ShapeFieldClassClosed

Close the symmetry-class interface from the established harmonic reflection and rotation rules. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**shaped field has the symmetry.** Proved result. The represented real field lies in the prescribed symmetry class. (`fieldClassInvariant_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldClassClosed.lean#L12)).

### Breakdown.CertCell.ShapeFieldDecay

Combine the uniform time phase and spatial estimates into decay bounds for the represented field. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**All times differ by a unit complex phase.** Proved result. The harmonic key field at time sigma is its time-zero field multiplied by the exponential of i times two pi times its temporal frequency times sigma. (`keyVector_time_eq_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldDecay.lean#L13)).

**Decay bounds uniform in time.** Proved result. Under the declaration's hypotheses, decay of a harmonic key field at time zero gives a common nonnegative constant controlling its velocity, gradient and Hessian at all times by the inverse first, second and third powers of one plus radius. (`keyVector_uniform_bounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldDecay.lean#L23)).

**The shaped field and Hessian decay.** Proved result. Under the hypotheses of this declaration, the shaped field, its gradient and its prescribed Hessian have uniform bounds by the inverse first, second and third powers of one plus radius. (`fieldDecay_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldDecay.lean#L54)).

### Breakdown.CertCell.ShapeFieldDiv

Supply the real-part and differentiability facts used to prove divergence-freeness of the represented field. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Read a real-part vector coordinate.** Proved result. A coordinate of the real-part vector is the real part of the corresponding complex coordinate. (`realPartVec_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldDiv.lean#L13)).

**Harmonic-key field is differentiable.** Proved result. For admissible harmonic field data, the vector field of one harmonic key is differentiable. (`keyVector_differentiable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldDiv.lean#L15)).

### Breakdown.CertCell.ShapeFieldExpandGrad

Recover the field and its gradient from the finite harmonic support. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Axial rotation as a linear map.** Definition. Package axial rotation as a continuous real linear map. (`spaceRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L18)).

**linear rotation map is axial rotation.** Proved result. Applying the packaged continuous linear map gives the ordinary axial rotation. (`spaceRot_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L21)).

**Rotate and multiply by a phase.** Definition. Multiply an axially rotated complex vector by the complex phase. (`twistVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L23)).

**The continuous phase-rotation map.** Definition. Package phase multiplication followed by axial rotation as a continuous real linear map. (`twistMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L26)).

**The twist map is phase times rotation.** Proved result. Applying the packaged twist map gives phase multiplication of the rotated vector. (`twistMap_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L36)).

**A key's time-angle phase.** Definition. Form the temporal and angular phase from the key's physical harmonic label. (`harmonicAngle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L38)).

**The time-angle phase of a harmonic key.** Proved result. Under the declaration's hypotheses, a time shift and axial rotation of a harmonic key field rotate its vector value and multiply it by the corresponding temporal-angular phase. (`key_shift_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L41)).

**The harmonic phase of key derivatives.** Proved result. Under the declaration's hypotheses, shifting time and rotating both the evaluation point and input vector rotates the key-field derivative and multiplies it by the key's time-angle phase. (`key_fderiv_shift_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L58)).

**Read the coordinatewise real part.** Proved result. The real-part map returns the real part of each complex coordinate. (`realPartVec_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L80)).

**Undo rotation while retaining the phase.** Proved result. Inverse axial rotation of the real part of a twisted vector leaves the real part of the phase-multiplied original vector. (`unrot_realPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L83)).

**Remove rotation from a phased real sum.** Proved result. Undoing the common axial rotation of a sum of twisted complex vectors leaves the sum of the real parts of their phase-weighted coordinates. (`unrot_realPart_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L99)).

**Differentiate a finite harmonic field.** Proved result. Under the declaration's hypotheses, the spatial derivative of the shaped real field is the real part of the sum of the derivatives of its harmonic key fields. (`fderiv_shapeField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L108)).

**Recover real parts from opposite modes.** Proved result. Under the declaration's hypotheses, summing the real parts of the half-weighted positive-frequency coefficients and their conjugate negative-frequency partners recovers the sum of the original real parts. (`span_of_waves`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L119)).

**Harmonic keys span the shaped field.** Proved result. Under the declaration's hypotheses, each coordinate of the shaped real field equals the finite sum of the real parts of its velocity modes on the chosen frequency set. (`fieldSpan_of_keys`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L134)).

**Differentiable keys span the gradient.** Proved result. When the harmonic key fields are differentiable, each gradient entry is the finite sum of the real parts of its gradient modes on the chosen frequency set. (`gradientSpan_of_keyDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L159)).

**Smooth keys span the gradient.** Proved result. Under the declaration's hypotheses, smoothness of the harmonic key fields gives a finite expansion of each gradient entry in the real parts of its gradient modes. (`gradientSpan_of_keySmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpandGrad.lean#L190)).

### Breakdown.CertCell.ShapeFieldExpansion

Recover the represented Hessian from its finite harmonic expansion and assemble the expansion interface. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Phase multiplication and rotation.** Definition. Multiply the rotated complex vector by the specified complex phase. (`phaseRotVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L19)).

**Invert phase and rotation together.** Proved result. Applying the opposite phase and opposite axial rotation undoes the original phase-rotation action. (`phaseRotVec_inv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L22)).

**Invertible phase and rotation.** Definition. Package phase multiplication and rotation as a continuous linear equivalence. (`phaseRotEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L32)).

**Read the phase-rotation equivalence.** Proved result. The continuous equivalence acts by the defined phase multiplication and axial rotation. (`phaseRotEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L48)).

**Axial rotation as an equivalence.** Definition. Package axial rotation as a continuous real linear equivalence. (`rotEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L50)).

**The rotation equivalence acts axially.** Proved result. Applying the continuous rotation equivalence gives the ordinary axial rotation. (`rotEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L52)).

**The phase of a harmonic key.** Definition. Form the phase from the key's temporal and angular frequencies. (`keyAngle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L54)).

**Phase and rotation in time-angle motion.** Proved result. Under the declaration's hypotheses, the key field at shifted time and rotated position is the phase-rotation transform of its original vector value. (`keyVector_shift_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L57)).

**The harmonic phase of key Hessians.** Proved result. Under the declaration's hypotheses, shifting time and rotating the point and both Hessian inputs rotates the Hessian output and multiplies it by the key's time-angle phase. (`keySecondDeriv_shift_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L75)).

**The real-part map reads real coordinates.** Proved result. Each coordinate of the real-part vector is the real part of the corresponding complex coordinate. (`realPartVec_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L82)).

**Undo rotation of a phased real part.** Proved result. Undoing the axial rotation of a phase-rotated complex vector leaves each coordinate equal to the real part of its original coordinate multiplied by the complex phase. (`rot_realPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L85)).

**shaped Hessian is a sum of key Hessians.** Proved result. The prescribed shaped Hessian applied to two vectors is the sum of the real parts of the individual key Hessians on those vectors. (`shapeSecondDeriv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L101)).

**Evaluate a vector sum coordinatewise.** Proved result. A coordinate of a finite sum of real vectors is the sum of that coordinate of each vector. (`space_sum_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L105)).

**Axial rotation commutes with finite sums.** Proved result. Axially rotating a finite sum of real vectors gives the sum of their axial rotations. (`axialRot_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L109)).

**The real parts of two conjugate halves.** Proved result. Adding the real parts of half a complex number and half its conjugate gives its real part. (`re_half_add_conj_half`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L113)).

**The moving-frame Hessian integrand.** Proved result. Under the declaration's hypotheses, the orbit Hessian with its inputs and output expressed in the moving frame equals the sum of real key-Hessian entries multiplied by their time-angle harmonic phases before taking real parts. (`secondDeriv_integrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L116)).

**Reconstruct one Hessian entry from modes.** Proved result. Under the declaration's hypotheses, a prescribed Hessian entry equals the finite sum of the real parts of its second-derivative Fourier modes. (`secondDerivSpan`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L128)).

**The shaped field has finite modes.** Proved result. For admissible harmonic field data, the represented field and its derivatives are recovered from the prescribed finite harmonic support. (`fieldHarmonicExpansion_of_spans`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L153)).

**Finite keys span every Hessian entry.** Proved result. Under the declaration's hypotheses, the finite harmonic key construction gives a mode expansion for every prescribed Hessian coordinate at every time and point. (`secondDerivSpan_of_keys`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldExpansion.lean#L164)).

### Breakdown.CertCell.ShapeFieldModes

Compute the Fourier coefficients of a finite shaped field using orthogonality in time and angle. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**A time-angle harmonic wave.** Definition. Use the complex exponential at the selected pair of integer frequencies. (`fieldModesWave`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L17)).

**Separate a harmonic wave into two phases.** Proved result. The time-angle harmonic wave is the product of its temporal and angular exponentials. (`fieldModesWave_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L20)).

**Multiplying waves adds both frequencies.** Proved result. The product of two time-angle harmonic waves has the sum of their temporal and angular frequencies. (`fieldModesWave_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L29)).

**Conjugate waves reverse both frequencies.** Proved result. The complex conjugate of a time-angle harmonic wave is the wave with both frequencies negated. (`fieldModesWave_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L37)).

**Angular harmonics integrate to zero.** Proved result. The integral of an integer angular harmonic over a full circle is two pi at frequency zero and zero at every other integer frequency. (`fieldModes_angle_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L46)).

**Temporal harmonics integrate to zero.** Proved result. The integral of an integer temporal harmonic over one unit period is one at frequency zero and zero at every other integer frequency. (`fieldModes_time_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L69)).

**Harmonic wave is continuous.** Proved result. The complex harmonic wave is continuous. (`fieldModesWave_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L96)).

**Temporal harmonic waves are continuous.** Proved result. The positive integer-frequency temporal exponential is continuous in time. (`fieldModes_time_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L100)).

**Angular waves integrate over a period.** Proved result. A constant multiple of a time-angle harmonic wave is interval integrable in angle from zero to two pi. (`fieldModesWave_intervalIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L104)).

**Temporal waves integrate over one period.** Proved result. A constant multiple of an integer-frequency temporal exponential is interval integrable from time zero to one. (`fieldModes_time_intervalIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L108)).

**Angular averages select zero frequency.** Proved result. Angular integration of a constant times a time-angle harmonic removes every nonzero angular frequency and leaves two pi times its temporal harmonic at angular frequency zero. (`fieldModes_inner_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L113)).

**Both frequency selectors must vanish.** Proved result. The product of temporal and angular zero-frequency selectors is nonzero only when both frequencies are zero. (`fieldModes_delta`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L121)).

**Double averages select zero frequency.** Proved result. The time-angle integral of a finite sum of harmonics is two pi times the sum of coefficients whose temporal and angular frequencies both vanish. (`fieldModes_double_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L125)).

**Read one coordinate of the real part.** Proved result. A coordinate of the represented real-part vector equals the real part of the complex coordinate. (`fieldModes_realPart_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L159)).

**Commute rotations and complex scaling.** Proved result. A common complex scalar can be moved through axial rotation of a complex vector. (`fieldModes_rotate_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L161)).

**Rotation commutes with a coordinate sum.** Proved result. Rotating the vector defined by a finite coordinatewise sum equals the sum of the rotated vectors. (`fieldModes_rotate_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L166)).

**Undo rotation of a real-part vector.** Proved result. Taking real parts of a complex rotation and then applying the inverse real rotation returns the original real coordinate. (`fieldModes_unrotate_re`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L172)).

**A moving-frame field is a harmonic sum.** Proved result. Under the declaration's hypotheses, after undoing the orbit rotation, each coordinate of the shifted shaped field is the real part of the sum of its key-vector coordinates multiplied by their temporal and angular waves. (`fieldModes_pointwise`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L192)).

**Conjugate-key negation is an involution.** Proved result. Negating the harmonic key twice returns the original key. (`fieldModes_negKey_negKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L217)).

**Negate labels before or after decoding.** Proved result. The physical harmonic label decoded from a negated lattice label is the negative of the original physical harmonic label. (`fieldModes_harmonic_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L221)).

**Compute modes of the finite shaped field.** Proved result. Under the hypotheses of this declaration, the Fourier coefficients of the shaped field equal the explicit harmonic-key sum. (`fieldModeFormula_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L231)).

**Compute modes of the finite shaped field.** Proved result. The Fourier coefficients of the shaped field equal the explicit harmonic-key sum. (`fieldModeFormula`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldModes.lean#L319)).

### Breakdown.CertCell.ShapeFieldSecondDerivFlip

Transport reflection through the prescribed second derivatives and close the field Hessian reflection interface. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Spatial reflection as an equivalence.** Definition. Package the involutive spatial reflection as a continuous real linear equivalence. (`flipPointEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L15)).

**spatial reflection map acts as expected.** Proved result. The continuous linear reflection equivalence sends a point to its coordinate reflection. (`flipPointEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L32)).

**Complex reflection as an equivalence.** Definition. Package reflection of a complex spatial vector as a continuous real linear equivalence. (`flipVecEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L34)).

**complex reflection map acts as expected.** Proved result. The continuous linear complex reflection equivalence sends a vector to its coordinate reflection. (`flipVecEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L51)).

**Real parts respect complex reflection.** Proved result. Taking real parts after complex reflection equals spatially reflecting the real-part vector. (`realPartVec_flipVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L53)).

**Linear transport of totalized Hessians.** Proved result. Under the declaration's hypotheses, an identity transported by continuous linear equivalences transports the totalized second Fréchet derivative in both transformed input directions. (`secondDeriv_of_equiv_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L58)).

**Reflection transfers key Hessians.** Proved result. Under the declaration's hypotheses, reflecting the point and both input vectors in a key Hessian gives the reflected output of the reflected-key Hessian at the original point and inputs. (`keySecondDeriv_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L73)).

**The shaped Hessian obeys reflection.** Proved result. Under the hypotheses of this declaration, the prescribed field Hessian transforms by reflection of the point, output and both input directions. (`fieldSecondDerivFlip_of_keyFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L94)).

**The shaped Hessian obeys reflection.** Proved result. The prescribed field Hessian transforms by reflection of the point, output and both input directions. (`fieldSecondDerivFlip_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSecondDerivFlip.lean#L108)).

### Breakdown.CertCell.ShapeFieldSmooth

Separate the smooth periodic time phase, prove joint continuous differentiability of the shaped field and establish measurability and periodicity of its prescribed Hessian. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The periodic temporal key factor.** Definition. Use the positive temporal Fourier exponential determined by the key label. (`keyTimeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L16)).

**The temporal key factor never vanishes.** Proved result. The complex temporal exponential of a harmonic key is nonzero. (`keyTimeFactor_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L19)).

**Key time factors have unit period.** Proved result. Adding one to time leaves every key's temporal harmonic factor unchanged. (`keyTimeFactor_add_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L22)).

**Every regularity order for time factors.** Proved result. Each temporal harmonic key factor has every specified finite or infinite differentiability order. (`contDiff_keyTimeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L31)).

**Separate a key field's temporal phase.** Proved result. The key field at time σ is its time-zero field multiplied by the temporal key factor. (`keyVector_eq_timeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L37)).

**Separate a key Hessian's temporal phase.** Proved result. The key Hessian at time σ is its time-zero Hessian multiplied by the same temporal key factor. (`keySecondDeriv_eq_timeFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L45)).

**Key fields have unit time period.** Proved result. Each harmonic key field repeats after one unit of time. (`keyVector_add_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L55)).

**Joint C¹ and measurable Hessian.** Proved result. Under the declaration's hypotheses, valid shape data give a jointly continuously differentiable periodic field and an almost everywhere strongly measurable periodic prescribed Hessian. (`fieldJointSmooth_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldSmooth.lean#L62)).

### Breakdown.CertCell.ShapeFieldWeak

Use local Lipschitz bounds to identify the real sum of totalized key Hessians with the weak second derivative of the finite harmonic field. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Local bounds give local integrability.** Proved result. Under the declaration's hypotheses, a measurable field that is bounded on every closed spatial ball is locally integrable. (`locallyIntegrable_of_ball_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldWeak.lean#L17)).

**Finite sums preserve bounds on balls.** Proved result. Under the declaration's hypotheses, a finite sum of fields that are bounded on each closed ball is itself bounded on each closed ball. (`ball_bound_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldWeak.lean#L29)).

**Local slope bounds give a.e. derivatives.** Proved result. Under the declaration's hypotheses, the stated local Lipschitz bounds imply differentiability almost everywhere in space. (`ae_differentiableAt_of_ball_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldWeak.lean#L43)).

**Bounds for the totalized derivative.** Proved result. Under the declaration's hypotheses, a function Lipschitz on every closed spatial ball has a uniformly bounded totalized Fréchet derivative on every such ball. (`fderiv_norm_bound_of_ball_slopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldWeak.lean#L57)).

**Sum key derivatives into a weak Hessian.** Proved result. For continuously differentiable keys with locally Lipschitz gradients, each gradient column of the summed real field has the corresponding sum of totalized key Hessians as its weak derivative. (`weakSecondDeriv_of_keys`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeFieldWeak.lean#L66)).

### Breakdown.CertCell.ShapeJetConjReflect

Transfer conjugation and reflection from real Hermite basis polynomials to the jet spline coefficients. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Real coefficients of jet polynomials.** Proved result. Conjugating the coefficients of a jet unit polynomial leaves the polynomial unchanged. (`jetUnit_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L15)).

**Real coefficients of left nodal bases.** Proved result. Coefficientwise complex conjugation fixes each left-end Hermite nodal polynomial. (`nodalLeft_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L18)).

**Real coefficients of right nodal bases.** Proved result. Coefficientwise complex conjugation fixes each right-end Hermite nodal polynomial. (`nodalRight_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L22)).

**Real coefficients in bubble polynomials.** Proved result. Coefficientwise complex conjugation fixes each endpoint-vanishing bubble polynomial. (`bubblePoly_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L27)).

**Real coefficients of axis polynomials.** Proved result. Conjugating coefficients fixes every axis basis polynomial on every cell. (`dofPoly_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L32)).

**Real coefficients in first embeddings.** Proved result. Under the declaration's hypotheses, embedding a real-coefficient polynomial in the first bivariate coordinate gives a polynomial fixed by coefficientwise complex conjugation. (`embedFirst_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L42)).

**Real coefficients in second embeddings.** Proved result. Under the declaration's hypotheses, embedding a real-coefficient polynomial in the second bivariate coordinate gives a polynomial fixed by coefficientwise complex conjugation. (`embedSecond_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L52)).

**Replace a jet spline's coefficients.** Definition. Keep the two jet axes and replace the coefficient table. (`withCoef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L62)).

**Conjugate splines through coefficients.** Proved result. Conjugating a tensor spline piece is equivalent to rebuilding it with all Hermite coefficients conjugated. (`toSpline_conj_piece`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L64)).

**Adding coefficients adds spline pieces.** Proved result. The spline piece formed from the sum of two coefficient arrays is the sum of their spline pieces. (`withCoef_add_piece`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L69)).

**Subtract coefficients and spline pieces.** Proved result. The spline piece formed from the difference of two coefficient arrays is the difference of their spline pieces. (`withCoef_sub_piece`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L74)).

**Restore the original spline coefficients.** Proved result. Replacing a jet spline's coefficients by its own coefficients returns the original spline. (`withCoef_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L79)).

**Polynomial reflection preserves addition.** Proved result. Reflecting a sum of bivariate polynomials gives the sum of their reflections. (`reflectPoly_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L81)).

**Reflection of polynomial differences.** Proved result. Reflecting a difference of bivariate polynomials gives the difference of their reflections. (`reflectPoly_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L84)).

**Real reflection signs of jet coordinates.** Proved result. Complex conjugation leaves the reflection sign of each axis degree of freedom unchanged. (`dofSign_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L87)).

**Parity signs are fixed by conjugation.** Proved result. The complex sign selected as minus one for odd parity and plus one otherwise is fixed by conjugation. (`sign_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L90)).

**Parity changes reverse reflection signs.** Proved result. Negating the Boolean parity flag changes the reflection sign to its negative. (`sign_not`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L93)).

**Jet conjugation and reflection agree.** Proved result. Under the hypotheses of this declaration, jet coefficient conjugation and reflection produce the stated conjugate-reflected spline. (`jetConjReflection_of_jetReflection`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetConjReflect.lean#L99)).

### Breakdown.CertCell.ShapeJetEntry

Connect valid representative jet data to the shape-entry conditions used by the cell layer. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Jets decode to valid amplitudes.** Proposition definition. Require every valid representative jet record to decode to valid representative harmonic amplitudes. (`GivenJetDataValid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetEntry.lean#L14)).

**The jet-to-shape proof interfaces.** Proposition structure. Bundle the shape proof interfaces with validity of decoded jet data. (`JetParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetEntry.lean#L17)).

**Connect jets to the cell-layer data.** Proposition structure. Require the jet model, shape parameters, forcing fields and remaining entry data to match the cell-layer instance. (`IsGivenJetEntry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetEntry.lean#L21)).

**Valid jets supply a shape entry.** Proved result. Under the declaration's hypotheses, the jet interfaces and jet-entry hypotheses produce a valid given shape entry. (`givenShapeEntry_of_jets`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetEntry.lean#L37)).

**Cell-layer shape facts from jet data.** Proved result. Under the declaration's hypotheses, the valid jet entry and jet proof interfaces imply the shape facts required by the cell layer. (`layerShapeFacts_of_jets`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetEntry.lean#L53)).

### Breakdown.CertCell.ShapeJetJoin

Show that the tensor-product jet spline joins with the derivative orders prescribed by its two axes. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Differentiate the radial embedding.** Proved result. The first-variable derivative of a radially embedded polynomial is the embedding of its ordinary derivative. (`pderiv_zero_embedFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L17)).

**No radial derivative of polar embeddings.** Proved result. The partial derivative in the first variable of a polynomial embedded only in the second variable is zero. (`pderiv_zero_embedSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L22)).

**Differentiate the polar embedding.** Proved result. The second-variable derivative of a polar embedded polynomial is the embedding of its ordinary derivative. (`pderiv_one_embedSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L26)).

**No polar derivative of radial embeddings.** Proved result. The partial derivative in the second variable of a polynomial embedded only in the first variable is zero. (`pderiv_one_embedFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L31)).

**Repeated partial derivatives of sums.** Proved result. Any fixed number of polynomial partial derivatives distributes over a finite sum. (`iterate_pderiv_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L35)).

**Radial derivatives of polynomial sums.** Proved result. Any fixed number of derivatives in the first polynomial variable distributes over a finite sum. (`tDeriv_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L44)).

**Polar derivatives of polynomial sums.** Proved result. Any fixed number of derivatives in the second polynomial variable distributes over a finite sum. (`xDeriv_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L48)).

**Differentiate the radial tensor factor.** Proved result. An iterated first-variable derivative of a tensor-product term differentiates only its radial polynomial factor. (`tDeriv_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L52)).

**Differentiate the polar tensor factor.** Proved result. An iterated second-variable derivative of a tensor-product term differentiates only its polar polynomial factor. (`xDeriv_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L64)).

**Evaluate the radial tensor factor.** Proved result. Evaluating the first coordinate of a tensor-product term replaces its radial polynomial by its value there. (`atFirst_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L75)).

**Evaluate the polar tensor-product factor.** Proved result. Evaluating the second coordinate of a tensor-product term replaces its polar polynomial by its value there. (`atSecond_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L84)).

**Ordered indices give ordered breakpoints.** Proved result. Under the declaration's hypotheses, two valid indices in a strictly increasing breakpoint list have strictly ordered values whenever the first index is smaller. (`getD_lt_getD_of_sorted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L93)).

**Adjacent basis pieces have matching jets.** Proved result. Under the declaration's hypotheses, the allowed derivatives of a jet basis polynomial agree at the shared breakpoint of adjacent cells. (`dofPoly_jets_agree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L98)).

**Substitute into a first-variable sum.** Proved result. Substituting a fixed value for the first polynomial variable commutes with a finite sum. (`atFirst_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L145)).

**Substitute into a second-variable sum.** Proved result. Substituting a fixed value for the second polynomial variable commutes with a finite sum. (`atSecond_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L150)).

**Expand a Hermite tensor spline piece.** Proved result. Each tensor spline piece is the double sum of its Hermite coefficients multiplied by the embedded basis polynomials for its two axes. (`toSpline_piece`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L155)).

**The spline keeps its radial jet breaks.** Proved result. The radial breakpoints of the decoded spline are the breakpoints of its radial jet axis. (`toSpline_tBreaks`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L160)).

**The spline keeps its polar jet breaks.** Proved result. The polar breakpoints of the decoded spline are the breakpoints of its polar jet axis. (`toSpline_xBreaks`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L162)).

**Endpoint jets give joined spline pieces.** Proved result. Under the declaration's hypotheses, the tensor-product spline joins to one less than the depth of each jet axis. (`jetSpline_isJoined_of_endJets`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L164)).

**Jet splines join to the required order.** Proved result. Under the hypotheses of this declaration, the tensor-product jet spline joins to the derivative orders prescribed by its axes. (`jetSplineJoined_of_endJets`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetJoin.lean#L196)).

### Breakdown.CertCell.ShapeJetReflect

Compute the parity signs of reflected Hermite and bubble basis polynomials and the resulting spline reflection. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Height reflection fixes radial factors.** Proved result. Reflecting in the second variable leaves a radially embedded polynomial unchanged. (`reflectPoly_embedFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L15)).

**Reflection negates the polar variable.** Proved result. Reflecting a polar embedded polynomial is equivalent to composing that polynomial with the negative variable. (`reflectPoly_embedSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L20)).

**Reflection fixes constant polynomials.** Proved result. Reflecting a constant polynomial leaves it unchanged. (`reflectPoly_C`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L26)).

**Constants in polar polynomial embeddings.** Proved result. Embedding a constant multiple of a polar polynomial equals that constant times its embedding. (`embedSecond_C_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L30)).

**Reflection swaps left and right nodes.** Proved result. Reflecting the interval and substituting the negative variable turns the left Hermite nodal polynomial into the right nodal polynomial multiplied by minus one to its derivative order. (`nodalLeft_comp_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L35)).

**Reflection swaps right and left nodes.** Proved result. Reflecting the interval and substituting the negative variable turns the right Hermite nodal polynomial into the left nodal polynomial multiplied by minus one to its derivative order. (`nodalRight_comp_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L54)).

**Bubble parity under reflection.** Proved result. Reflecting the interval and negating the variable multiplies a bubble polynomial by minus one to its central monomial degree. (`bubblePoly_comp_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L73)).

**Reflection preserves polynomial products.** Proved result. Reflecting a product of polynomials equals the product of their reflections. (`reflectPoly_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L86)).

**Polynomial reflection preserves sums.** Proved result. Reflecting the second polynomial variable distributes over a finite sum of bivariate polynomials. (`reflectPoly_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L90)).

**Reflect the polar tensor factor.** Proved result. Reflection of a tensor-product term keeps its coefficient and radial factor while negating the polar polynomial's variable. (`reflectPoly_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L95)).

**Symmetric breakpoints are opposite pairs.** Proved result. Under the declaration's hypotheses, reading a breakpoint at the reflected index gives the negative of the original breakpoint. (`getD_of_symmetric`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L100)).

**Node and bubble degrees of freedom.** Proved result. An axis degree of freedom is either a node derivative of order below the depth at a valid node or a bubble index below the bubble count in a valid cell. (`mem_dofs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L110)).

**Reflection preserves jet coordinates.** Proved result. Under the declaration's hypotheses, reflecting an active jet degree of freedom produces another active degree of freedom. (`reflectDof_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L123)).

**Reflecting a jet coordinate twice.** Proved result. Under the declaration's hypotheses, reflecting an active jet coordinate twice returns the original coordinate. (`reflectDof_reflectDof`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L129)).

**Reflect a jet basis with its parity sign.** Proved result. Under the declaration's hypotheses, a jet basis polynomial in the reflected cell equals the basis of the reflected coordinate multiplied by its parity sign. (`dofPoly_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L138)).

**Reflected jets give reflected splines.** Proved result. Reflecting jet coordinates with their parity signs gives the reflected spline. (`jetReflection`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetReflect.lean#L174)).

### Breakdown.CertCell.ShapeJetScaled

Define scaled nodal and Jacobi-bubble coordinates and the interfaces connecting them to ordinary jet splines. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**The affine cell coordinate.** Definition. Map a cell interval to the reference coordinate using its midpoint and width. (`cellVariable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L16)).

**A scaled Jacobi bubble polynomial.** Definition. Multiply a symmetric Jacobi polynomial by the endpoint-vanishing factor in the affine cell coordinate. (`jacobiBubble`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L19)).

**The scaled jet basis polynomial.** Definition. Use inverse nodal scales for endpoint jets and scaled Jacobi bubbles for interior coordinates. (`dofPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L25)).

**The directly evaluated scaled spline.** Definition. Sum the tensor products of the scaled radial and polar basis polynomials with the stored coefficients. (`toSpline`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L36)).

**Scaled and converted splines agree.** Interface. Require direct scaled evaluation and evaluation after conversion to ordinary jets to agree on valid axes. (`ScaledSplineAgreementHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L50)). Proof route: `Breakdown.CertCell.GivenShape.scaledSplineAgreementHolds`.

**Scaled jets convert to valid jets.** Interface. Require valid scaled representative data to convert into valid ordinary representative jets. (`ScaledJetDataHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L54)). Proof route: `Breakdown.CertCell.GivenShape.scaledJetDataHolds`.

**The scaled-jet proof interfaces.** Proposition structure. Bundle the ordinary jet interfaces, scaled-spline agreement and validity after conversion. (`ScaledJetParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L57)).

**Ordinary jet entries from scaled data.** Proved result. Under the declaration's hypotheses, converting the scaled data yields a valid ordinary jet entry with the represented Hessian supplied to the cell-layer data. (`givenJetEntry_of_scaled`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L62)).

**Cell-layer shape facts from scaled jets.** Proved result. Under the declaration's hypotheses, the scaled-jet interfaces and entry hypotheses imply the shape facts required by the cell layer. (`layerShapeFacts_of_scaled`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaled.lean#L81)).

### Breakdown.CertCell.ShapeJetScaledAgree

Expand Jacobi bubbles in the ordinary bubble basis and prove that both scaled-spline constructions agree. Appendix B: the cell-calculus, harmonic decomposition, row representation and finite reference-field construction used by the cell-system route.

**Strict ordering of breakpoint values.** Proved result. For valid increasing indices in a strictly increasing list, the earlier breakpoint value is strictly smaller. (`sortedGetD_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L16)).

**The degree bound for Jacobi polynomials.** Proved result. The symmetric Jacobi polynomial of index j has degree at most j. (`symmetricJacobi_natDegree_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L21)).

**Expand a rescaled real Jacobi bubble.** Proved result. For distinct interval endpoints and a truncation count larger than the polynomial index, the scaled monomial-bubble sum equals the Jacobi bubble in the affine cell coordinate. (`jacobiBubble_real_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L38)).

**complex bubble is a cast real polynomial.** Proved result. The complex bubble polynomial is obtained by casting the real endpoint-vanishing polynomial with its centered power factor. (`bubblePoly_eq_map`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L59)).

**Expand a complex Jacobi bubble.** Proved result. Under the declaration's hypotheses, the scaled coefficients of a real Jacobi polynomial, embedded into the complex numbers, express its cell bubble in the monomial bubble basis. (`jacobiBubble_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L63)).

**Convert scaled axis basis polynomials.** Proved result. Under the declaration's hypotheses, each scaled axis basis polynomial equals the linear combination of base basis polynomials given by its conversion column. (`scaledAxis_dofPoly_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L72)).

**Embed a weighted first-variable sum.** Proved result. Embedding a weighted polynomial sum in the first bivariate coordinate gives the sum of the embedded polynomials with the same constant coefficients. (`embedFirst_sum_C_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L128)).

**Embed a weighted second-variable sum.** Proved result. Embedding a weighted polynomial sum in the second bivariate coordinate gives the sum of the embedded polynomials with the same constant coefficients. (`embedSecond_sum_C_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L133)).

**Exchange the two pairs of finite sums.** Proved result. The four finite sums can be reordered by interchanging the first pair of indices with the second pair. (`sum_four_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L138)).

**Scaled and ordinary splines agree.** Proved result. Direct scaled-spline evaluation agrees with evaluation after conversion to ordinary jets. (`scaledSplineAgreementHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledAgree.lean#L151)).

### Breakdown.CertCell.ShapeJetScaledValid

This file transfers regularity, vanishing, real coefficients and reflection parity from scaled Hermite data to ordinary jet data, using the parity of symmetric Jacobi polynomials. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Negating X changes coefficient parity.** Proved result. For a real polynomial p, the coefficient of Xˢ in p(−X) is (−1)ˢ times the coefficient of Xˢ in p(X). (`coeff_comp_neg_X_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L16)).

**Jacobi parity follows its degree.** Proved result. Negating the variable multiplies the degree-j symmetric Jacobi polynomial by (−1) to power j. (`symmetricJacobi_comp_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L30)).

**Jacobi coefficients have fixed parity.** Proved result. For a symmetric Jacobi polynomial of degree j, its coefficient aₛ satisfies (−1)ʲaₛ = (−1)ˢaₛ, so coefficients of the opposite parity vanish. (`symmetricJacobi_coeff_parity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L52)).

**Jet conversion commutes with conjugation.** Proved result. Every entry of the scaled-to-unscaled jet conversion matrix is real, and hence is unchanged by complex conjugation. (`scaled_convert_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L58)).

**Reflected node scales agree.** Proved result. If the nodal scales are symmetric, the scale at node k equals the scale at the reflected node N−k for every 0 ≤ k ≤ N. (`scale_getD_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L63)).

**Reflection respects jet conversion.** Proved result. On a symmetric jet axis with symmetric scales, reflecting both indices of the conversion matrix gives the original entry multiplied by the quotient of the two jet parity signs. (`scaled_convert_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L76)).

**Reflected coefficient sums agree.** Proved result. On a symmetric axis with symmetric scales, a coefficient relation c(reflect e) = τ εₑ g(e) is preserved by jet conversion, with the same factor τ and parity sign εₑ. (`sum_scaled_convert_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L126)).

**Converted coefficients are double sums.** Proved result. Each converted two-variable jet coefficient is the double sum of the original coefficients against the conversion matrices in the first and second coordinates. (`scaled_toJet_coef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L140)).

**Conversion preserves jet regularity.** Proved result. Scaled-to-ordinary jet conversion preserves the two specified derivative joining orders. (`scaled_jetClass`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L145)).

**Conversion preserves initial vanishing.** Proved result. If the scaled jet coefficients vanish at the initial endpoint, the coefficients after conversion to the ordinary jet basis also vanish there. (`scaled_vanishesAtStart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L149)).

**Conversion preserves real coefficients.** Proved result. If all scaled spline coefficients are real, their coefficients in the ordinary jet basis remain real after conversion. (`scaled_realCoef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L168)).

**Conversion preserves reflection parity.** Proved result. On a symmetric second-coordinate axis with symmetric scales, conversion from scaled to ordinary jets preserves either the even or the odd reflection law of the coefficients. (`scaled_reflectFixed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L174)).

**Conversion preserves conjugate parity.** Proved result. On a symmetric second-coordinate axis with symmetric scales, jet conversion preserves a reflection law combined with complex conjugation, with the same even or odd sign. (`scaled_conjReflectFixed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L184)).

**Validity of converted scaled jet data.** Proved result. The scaled jet conversion preserves regularity, initial vanishing, real coefficients, and both reflection conditions. (`scaledJetDataHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetScaledValid.lean#L200)).

### Breakdown.CertCell.ShapeJetStart

This file checks the left-endpoint values of the Hermite basis and uses them to prove that zero initial jet coefficients make the first spline row vanish. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Higher jet values vanish at zero.** Proved result. The unit jet polynomial corresponding to derivative order p > 0 has value zero at the left endpoint 0. (`jetUnit_eval_zero_of_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L15)).

**Unit jets vanish at one.** Proved result. For positive matching order n, every unit jet polynomial has value zero at the right endpoint 1. (`jetUnit_eval_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L18)).

**Left jets vanish for positive order.** Proved result. The left-endpoint basis polynomial for derivative order p > 0 has value zero at its own endpoint a. (`nodalLeft_eval_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L21)).

**Right jets vanish at the left endpoint.** Proved result. If the endpoints a and b are distinct and the matching order is positive, every right-endpoint basis polynomial vanishes at a. (`nodalRight_eval_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L26)).

**Bubble values vanish at the left end.** Proved result. For positive matching order n, every bubble polynomial on [a,b] has value zero at a. (`bubblePoly_eval_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L35)).

**The first jet interval starts at zero.** Proved result. A valid jet axis on [0,1] has first breakpoint 0 and a strictly positive second breakpoint. (`breaks_start`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L39)).

**Noninitial degrees vanish at the start.** Proved result. On a valid jet axis over [0,1], every basis polynomial on the first cell vanishes at 0 except possibly the basis polynomial for the value at the initial node. (`dofPoly_start_eval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L58)).

**Embedding evaluates to a constant.** Proved result. Fixing the first variable of an embedded one-variable polynomial gives the constant polynomial equal to its value at that input. (`atFirst_embedFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L85)).

**Initial jet vanishing reaches splines.** Proved result. For valid jet axes on [0,1] and [−1,1], vanishing of the initial nodal coefficients makes the polynomial on every first-coordinate initial cell vanish identically at first coordinate 0. (`jetStartVanish`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetStart.lean#L92)).

### Breakdown.CertCell.ShapeJetUnit

This file proves the endpoint derivative identities for the Hermite nodal basis and interior bubble basis on an interval. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Root multiplicity kills derivatives.** Proved result. If a complex polynomial has a root r of multiplicity at least n, then every derivative of order o < n vanishes at r. (`eval_iterate_derivative_eq_zero_of_dvd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L13)).

**Affine composition scales derivatives.** Proved result. If q is an affine complex polynomial with derivative c, then the o-th derivative of P(q(X)) is cᵒP⁽ᵒ⁾(q(X)) for every o ≥ 0. (`iterate_derivative_comp_linear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L18)).

**Monomial jets vanish except at degree.** Proved result. For cXᵖ, the derivative of order o evaluated at 0 equals cp! when o = p and equals zero otherwise. (`eval_iterate_derivative_C_mul_X_pow_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L27)).

**A binomial sum inverts modulo a power.** Proved result. For nonnegative integers d and m, (1−X)ᵈ⁺¹∑ₛ₌₀ᵐ⁻¹ binom(d+s,s)Xˢ agrees with 1 modulo Xᵐ. (`one_sub_pow_mul_choose_sum_sub_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L39)).

**Unit jets select one derivative.** Proved result. At zero, every derivative below the joining order of a unit jet is one when its order equals the selected jet index and zero otherwise. (`iterate_derivative_jetUnit_eval_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L66)).

**Unit jets vanish at the right endpoint.** Proved result. Every derivative of a unit jet polynomial of order o < n vanishes at the right endpoint 1. (`iterate_derivative_jetUnit_eval_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L95)).

**Left basis selects one derivative.** Proved result. For distinct interval endpoints, each derivative below the joining order of the left nodal basis at the left endpoint is one at its selected index and zero otherwise. (`iterate_derivative_nodalLeft_eval_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L102)).

**Left basis vanishes at the right end.** Proved result. If a ≠ b, every derivative of order o < n of a left-endpoint jet basis polynomial vanishes at b. (`iterate_derivative_nodalLeft_eval_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L116)).

**Right basis selects one derivative.** Proved result. For distinct interval endpoints, each derivative below the joining order of the right nodal basis at the right endpoint is one at its selected index and zero otherwise. (`iterate_derivative_nodalRight_eval_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L127)).

**Right basis vanishes at the left end.** Proved result. If a ≠ b, every derivative of order o < n of a right-endpoint jet basis polynomial vanishes at a. (`iterate_derivative_nodalRight_eval_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L141)).

**Bubble jets vanish at the left endpoint.** Proved result. Every derivative of order o < n of a bubble polynomial on [a,b] vanishes at a. (`iterate_derivative_bubblePoly_eval_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L152)).

**Bubble jets vanish at the right endpoint.** Proved result. Every derivative of order o < n of a bubble polynomial on [a,b] vanishes at b. (`iterate_derivative_bubblePoly_eval_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetUnit.lean#L159)).

### Breakdown.CertCell.ShapeJetValid

This file assembles the jet joining, reflection, conjugation and initial-vanishing facts into validity of the supplied shape data. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Spline join orders can be lowered.** Proved result. If adjacent spline pieces agree through orders a and b in their two coordinates, they also agree through any smaller orders a′ ≤ a and b′ ≤ b. (`joinedSpline_mono_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L20)).

**Jet regularity gives joined splines.** Proved result. Under the jet-joining rule, jet data of radial and height orders a and b give a spline joined to those same orders. (`joinedSpline_of_jetClass`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L25)).

**Real coefficients respect conjugation.** Proved result. For real jet coefficients, an even or odd reflection law also gives the corresponding reflection law combined with complex conjugation. (`conjReflectFixed_of_realCoef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L29)).

**Zero first label for self-conjugate keys.** Proved result. Self-conjugate keys have zero first label. (`label_fst_eq_zero_of_negKey_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L33)).

**Two reflection laws give conjugacy.** Proved result. Assuming the spline agreement rules, a spline that agrees both with its signed reflection and with the signed reflection of its conjugate agrees with its conjugate. (`splineAgrees_conj_of_reflect_fixed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L38)).

**Jet rules imply valid given data.** Proved result. The jet joining, reflection, conjugate reflection, initial vanishing, and agreement assumptions imply validity of given jet data. (`givenJetDataValid_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L51)).

**Valid jet data from shape assumptions.** Proved result. The shape-analysis assumptions turn valid jet axes and key symmetries into valid given jet data. (`givenJetDataValid_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L89)).

**Validity of given jet data.** Proved result. Valid jet axes with the required coefficient symmetries produce valid given jet data. (`givenJetDataValid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetValid.lean#L92)).

### Breakdown.CertCell.ShapeJetVanish

This file turns vanishing nodal and bubble coefficients beyond a radial breakpoint into vanishing of the represented spline there. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Defaulted breakpoints remain ordered.** Proved result. A strictly increasing breakpoint list ending at 1 remains nondecreasing when all entries beyond its end are defined to be 1. (`getD_succ_ge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetVanish.lean#L15)).

**Zero tail coefficients kill each term.** Proved result. If every nodal and bubble coefficient whose first-coordinate support begins at or beyond tᵦ is zero, then each coefficient-weighted basis polynomial vanishes on every cell starting at or beyond tᵦ. (`dof_term_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetVanish.lean#L30)).

**Zero jet tails give zero spline tails.** Proved result. Vanishing jet tails give vanishing splines. (`jetSplineVanishesFrom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJetVanish.lean#L56)).
<!-- /passage:front -->

