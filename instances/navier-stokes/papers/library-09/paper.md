
<!-- passage:front -->
# Library guide 9: Breakdown/CertCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) **9** [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.CertCell.AssemblyRowExpansionAllowance` to `Breakdown.CertCell.HarmonicPressureFlip` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.CertCell.AssemblyRowExpansionAllowance

This file proves that the separate row-error allowances fit inside the total curl and velocity allowance. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Linearity of weighted cell integrals** · theorem. `allowWeighted_lin`: The radial-weighted integral of a two-term scalar combination equals the same combination of the two integrals under the integrability hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionAllowance.lean#L16).

**Increase three allowance coefficients** · theorem. `allowWeighted_three_le`: Increasing the coefficients of three nonnegative integrable energy profiles bounds their weighted integral combination by the integral with the larger coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionAllowance.lean#L22).

**Fit the row allowances into budgets** · theorem. `allowanceSplit_holds`: Under the stated hypotheses, resolved, band and deactivated allowances fit respectively into the box, band and leakage budgets, retaining the pairing slack. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionAllowance.lean#L43).

### Breakdown.CertCell.AssemblyRowExpansionCombineAlgebra

This file provides the finite matrix algebra that combines differently scaled row vectors against inverse Gram matrices. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Scale row coordinates by label** · definition. `scaleVec`: This map multiplies each row coordinate by its label-dependent scaling factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L16).

**Matrix split into label blocks** · proposition definition. `IsLabelBlock`: This predicate requires matrix entries between different row labels to vanish. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L20).

**Scaling constant within each label** · proposition definition. `IsLabelConst`: This predicate requires equal scaling factors on rows carrying the same harmonic label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L22).

**Nonnegativity of semidefinite forms** · theorem. `Breakdown.CertCell.AssemblyRowExpansionCombineAlgebra.quad_nonneg`: A positive semidefinite complex matrix has nonnegative real quadratic value at every complex vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L24).

**A positive definite form detects zero** · theorem. `eq_zero_of_quad_nonpos`: A vector whose positive definite quadratic form is nonpositive must be zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L27).

**Symmetry of the real cross form** · theorem. `cross_swap`: The real cross form of the specified self-adjoint matrix is unchanged when its two vectors are exchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L35).

**Quadratic form from the cross form** · theorem. `quad_eq_cross`: The matrix quadratic form is the corresponding cross form evaluated on the same vector twice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L41).

**Quadratic form of a difference** · theorem. `quad_sub`: For the specified Hermitian matrix, the form of x minus y is the sum of their forms minus twice their cross form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L43).

**Scale a vector in a quadratic** · theorem. `quad_smul`: Scaling the input vector by a real t multiplies its quadratic value by t squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L53).

**Add in the first real cross-form slot** · theorem. `crossForm_add_left`: The real cross form of a matrix is additive in its first vector argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L61).

**The cross form vanishes on a zero input** · theorem. `crossForm_zero_left`: The real cross form is zero when its first vector is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L66).

**Finite sums in the first cross-form slot** · theorem. `crossForm_sum_left`: The real cross form of a finite vector sum equals the sum of the corresponding cross forms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L70).

**Label-constant scalars commute** · theorem. `block_mul_comm`: A scalar function constant on labels can be moved from the column index to the row index of a label-block matrix entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L77).

**Move a label-constant scale** · theorem. `crossForm_scale`: For a label-block matrix, a scale constant on labels can be transferred between the two arguments of the real cross form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L84).

**Compose coordinate scalings** · theorem. `scaleVec_scaleVec`: Successive coordinate scalings multiply their scale factors pointwise. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L94).

**Coordinate scaling preserves addition** · theorem. `scaleVec_add`: Applying a fixed real coordinate scale to a vector sum gives the sum of the scaled vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L100).

**Coordinate scaling preserves finite sums** · theorem. `scaleVec_sum`: Applying a fixed real coordinate scale to a finite vector sum gives the finite sum of the scaled vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L105).

**A constant coordinate scale** · theorem. `scaleVec_const`: Scaling all coordinates by the same real number is complex scalar multiplication by its coercion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L110).

**Square-root scaling of a quadratic** · theorem. `quad_scale_const`: Scaling a vector by the square root of a nonnegative real t multiplies its quadratic form by t. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L114).

**Combine labelwise weighted vectors** · theorem. `weighted_combine`: For a positive semidefinite label-block matrix, label-constant scales with coordinatewise square sum at most one bound the form of the weighted vector sum by the sum of the separate forms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L118).

**Combine the four row error families** · theorem. `combine_four`: For a positive semidefinite label-block matrix, the three displayed vectors and the indexed fourth family obey the summed quadratic bound when the labelwise scale squares total at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L159).

**Block matrices commute with label scales** · theorem. `comm_of_block`: A label-block matrix commutes with a diagonal matrix whose entries are constant on labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L185).

**The inverse preserves label blocks** · theorem. `inv_block`: The inverse of the stated label-block matrix also has zero entries between distinct labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L191).

**Scaling as a diagonal matrix** · theorem. `scaleVec_eq_mulVec`: Coordinate scaling by a real function equals multiplication by the diagonal matrix of its complex coercions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L210).

**Move weights into the input vector** · theorem. `inverseWeightedSq_scaled`: The inverse weighted square of the row-scaled matrix equals the inverse original-matrix quadratic on the input scaled by the square roots of the positive weights. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L216).

**Count equal square-root contributions** · theorem. `sum_sq_ite_mem`: For nonnegative x, summing the squares of sqrt(x) on a finite set and zero elsewhere gives the set's cardinality times x. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L240).

**Cancel a positive square-root weight** · theorem. `sqrt_div_mul_sqrt`: For the stated nonnegative numerator and positive denominator, sqrt(w/c) times sqrt(c) equals sqrt(w). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionCombineAlgebra.lean#L250).

### Breakdown.CertCell.AssemblyRowExpansionDeactSplit

This file reindexes deactivated-mode interactions by their source groups so the leakage estimates can be applied with the correct partner sets. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.RowStageDeact.Internal`.**

**Opposite labels give opposite harmonics** · theorem. `Breakdown.CertCell.AssemblyRowExpansionDeactSplit.labelHarmonic_neg`: The harmonic assigned to the negative label is the negative of its original harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionDeactSplit.lean#L14).

**Reindex a restricted shifted sum** · theorem. `sum_shift_filter`: The supplied support conditions let a finite sum indexed by partner labels be reindexed by shifts while preserving both membership restrictions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionDeactSplit.lean#L18).

**Regroup shifts by partner classes** · theorem. `sum_regroup_partners`: The shift sum selected by the keep predicate equals the sum over the specified disjoint partner classes and their permitted shifts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionDeactSplit.lean#L35).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Regroup the deactivated row term** · theorem. `deactSplit_holds`: Under the stated hypotheses, the deactivated row contribution is the sum of its designated group contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionDeactSplit.lean#L61).

### Breakdown.CertCell.AssemblyRowExpansionLink

This file supplies the row-moment expansion interface from the separately proved row identity and five component bounds. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Bound the row-moment remainder** · theorem. `rowMomentExpansion_of_parts`: Under the stated hypotheses, the inverse leakage-Gram norm of the row remainder and resolved slack are bounded by the allocated box, tail, leakage, band and actuator budgets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLink.lean#L11).

### Breakdown.CertCell.AssemblyRowExpansionLongPiece

This file controls long-mode row terms by Fourier coefficients on time-angle fibres and the low-versus-high class split. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal.LongPart`.**

**Explicit negative exponential phase** · theorem. `conj_phase_eq`: The conjugate label phase is the negative imaginary exponential of its time-angle harmonic argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L23).

**Fibre and label coefficients agree** · theorem. `coef_fiber`: The Fourier coefficient of a rotated real velocity fibre equals the corresponding labelled velocity coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L32).

**The rotating fibre preserves energy** · theorem. `fiber_normSq`: The sum of squared norms of the complex-coerced fibre coordinates equals the squared physical velocity norm along the rotation orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L36).

**Away from the axis and equator** · definition. `offAxisPoints`: This set consists of time-space points with positive cylindrical radius and nonzero height. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L44).

**The off-axis region is open** · theorem. `offAxisPoints_open`: The space-time set whose spatial point lies off the axis is open. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L47).

**Positive-radius orbits avoid the axis** · theorem. `orbit_offAxis`: The time-angle orbit of a plane point with positive radius belongs to the off-axis space-time region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L56).

**Rotating back preserves continuity** · theorem. `rotated_coord_continuous`: A coordinate of a continuous planar vector field rotated back by its angular argument is continuous after complex coercion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L60).

**Continuity of the off-axis fibre** · theorem. `fiber_continuous`: Continuity on the off-axis region makes the rotating velocity fibre continuous above every positive-radius plane point with nonzero height. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L65).

**Realize bounded Fourier data** · theorem. `fiber_coefficients`: The orbit bound yields an integrable torus vector with pointwise squared norm at most the error bound squared and with the required labelled Fourier coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L75).

**Off-axis fields give measurable labels** · theorem. `label_coefficient_measurable`: Continuity on the off-axis region yields almost-everywhere strongly measurable labelled velocity coordinates on every cell of a valid mesh. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L95).

**Zero model fields give zero coupling** · theorem. `crossVec_zero_zero`: The packed-profile coupling vector vanishes when both the model velocity and model vorticity vectors are zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L114).

**Coupling coordinates are measurable** · theorem. `crossVec_aesm`: Almost-everywhere strong measurability of the profile and both model vectors implies the same measurability for every coupling-vector coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L117).

**A dominated vector pairs with a test** · theorem. `weighted_pair_integrable`: A measurable vector whose squared norm is dominated by a radial-integrable bound has integrable radial-weighted pairing with each continuous vector test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L130).

**Source section `Pointwise`.**

**Long-mode coupling row vector** · definition. `longCouplingVec`: This vector pairs the long velocity and vorticity coefficients with the perturbation's curl and velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L173).

**Curl energy of the band encoding** · theorem. `curl_band_eq`: The curl-coordinate energy of the band profile equals the corresponding mode curl energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L177).

**Velocity energy of the band encoding** · theorem. `vel_band_eq`: The velocity-coordinate energy of the band profile equals the corresponding mode velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L185).

**Parseval bound for long coupling** · theorem. `long_parseval`: Almost everywhere in the cell, finite sums of long-coupling coefficient energies are bounded by twice the squared velocity error times curl energy plus twice the squared vorticity error times velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L191).

**Separate low and high long labels** · theorem. `long_class_split`: The low/high weighted long-coupling energy obeys the displayed class-dependent bound in terms of velocity and vorticity model errors and source-mode energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L214).

**Source section `Rows`.**

**Scaled Gram as a diagonal pullback** · theorem. `scaledRowGram_congr`: When the labelwise scale squared times the weight is one, the scaled row Gram matrix equals the original Gram matrix conjugated by that diagonal scale. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L278).

**Bound scaled row moments by energy** · theorem. `scaled_rows_le`: The inverse weighted row-Gram square of the moment vector is bounded by the weighted sum of radial integrals of the source profile energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L293).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Bound the long-mode row term** · theorem. `longPieceBound_holds`: Under the stated hypotheses, the long-scaled inverse-Gram squared term is bounded by the resolved, band and deactivated long-mode allowances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLongPiece.lean#L384).

### Breakdown.CertCell.AssemblyRowExpansionLow

This file proves the row identity by separating the given field into model, error, long-mode, retained and tail contributions. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal.RowIdentity`.**

**Pairing with the given field** · definition. `pairTrue`: This term pairs the true given-field coupling with the perturbation's harmonic profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L33).

**Pairing with the model field** · definition. `pairModel`: This term pairs the polynomial model coupling with the perturbation's harmonic profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L38).

**Pairing with the field error** · definition. `pairError`: This term pairs the difference between the given and model fields with the harmonic profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L44).

**Pairing with the long-mode field** · definition. `pairLong`: This term pairs the long-mode field with the perturbation's harmonic profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L54).

**Pairing at a shifted harmonic** · definition. `pairShift`: This term writes the model interaction at a harmonic shifted by the row's label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L60).

**Row pairing with the projection tail** · definition. `tailTerm`: This term pairs a row test with the difference between the actual coefficient and its polynomial projection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L66).

**Row pairing with the band profile** · definition. `bandTerm`: This term pairs the row model with the band-profile contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L71).

**Row evaluated on retained data** · definition. `lowRow`: This value evaluates the row on the retained polynomial cell data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L75).

**Evaluate the velocity model polynomial** · theorem. `modelVelocity_eq_poly`: On the cell rectangle, each component of the labelled velocity model is the evaluation of its stored cell polynomial. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L82).

**Evaluate the vorticity model polynomial** · theorem. `modelVorticity_eq_poly`: On the cell rectangle, each component of the labelled vorticity model is the evaluation of its stored cell polynomial. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L89).

**A finite-energy profile fits the test** · theorem. `pair_integrableOn`: Coordinatewise finite radial energy and continuous representatives for the model fields make the profile's radial-weighted cross-test pairing integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L96).

**Replace shifts by partner labels** · theorem. `shift_sum`: The support and matching-value hypotheses convert the restricted finite shift sum into the finite sum over partner labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L116).

**Integrate three summands** · theorem. `integral_add_three`: The integral of three integrable summands is the sum of their three integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L135).

**Multiply a square-integrable profile** · theorem. `rectSquare_mul_right`: Multiplying the cell square-integrable profile by the stated bounded measurable factor preserves its weighted square-integrability conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L143).

**A uniform field bound controls a mode** · theorem. `norm_labelVel_le`: The uniform bound on the field along the required orbit bounds each labelled velocity coefficient by the same constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L150).

**Continuous profiles have finite energy** · theorem. `rectSquare_of_continuous`: A continuous scalar function on the compact cell rectangle satisfies the radial-weighted square-integrability predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L159).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Resolve one complete row defect** · theorem. `rowIdentity_entry`: Each row moment minus its resolved-state row and tail row is the sum of its frequency, model-error, long, deactivated and actuator pieces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L168).

**Decompose the row-moment error** · theorem. `rowIdentity_holds`: Under the stated hypotheses, the right-side row moment minus the retained row and tail equals the sum of period, approximation, long, deactivated and actuator contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLow.lean#L589).

### Breakdown.CertCell.AssemblyRowExpansionLowAlgebra

This file supplies the finite sums, weighted integrability and continuity facts used to integrate the low-mode row identity. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Split the packed bilinear pairing** · theorem. `pairVec_sum_mul`: The coordinate product sum of two packed profiles equals the matrix-entry product sum plus the velocity-coordinate product sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L14).

**Conjugation respects profile packing** · theorem. `conj_pairVec`: Conjugating a packed profile coordinate equals packing the entrywise conjugated matrix and velocity vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L22).

**Cross-test pairing in vector form** · theorem. `cross_pairing`: Pairing a packed profile with the conjugate cross test equals the vector pairing of its curl-velocity and vorticity-velocity cross terms with the test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L27).

**Add the model fields in a cross test** · theorem. `crossTest_add`: Adding both model velocity and vorticity fields gives the sum of their cross tests against the same test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L44).

**Zero model fields give a zero cross test** · theorem. `crossTest_zero`: The cross test is the zero vector when its model velocity and vorticity inputs are both zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L52).

**The linear row integrands integrate** · theorem. `rowVolume_integrable`: A valid weak row profile and axis-regular polynomial test make both the interior row integrand and its velocity-test frequency correction integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L58).

**Change the row frequency** · theorem. `rowVolume_freq_shift`: Changing the row frequency adds the complex frequency difference times i times the radial-weighted velocity-test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L122).

**Square integrability on a cell** · proposition definition. `RectSquare`: This predicate records the measurability and square-integrability conditions used for row pairings on a rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L133).

**Add finite-energy profiles** · theorem. `rectSquare_add`: The sum of two profiles satisfying the cell weighted square-integrability predicate satisfies the same predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L136).

**Multiply by a bounded cell factor** · theorem. `rectSquare_mul`: The product of the specified bounded measurable factor and a cell finite-energy profile again satisfies the cell square-integrability predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L150).

**A bounded profile has finite cell energy** · theorem. `rectSquare_bounded`: The stated measurability and uniform bound imply radial-weighted square-integrability on the finite cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L164).

**Scale a finite-energy profile** · theorem. `rectSquare_const_mul`: Multiplying a cell finite-energy profile by a fixed complex scalar preserves its weighted square-integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L178).

**Sum finitely many finite-energy profiles** · theorem. `rectSquare_sum`: A finite sum of cell finite-energy profiles satisfies the same weighted square-integrability predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L182).

**Bounded tests fit finite-energy profiles** · theorem. `rectSquare_pairing`: A radial-square-integrable scalar profile has integrable radial-weighted product with an almost-everywhere measurable bounded test factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L194).

**Rotation is jointly continuous** · theorem. `continuous_axialRot_pair`: Axial rotation depends continuously on both its angle and its vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L199).

**Compose continuous rotation data** · theorem. `continuous_axialRot_of`: A continuously varying angle acting by axial rotation on a continuously varying vector gives a continuous vector field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L203).

**The plane embedding is continuous** · theorem. `Breakdown.CertCell.AssemblyRowExpansionLowAlgebra.continuous_planePoint`: The embedding (r,z) into the vector (r,0,z) is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L208).

**Parameter-dependent torus integrals** · theorem. `continuous_double_integral`: A jointly continuous integrand has a continuous iterated integral over the fixed compact time-angle box as the remaining parameter varies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L216).

**Fourier averages depend continuously** · theorem. `continuous_modeAverage`: A jointly continuous real integrand gives a continuously varying fixed-frequency mode average in the remaining parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L226).

**Continuous fields give continuous labels** · theorem. `continuous_labelVel`: A continuous space-time vector field has continuous labelled velocity coordinates as functions of the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L238).

**Cross tests vary continuously** · theorem. `continuous_crossTest_comp`: Continuous model velocity, vorticity and test coordinates give continuous coordinates of their cross test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L252).

**A continuous representative is bounded** · theorem. `rect_regular_of_eqOn`: A function agreeing on the cell rectangle with a continuous function is almost-everywhere strongly measurable there and uniformly bounded there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowAlgebra.lean#L265).

### Breakdown.CertCell.AssemblyRowExpansionLowCoupling

This file derives the harmonic convolution formula for the row coupling between the given field and a perturbation. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Positive harmonic phase factor** · definition. `phaseFactor`: This factor is the complex exponential with the positive harmonic phase convention. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L25).

**Harmonic coefficient as a box mean** · definition. `modeMean`: This mean integrates against the negative harmonic phase over the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L28).

**A phase factor has norm one** · theorem. `norm_phaseFactor`: Every complex time-angle phase factor has norm one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L31).

**The positive phase is continuous** · theorem. `continuous_phaseFactor`: The positive harmonic exponential is continuous in time and angle at each fixed frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L35).

**Subtract frequencies when phases meet** · theorem. `expFactor_mul_phaseFactor`: Multiplying the negative Fourier phase at xi by the positive phase at beta gives the negative phase at xi minus beta. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L39).

**Conjugate phases add frequencies** · theorem. `expFactor_mul_conj_phaseFactor`: Multiplying a negative Fourier phase by a conjugate positive phase gives the negative phase at the sum of their frequencies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L48).

**A phase preserves torus integrability** · theorem. `integrable_expFactor_mul`: Multiplying the complex coercion of the integrable real torus function by the Fourier phase gives an integrable complex function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L57).

**Fourier mean as a box integral** · theorem. `modeMean_eq_integral`: The mode mean equals the integral of the negative phase times the complex-coerced function over the time-angle box, divided by 2pi. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L65).

**Average finite real sums by frequency** · theorem. `modeMean_sum`: The harmonic mean of a finite sum of integrable real functions equals the sum of their harmonic means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L71).

**Scale a real harmonic mean** · theorem. `modeMean_const_mul`: Multiplying the real input by a real scalar multiplies its complex Fourier mean by that scalar's complex coercion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L82).

**Add real harmonic means** · theorem. `modeMean_add`: The harmonic mean of the sum of two integrable real functions equals the sum of their harmonic means. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L88).

**A real phase product integrates** · theorem. `integrable_mul_re_phase`: Multiplying an integrable real torus function by the real part of a fixed phase-weighted complex coefficient preserves integrability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L98).

**Two frequency shifts from a real mode** · theorem. `modeMean_mul_re_phase`: The mode mean of a real phase component times a real function is half the sum of the negatively and positively shifted mode means with conjugate coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L106).

**Negation permutes a symmetric support** · theorem. `sum_neg_of_symmetric`: On a finite support closed under negation, summing f at negative indices gives the same result as summing f at the original indices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L125).

**A rotated zero vector was zero** · theorem. `rotC_eq_zero`: If the complex-linear coordinate extension of an axial rotation sends a vector to zero, that vector is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L130).

**Rotate a cross product** · theorem. `crossVec_axialRot`: An axially rotated cross product is the alternating-tensor contraction of the rotated vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L146).

**Permutation and tensor signs agree** · theorem. `permSign_eq_alternatingSymbol`: The certificate permutation sign equals the real alternating-tensor entry. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L156).

**Harmonics preserve label differences** · theorem. `Breakdown.CertCell.AssemblyRowExpansionLowCoupling.labelHarmonic_sub`: The harmonic assigned to a label difference equals the difference of the assigned harmonics. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L159).

**Closed-box representation of the measure** · theorem. `boxMeasure_eq_Icc`: Restricting planar Lebesgue measure to the closed unit-time and full-angle box gives the torus box measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L163).

**Move integrability to the closed box** · theorem. `integrableOn_Icc_of_box`: Integrability for the torus box measure implies integrability on the corresponding closed rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L169).

**Continuous box functions integrate** · theorem. `Breakdown.CertCell.AssemblyRowExpansionLowCoupling.integrable_box_of_continuous`: A continuous normed-space-valued function is integrable for the finite time-angle box measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L174).

**Continuity along time-angle orbits** · theorem. `continuous_orbit`: Restricting a continuous space-time field to a time-shifted axial-rotation orbit gives a continuous function of time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L179).

**Spatial slice derivatives are continuous** · theorem. `continuous_partialDeriv`: A C1 space-time function has spatial slice derivatives that depend continuously on time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L188).

**Rotation preserves vector addition** · theorem. `axialRot_add_vec`: Axial rotation sends the sum of two vectors to the sum of their rotations. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L198).

**Read a standard-coordinate sum** · theorem. `coord_sum_unitVector`: The ith coordinate of the sum of scalar multiples of coordinate vectors equals the ith scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L202).

**Alternating formula for the curl** · theorem. `curlVec_apply`: Each curl-vector coordinate is the alternating-tensor contraction of the linear map's coordinate columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L205).

**Finite Fourier expansion along an orbit** · theorem. `rot_expansion`: The rotated-back field along a time-angle orbit equals the real finite Fourier synthesis of its zero-time mode coefficients under the span hypothesis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L210).

**Vorticity inherits time periodicity** · theorem. `periodic_vorticity`: The time-periodic differentiable velocity field has time-periodic vorticity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L232).

**A C1 field has continuous vorticity** · theorem. `continuous_vorticity`: A vector field that is C1 in space-time has continuous spatial vorticity as a space-time field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L237).

**Vorticity has the same finite span** · theorem. `vorticity_span`: Under the field's differentiability and finite-mode span hypotheses, vorticity is the sum of the real parts of its modes on the same support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L243).

**Shift two real phase products** · theorem. `modeMean_pair`: The Fourier mean of the displayed two-product expression is the sum of the two explicit pairs of shifted mode means, multiplied by the real prefactor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L260).

**Opposite velocity modes are conjugate** · theorem. `conj_modeVel`: For a real vector field, conjugating a velocity-mode coordinate gives the coordinate at the negative frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L268).

**A velocity mode is a rotating mean** · theorem. `modeVel_zero_eq`: The zero-time velocity mode is the Fourier mean of the rotated-back velocity along the time-angle orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L272).

**Fourier convolution of the coupling** · theorem. `coupling_at_point`: The coupling-field mode equals the finite convolution of the given field's velocity and vorticity modes with the unknown field's shifted curl and velocity modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L278).

**A rotated matrix column integrates** · theorem. `integrable_apply_rot`: An integrable operator field applied to a continuously rotating unit vector is integrable on the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L381).

**Move a zero mode along an orbit** · theorem. `modeVel_zero_of_shift`: For a periodic orbit-integrable velocity field, a mode vanishing at one time-angle translate also vanishes at the zero-time base point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L392).

**Move a zero gradient mode along an orbit** · theorem. `modeGrad_zero_of_shift`: Under periodicity and orbit-integrability, a gradient mode vanishing at a time-angle translate also vanishes at the zero-time base point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L403).

**Curl agrees after label conversion** · theorem. `curlComp_gradArray`: The curl of the labelled gradient matrix equals the curl of its harmonic-indexed Fourier gradient at the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L430).

**The torus slice has nonzero measure** · theorem. `sliceMeasure_nonzero`: The time-angle slice measure used for orbit integrals is nonzero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L434).

**Label convolution almost everywhere** · theorem. `labelVel_coupling_plane`: For almost every positive-radius plane point, each labelled coupling velocity is the finite alternating-tensor convolution of the shifted gradient and velocity labels with the given field labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowCoupling.lean#L445).

### Breakdown.CertCell.AssemblyRowExpansionLowLong

This file establishes the off-axis measurability and pairing integrability required by the long part of the row identity. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**The cross test is jointly continuous** · theorem. `continuous_crossTest_triple`: Each cross-test coordinate depends continuously on its model velocity, model vorticity and test-vector arguments together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowLong.lean#L17).

**Bounded measurable models fit the test** · theorem. `pair_integrableOn_ae`: Coordinatewise finite radial energy and almost-everywhere bounded measurable model fields make the radial-weighted cross-test pairing integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowLong.lean#L32).

**Measurability extends across the axis** · theorem. `aestronglyMeasurable_off_axis`: The stated off-axis measurability yields almost-everywhere strong measurability of the full space-time field because the axis is null. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowLong.lean#L85).

**Orbit bounds control a label mode** · theorem. `norm_labelVel_le_orbit`: A bound on the field along the time-angle orbit bounds the norm of each labelled velocity coordinate by the same constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowLong.lean#L135).

### Breakdown.CertCell.AssemblyRowExpansionLowOffLabel

This file proves that harmonic coefficients outside the declared support vanish, including coefficients of the given field's vorticity. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal.RowIdentity.OffSupport`.**

**Separate time and angle phases** · theorem. `expFactor_split`: The negative Fourier phase factors into the product of its time exponential and its angular exponential. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L27).

**Nonconstant periodic exponentials cancel** · theorem. `integral_exp_period_eq_zero`: If c is nonzero and exp(cL) is one, the interval integral of exp(cx) from zero to L is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L36).

**Nonzero angular harmonics cancel** · theorem. `angle_integral_eq_zero`: For a nonzero integer angular frequency, the negative exponential has integral zero over a full angle period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L41).

**Nonzero time harmonics average to zero** · theorem. `time_integral_eq_zero`: For a nonzero integer time frequency, the negative exponential has integral zero over the unit time period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L55).

**Nonzero torus frequencies cancel** · theorem. `iter_expFactor_eq_zero`: The iterated time-angle integral of a nonzero frequency's negative phase is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L68).

**Half-open box representation** · theorem. `boxMeasure_eq_restrict`: The torus box measure is planar Lebesgue measure restricted to the half-open unit-time and full-angle rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L77).

**Continuous box functions integrate** · theorem. `Breakdown.CertCell.AssemblyRowExpansionLowOffLabel.integrable_box_of_continuous`: A continuous normed-space-valued function is integrable for the finite time-angle box measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L81).

**A finite nonconstant Fourier sum cancels** · theorem. `iter_sum_eq_zero`: The iterated torus integral of the displayed finite sum of nonzero-frequency phases is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L87).

**Conjugation gives the negative phase** · theorem. `conj_phase`: Conjugating the positive harmonic phase gives the negative Fourier exponential factor at the same frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L104).

**Expand a real phase product** · theorem. `expFactor_mul_re_phase`: Multiplying a negative Fourier phase by the complex-coerced real part of a positive phase gives the two half-weighted shifted negative phases with conjugate coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L110).

**Continuity along time-angle orbits** · theorem. `continuous_orbit_of`: Restricting a continuous space-time field to a time-shifted axial-rotation orbit gives a continuous function of time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L116).

**Read the coordinate-vector expansion** · theorem. `coord_of_sum`: The kth coordinate of the standard-coordinate expansion is its kth coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L122).

**Fourier synthesis in the rotating frame** · theorem. `rotated_expansion`: The rotated-back field equals the real finite Fourier sum over its specified mode support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L125).

**Modes vanish outside the finite support** · theorem. `modeVel_eq_zero_off_support`: Under the periodicity, integrability and finite-span hypotheses, every velocity mode outside the symmetric support is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L149).

**Spatial slice derivatives are continuous** · theorem. `continuous_spaceDeriv`: A C1 space-time function has spatial slice derivatives that depend continuously on time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L166).

**The curl keeps time periodicity** · theorem. `periodic_vorticityOf`: The vorticity of the specified differentiable time-periodic field is time periodic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L175).

**A C1 field has continuous vorticity** · theorem. `continuous_vorticityOf`: A vector field that is C1 in space-time has continuous spatial vorticity as a space-time field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L181).

**Coordinate expression for the curl** · theorem. `curlVec_coord`: Each curl coordinate is the alternating-tensor contraction of the linear map's coordinate entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L187).

**Finite Fourier synthesis of vorticity** · theorem. `vorticity_expansion`: The vorticity field equals the finite sum of the real parts of its Fourier velocity modes over the given support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L192).

**Source namespace `Breakdown.CertCell.Assembly.Internal.RowIdentity`.**

**Given-field labels vanish off support** · theorem. `labelVel_given_off_label`: Outside the prescribed harmonic-label support, both the given velocity and its vorticity have zero labelled velocity coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOffLabel.lean#L209).

### Breakdown.CertCell.AssemblyRowExpansionLowOrbit

This file transfers almost-everywhere statements from physical space to time-angle fibres and then to the half-plane coefficients. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Orbit coordinates preserve null sets** · theorem. `orbit_quasiMeasurePreserving`: The orbit map is quasi-measure-preserving from the orbit-coordinate measure to the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L13).

**Factor the orbit-coordinate measure** · theorem. `orbitMeasure_eq`: The orbit measure is the product of planar measure on the open radial half-plane and the time-angle slice measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L18).

**Restrict an almost-everywhere orbit fact** · theorem. `ae_slice_of_ae`: A period-almost-everywhere assertion holds on almost every time-angle slice above almost every positive-radius plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L20).

**Explicit time-angle slice measure** · theorem. `sliceMeasure_eq`: The slice measure is Lebesgue measure restricted to the half-open unit-time and full-angle rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L31).

**The slice measure is nonzero** · theorem. `sliceMeasure_ne_zero`: The unit-time full-angle slice measure is nonzero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L34).

**Radius of a rotated plane point** · theorem. `norm_orbit_sq`: The squared norm of a rotated plane point equals its radial coordinate squared plus its axial coordinate squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L44).

**Almost every orbit slice is integrable** · theorem. `ae_slice_integrable`: The supplied space-time integrability hypotheses give integrability along almost every positive-radius time-angle orbit slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L48).

**Descend a null identity to the plane** · theorem. `ae_plane_of_ae_space`: A spatial almost-everywhere zero identity descends to almost every positive-radius plane point when zeros along the rotation orbit imply the zero at the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L84).

**Finite field sums and Fourier data** · theorem. `labelVel_sum_of_slice`: Under the slice-integrability assumptions, the label coefficient of the finite real-linear field combination equals the same combination of label coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowOrbit.lean#L96).

### Breakdown.CertCell.AssemblyRowExpansionLowResolved

This file identifies resolved row pairings with the retained polynomial coefficients plus the orthogonal tail and band terms. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Expand a resolved cross-test pairing** · theorem. `cross_pair`: The packed profile paired with the conjugate cross test equals the coordinate contraction of the curl-velocity and vorticity-velocity cross terms against the conjugate test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L20).

**Separate a packed profile and its error** · theorem. `pairVec_split`: A packed profile equals a second packed profile plus the packed entrywise differences of their matrix and velocity components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L29).

**Packing preserves coordinate integrals** · theorem. `pairVec_int`: If every matrix and velocity coordinate is integrable on the region, every coordinate of their packed profile is integrable there. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L34).

**Polynomial cross tests are continuous** · theorem. `crossTest_cont`: Continuous model velocity and vorticity coordinates paired with a polynomial cell test give continuous cross-test coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L43).

**Factor radial weight through line weight** · theorem. `weight_split`: On the cell rectangle, the complex-coerced radius equals the product of the complex-coerced line weight and radius-ratio function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L60).

**Polynomial orthogonality of the tail** · theorem. `orth_zero`: With a valid cell basis and the stated integrability, the line-weighted pairing of a projection error with any polynomial in its projection space is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L69).

**The low coupling row uses finite data** · theorem. `low_part`: The row pairing of the projected coupling equals the coupling-row vector applied to the stored harmonic data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L87).

**Separate projected and tail pairings** · theorem. `tail_split`: The full radial-weighted profile pairing splits into its projected-profile pairing and the line-weighted projection error paired with the test remainder, using orthogonality of the removed polynomial test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L148).

**Finite row plus projection remainder** · theorem. `resolved_model_pairing`: The resolved model coupling pairing equals its finite harmonic-data row plus the explicit line-weighted pairing of profile and test projection errors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowResolved.lean#L244).

### Breakdown.CertCell.AssemblyRowExpansionLowRight

This file reads the Hessian-trace part of the strong right side in the cylindrical frame and proves its coefficient identity. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Local square bounds imply integrability** · theorem. `locallyIntegrable_of_localSquare`: The stated local square-integrability and measurability conditions make the space-time field locally integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L16).

**Local bounds imply integrability** · theorem. `locallyIntegrable_of_bound`: The measurable function with the stated local norm bounds is locally integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L61).

**A trace costs at most three norms** · theorem. `norm_trace_le_three`: The norm of a second derivative's vector trace is at most three times the norm of that second derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L70).

**Hessian in one frame direction** · definition. `traceColumn`: This vector evaluates the Hessian twice in one cylindrical frame direction; summing the three directions gives its trace. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L80).

**Compute the trace in a rotated frame** · theorem. `trace_frame`: The second-derivative trace equals the sum of its diagonal values in any axially rotated orthonormal frame. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L83).

**Fourier coefficient of a trace column** · theorem. `labelVel_traceColumn`: The labelled velocity coefficient of the selected trace column equals the corresponding repeated-index slope coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L100).

**Hessian frame columns are measurable** · theorem. `measurable_traceColumn`: Each trace column of an almost-everywhere strongly measurable Hessian field is almost-everywhere strongly measurable in space-time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L111).

**A trace column is norm bounded** · theorem. `norm_traceColumn_le`: The norm of each selected second-derivative trace column is at most the norm of the full second derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L120).

**Fourier form of the strong equation** · theorem. `labelVel_right_plane`: At almost every positive-radius plane point, each labelled forcing coefficient equals the displayed sum of time-frequency transport, spatial drift, negative derivative trace, finite coupling convolution, actuator and pressure terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowRight.lean#L129).

### Breakdown.CertCell.AssemblyRowExpansionLowTransport

This file shows that the transport defect vanishes in the rotating frame, which removes it from the row coefficient identity. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Rotated coordinate extraction** · theorem. `rotate_column_dot`: The dot product of a rotated coordinate vector with the same rotation of y is the corresponding coordinate of y. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L17).

**Rotation detects the zero vector** · theorem. `rotate_vec_eq_zero`: A vector whose specified complex-linear rotated coordinate representation vanishes must be zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L28).

**Rotation law for the transport defect** · theorem. `transportDefect_rotate`: Rotating the spatial base point transforms the Fourier transport defect by the corresponding phase and rotation of its vector components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L44).

**Transport zeros descend along an orbit** · theorem. `transportDefect_eq_zero_of_rotate`: Vanishing of the transport defect at the rotated point implies vanishing at the original point under its rotation covariance hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L77).

**The slice is a restricted rectangle** · theorem. `slice_eq_restrict`: The time-angle slice measure equals planar Lebesgue measure restricted to the half-open unit-time full-angle rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L94).

**Slice integrability on the closed box** · theorem. `integrableOn_of_slice`: Integrability for the slice measure gives integrability on the corresponding closed time-angle rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L98).

**A rotating derivative column integrates** · theorem. `column_of_slice`: An integrable gradient along the orbit remains integrable after evaluation on a rotating coordinate unit vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L107).

**Coordinates of the meridian point** · theorem. `planePoint_coords`: The plane embedding sends (r,z) to the three-dimensional vector with coordinates r, zero and z. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L124).

**Fourier transport on the meridian plane** · theorem. `labelVel_transport_plane`: At almost every positive-radius plane point, the labelled transport field equals the time-frequency plus one-half velocity term and one-half the radial and axial gradient contraction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionLowTransport.lean#L128).

### Breakdown.CertCell.AssemblyRowExpansionRest

This file supplies the frequency and deactivated-piece bounds from the common row-frame and weighted Gram estimates. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Model plane values have bounded energy** · theorem. `restPlane_facts`: Each model plane coordinate is almost-everywhere strongly measurable on the cell rectangle and their squared-norm sum has one uniform bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRest.lean#L17).

**Linearity for radial-weighted terms** · theorem. `restWeighted_lin`: The integral of a two-term radial-weighted linear combination equals the corresponding combination of integrals under their integrability hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRest.lean#L37).

**Bound the period-mismatch row term** · theorem. `freqPieceBound_holds`: Under the stated hypotheses, the inverse-Gram squared size of the period-mismatch term is bounded by its tested velocity allowance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRest.lean#L43).

**Bound deactivated row groups** · theorem. `deactPieceBound_holds`: Under the stated hypotheses, the weighted sum of inverse-Gram group contributions is bounded by the allocated deactivated-mode allowance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRest.lean#L90).

### Breakdown.CertCell.AssemblyRowExpansionRestDeact

This file bounds deactivated harmonic interactions by grouping partner modes and charging their curl and velocity leakage. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**A coarse bound for the curl vector** · theorem. `norm_curlVec_bound`: The norm of the encoded curl vector is at most 27 times the norm of its linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L20).

**Source section `Harmonics`.**

**Uniform bounds for the given modes** · theorem. `trueHarmonics_bound`: The weak second-derivative bound B is nonnegative and bounds every true velocity coefficient energy by three times B squared and every vorticity coefficient energy by three times (27B) squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L54).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Regroup deactivated partners** · theorem. `group_regroup`: The deactivated shift sum equals the sum over the specified partner groups with their harmonic membership restrictions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L75).

**Bound a sum by its size** · theorem. `norm_sum_sq_le_card`: The squared norm of the finite vector sum is at most the permitted number of terms times the sum of the individual squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L120).

**Negating a harmonic label** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestDeact.labelHarmonic_neg`: The harmonic assigned to the negative label is the negative of its original harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L127).

**Zero model fields give zero coupling** · theorem. `crossVec_zero`: The packed-profile coupling vector vanishes when both the model velocity and model vorticity vectors are zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L131).

**Curl energy of a labelled profile** · theorem. `curlOfU_bandProfile`: The curl slots of a band profile have squared-norm sum equal to the labelled mode curl energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L134).

**Velocity energy of a labelled profile** · theorem. `velOfU_bandProfile`: The velocity slots of a band profile have squared-norm sum equal to the labelled mode velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L143).

**Control curl slots by all slots** · theorem. `curlOfU_sq_le`: The sum of squared curl-slot norms is at most twice the squared-norm sum of the full twelve-coordinate profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L150).

**Control velocity slots by all slots** · theorem. `velOfU_sq_le`: The sum of squared velocity-slot norms is at most the squared-norm sum of the full twelve-coordinate profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L163).

**Bound the coupling vector by energy** · theorem. `crossVec_sq_le`: Bounds CW and COmega for the given velocity and vorticity squared energies bound the coupling vector energy by (4CW+2COmega) times the full profile energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L176).

**Coupling coordinates are measurable** · theorem. `crossVec_measurable`: Almost-everywhere strong measurability of the profile and both model vectors implies the same measurability for every coupling-vector coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L188).

**The bounded coupling test integrates** · theorem. `crossVec_term_integrable`: Finite radial energy of the profile, bounded measurable model energies and continuous test coordinates imply integrability of the radial-weighted coupling-test pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L201).

**Source section `Deact`.**

**One deactivated coupling vector** · definition. `deactVec`: This vector collects the row coupling contributed by one deactivated partner label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L255).

**Grouped deactivated coupling vector** · definition. `deactGroupVec`: This vector sums the deactivated interactions in one chosen harmonic group. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L261).

**Bound finite Fourier coefficient energy** · theorem. `trig_coef_sq_le`: The stated bound for a finite trigonometric vector synthesis bounds the sum of the squared norms of its coefficient vectors by the same constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L266).

**Energy bounds for a harmonic group** · theorem. `model_group_bound`: Within the cell, the group's summed velocity and vorticity model coefficient energies are bounded by the squares of its velocity and curl constants. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L307).

**Energy bound for one group harmonic** · theorem. `model_harmonic_bound`: Each harmonic belonging to the group obeys the group's squared velocity and vorticity coefficient bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L315).

**Pointwise deactivated-group bound** · theorem. `deact_pointwise`: The deactivated group's output coefficient energy is bounded by twice its velocity bound squared times partner curl energy plus twice its curl bound squared times partner velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L325).

**Sum through a common partner set** · theorem. `sum_partners_eq`: The sum over all group partner sets can be rewritten as a sum over the containing label set with group-membership indicators. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L383).

**Collect deactivated leakage by label** · theorem. `leak_pointwise`: The weighted sum of all deactivated-group energy allowances equals the sum of per-label curl and velocity energies weighted by the groups containing that label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L391).

**Tested partners of deactivated sources** · theorem. `guard_of_deactSources`: A label in the deactivated source set has a tested label whose difference from it lies in the prescribed harmonic support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L419).

**The curl leak covers all error families** · theorem. `leak_curl_guard`: The allocated curl leakage coefficient dominates the sum of deactivated, model-error and long-error curl costs under the guard hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L427).

**The velocity leak covers all errors** · theorem. `leak_vel_guard`: The allocated velocity leakage coefficient dominates the sum of deactivated, model-error and long-error velocity costs under the guard hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L439).

**Curl leakage covers deactivation** · theorem. `leak_curl_deact`: The allocated curl leakage coefficient dominates the deactivated groups' velocity-bound contribution at the label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L451).

**Velocity leakage covers deactivation** · theorem. `leak_vel_deact`: The allocated velocity leakage coefficient dominates the deactivated groups' curl-bound contribution at the label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestDeact.lean#L465).

### Breakdown.CertCell.AssemblyRowExpansionRestError

This file bounds the approximation-error contribution to the rows, with the row Gram scaling and long-mode split kept explicit. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Explicit negative exponential phase** · theorem. `conj_labelPhase_exp`: The conjugate label phase is the negative imaginary exponential of its time-angle harmonic argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L20).

**Fibre coefficients are harmonic modes** · theorem. `coefOf_fibVel`: The labelled Fourier coefficient of the complex-coerced rotating velocity fibre equals the corresponding zero-time harmonic velocity mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L30).

**The fibre keeps the physical norm** · theorem. `fibVel_sq`: The squared-norm sum of the rotating fibre's coordinates equals the squared physical field norm along the orbit. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L35).

**Rotating back preserves continuity** · theorem. `rotated_coordinate_continuous`: A coordinate of a continuous planar vector field rotated back by its angular argument is continuous after complex coercion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L41).

**The time-angle orbit map is continuous** · theorem. `orbit_pair_continuous`: The map sending time and angle to that time and the rotated spatial point is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L46).

**A continuous field restricts to an orbit** · theorem. `orbit_continuous_of_continuous`: Evaluating a continuous space-time field along the fixed point's axial-rotation orbit gives a continuous time-angle field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L50).

**Continuous fibres from continuous orbits** · theorem. `fibVel_continuous_of_orbit`: Continuity of the field along the orbit makes each complex-coerced rotating fibre coordinate continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L54).

**Continuity gives torus integrability** · theorem. `torusIntegrable_of_continuous_box`: A continuous function of time and angle is integrable on the compact time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L59).

**Subtract torus Fourier coefficients** · theorem. `coefOf_sub`: For integrable torus functions, the coefficient of their difference equals the difference of their coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L64).

**Combine low and high model errors** · theorem. `split_long_sq_bound`: The separate model and long-field error bounds imply that the squared norm of the remaining error is at most the square of the sum of their error constants. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L77).

**Subtract physical velocity fibres** · theorem. `fibVel_sub`: The difference of two rotating velocity fibres equals the fibre of the difference of the physical fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L88).

**Realize the model-error coefficients** · theorem. `error_field`: The supplied approximation bounds give an integrable torus vector bounded in squared norm by the total error constant squared, whose coefficients are true minus model minus long coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L95).

**The mean of a constant** · theorem. `torusMean_const`: The normalized torus mean of a constant is that constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L148).

**Bound one vector Fourier coefficient** · theorem. `coef_vec_sq_le`: A uniform squared-norm bound on an integrable torus vector bounds the squared-norm sum of each of its Fourier coefficient vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L158).

**The off-axis nonzero-height set is open** · theorem. `offAxis_isOpen`: The space-time set with positive cylindrical radius and nonzero cylindrical height is open. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L187).

**Orbit stays in the regular region** · theorem. `orbit_offAxis_mem`: The stated positive-radius and nonzero-height conditions place every time-angle orbit point in the off-axis nonzero-height set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L197).

**Off-axis continuity controls the orbit** · theorem. `orbit_continuous_of_offAxis`: A field continuous on the positive-radius nonzero-height region restricts continuously to each orbit based at a point in that region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L202).

**Measurable modes from off-axis fields** · theorem. `labelVel_measurable_of_offAxis`: A field continuous off the axis and zero-height plane has almost-everywhere strongly measurable labelled coordinates on every valid mesh cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L208).

**Source section `Error`.**

**Error contribution to a row vector** · definition. `errVec`: This vector records the row's coupling with the approximation-error field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L233).

**Almost-everywhere model-error bounds** · theorem. `error_pointwise`: Almost everywhere on the cell, the total error-coupling coefficient energy and each residual velocity and vorticity coefficient obey the displayed bounds from the low and high model errors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L239).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Rescale an inverse weighted square** · theorem. `inverseWeightedSq_inv_smul`: Multiplying the matrix by the reciprocal of a nonzero real c multiplies its inverse weighted square by c. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L301).

**Constant scaling of the row Gram** · theorem. `scaledRowGram_const`: Scaling every row-label weight by the same c makes the scaled row Gram matrix the original Gram matrix multiplied by the complex reciprocal of c. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L317).

**Model plane coefficients are measurable** · theorem. `modelPlaneValue_aesm`: Each component of a cell vector model's plane value is almost-everywhere strongly measurable on its valid cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L324).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Bound the approximation-error row term** · theorem. `errorPieceBound_of`: Under the stated hypotheses, the scaled inverse-Gram squared error is bounded by the resolved, band and deactivated approximation allowances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L336).

**Bound the approximation-error row term** · theorem. `errorPieceBound_holds`: Under the stated hypotheses, the scaled inverse-Gram squared error is bounded by the resolved, band and deactivated approximation allowances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestError.lean#L482).

### Breakdown.CertCell.AssemblyRowExpansionRestFrame

This file states the reconstruction of a cell vector field in the rotating frame as a finite label-phase sum. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Cell vector field in the rotating frame** · interface proposition. `VecFieldFrameStatement`: This predicate requires that a valid conjugate-closed cell vector field equals its finite label-phase expansion almost everywhere on each rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrame.lean#L17).

Proved by `Breakdown.CertCell.Assembly.Internal.vecFieldFrame`.

### Breakdown.CertCell.AssemblyRowExpansionRestFrameFacts

This file proves that vector-field reconstruction, including angle invariance, conjugate closure and the exclusion of overlapping cells almost everywhere. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal.VecFrame`.**

**Coordinates of a rotated plane point** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestFrameFacts.rot_plane_coords`: Rotating (r,0,z) gives (r cos φ,r sin φ,z). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L21).

**The rotated radial square** · theorem. `rot_plane_sq`: The sum of the squared cosine and sine coordinates at radius r is r squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L27).

**Recover the cylindrical radius** · theorem. `rot_plane_radius`: For nonnegative r, the cylindrical radius of the rotated plane point is r. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L31).

**Orbit membership matches the rectangle** · theorem. `rot_plane_solid_iff`: Under the stated plane-point conditions, membership of its axial rotation in the cell solid is equivalent to membership of the plane point in the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L36).

**Recover the plane point after rotation** · theorem. `rot_plane_back`: Converting the rotated plane point back to cylindrical plane coordinates returns the original point under its radius and height hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L45).

**The recovered angle has the same phase** · theorem. `rot_plane_angle`: At positive radius, the recovered angle of the rotated plane point has the same sine and cosine as the rotation angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L50).

**Matching angles give the same frame** · theorem. `unit_of_angle`: When the two angles have the same sine and cosine, the frame unit at one angle is the rotation of the standard unit vector by the other. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L68).

**Label phases depend only on the angle** · theorem. `phase_of_angle`: Angles with matching sine and cosine give the same integer-frequency label phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L74).

**Read coefficients in a rotated frame** · theorem. `frame_comps`: Rotating back a coordinate-vector combination in the rotated frame recovers each original coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L89).

**Negative labels conjugate the phase** · theorem. `phase_neg`: The phase of the negative label is the complex conjugate of the original label phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L98).

**Negative vector-model labels conjugate** · theorem. `value_neg`: For a conjugate-closed vector model, its plane value at the negative label is the conjugate of its value at the original label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L106).

**The model field in fibre coordinates** · theorem. `field_in_frame`: The rotating fibre of the assembled model field equals the real finite labelled-phase sum of the cell's plane coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L118).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Cell vector field in the rotating frame** · theorem. `vecFieldFrame`: Under the stated hypotheses, a valid conjugate-closed cell vector field equals its finite label-phase expansion almost everywhere on each rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestFrameFacts.lean#L147).

### Breakdown.CertCell.AssemblyRowExpansionRestGram

This file derives the inverse-Gram bound for diagonally scaled row vectors without changing the underlying quadratic form. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Rescale an inverse Gram quadratic** · theorem. `quadForm_inv_diagonal_scaled`: For the stated positive label-constant scales, the inverse quadratic of the row-divided matrix equals the original inverse quadratic on the square-root-scaled vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestGram.lean#L18).

**Source section `ScaledRows`.**

**Energy bound for weighted row moments** · theorem. `inverseWeightedSq_scaled_rows_le`: The inverse square for the scaled row Gram matrix is bounded by the label-weighted sum of radial profile-energy integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestGram.lean#L60).

### Breakdown.CertCell.AssemblyRowExpansionRestTests

This file converts row-test inequalities into inverse-Gram bounds and establishes the weighted integrability needed to apply them to physical coefficients. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**A scalar square-completion inequality** · theorem. `two_re_mul_conj_sub_le`: Twice the real part of f times conjugate(u), minus the squared norm of u, is at most the squared norm of f. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L18).

**Weighted square bounds give a product** · theorem. `integrable_weight_mul_conj`: Two measurable complex functions with integrable squared norms under the same nonnegative measurable weight have integrable weighted conjugate product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L24).

**Collapse a sum over label fibres** · theorem. `sum_fiber_ite`: Summing row terms over all labels with equality indicators selects exactly the term at each row's own label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L41).

**Gram inverse bound from test pairings** · theorem. `quadForm_inv_le_of_tests`: The moment and Gram identities with the stated positive-definiteness and integrability assumptions bound the inverse-Gram quadratic by the total weighted source energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L47).

**Cell polynomial evaluation is continuous** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestTests.cellPoly_eval_continuous`: Evaluating a fixed cell polynomial gives a continuous function of the radial-height point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L193).

**The cell rectangle is compact** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestTests.rect_isCompact`: The cell's closed and bounded radial-height rectangle is compact. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L197).

**Nonnegative radius in the rectangle** · theorem. `rect_first_nonneg`: Every point in a valid cell rectangle has nonnegative radial coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L199).

**Continuous real cell functions integrate** · theorem. `integrableOn_rect_of_continuous`: A continuous real function is integrable on the compact cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L202).

**The cell rectangle is measurable** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestTests.rect_measurableSet`: The closed radial-height rectangle associated with a cell box is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L206).

**Radius is almost everywhere nonnegative** · theorem. `ae_rect_first_nonneg`: The radial coordinate is nonnegative almost everywhere for the measure restricted to the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L208).

**Source section `Rows`.**

**Polynomial row tests are continuous** · theorem. `rowTestValue_continuous`: Every coordinate of each polynomial row test is continuous in the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L215).

**The row Gram controls moment energy** · theorem. `inverseWeightedSq_rows_le`: The inverse weighted square of the row moment vector is bounded by the sum of radial-weighted profile energies over tested labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L219).

**Two-energy bound for a difference** · theorem. `norm_sub_sq_le_two`: The squared norm of x minus y is at most twice the squared norm of x plus twice the squared norm of y. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L245).

**Match the curl encodings** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestTests.curlComp_eq`: The certificate curl of a matrix equals the curl computed from its pair-indexed gradient array. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L250).

**Bound curl energy by matrix energy** · theorem. `curlSq_le_sumSq`: The matrix curl energy is at most twice the full matrix squared-norm sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L254).

**Energy splits between packed slots** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestTests.sum_pairVec_sq`: The squared-norm sum of a packed matrix and vector equals the matrix entry energy plus the vector coordinate energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L262).

**Locate a labelled velocity coordinate** · theorem. `velAt_eq_bandProfile`: Labelled velocity coordinate a is coordinate 9+a of the band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L267).

**Locate a labelled gradient entry** · theorem. `gradAt_eq_bandProfile`: Labelled gradient entry (a,b) is coordinate 3a+b of the band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L277).

**Measured coordinates and finite energy** · theorem. `profile_facts`: The labelled velocity and gradient coordinates are almost-everywhere strongly measurable and their combined radial-weighted squared energy is integrable on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L287).

**Radial integrability passes to a bound** · theorem. `integrableOn_of_le_weighted`: A measurable nonnegative profile dominated by a constant times a radial-integrable profile is itself radial-integrable on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L304).

**Velocity and curl energies integrate** · theorem. `profile_integrable`: True-field regularity and a compatible cell tuple give integrability of radial-weighted velocity energy, curl energy and each velocity-coordinate energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L313).

**The full gradient energy integrates** · theorem. `sumSq_integrable`: True-field regularity and a compatible cell tuple give integrability of the radial-weighted squared-norm sum of the labelled gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L345).

**A nonnegative radial integral** · theorem. `weighted_integral_nonneg`: The radial-weighted integral of a pointwise nonnegative profile on a valid cell rectangle is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L357).

**Add and increase allowance terms** · theorem. `weighted_three_le`: For the stated nonnegative profiles and coefficient inequalities, the two-term weighted integral is bounded by the three-term integral with the larger outer coefficients and nonnegative middle contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L363).

**Distribute two weighted energy terms** · theorem. `weighted_two_eq`: Multiplying the weighted integral of a two-term energy combination by c gives the two separate integrals with coefficients multiplied by c. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L384).

**Increase two energy coefficients** · theorem. `weighted_two_le`: The coefficient comparisons for nonnegative profiles bound the two weighted integrals by the integral with the larger coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTests.lean#L394).

### Breakdown.CertCell.AssemblyRowExpansionRestTorus

This file proves the Fourier coefficient and square-sum estimates used by all row-error terms on the time-angle torus. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Normalized harmonic coefficient** · definition. `coefOf`: This coefficient is the normalized time-angle mean against the conjugate label phase. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L19).

**The label phase is continuous** · theorem. `labelPhase_continuous`: For each fixed label and azimuth order, its complex phase depends continuously on time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L22).

**A label phase has unit norm** · theorem. `norm_labelPhase`: Every time-angle phase associated with a label has complex norm one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L26).

**Continuous functions on the torus box** · theorem. `Breakdown.CertCell.AssemblyRowExpansionRestTorus.torusIntegrable_of_continuous`: The continuous function with the stated bound is integrable on the compact time-angle box, using the supplied torus facts where required. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L30).

**Phases preserve torus integrability** · theorem. `torusIntegrable_phase_mul`: Multiplication by a label phase preserves integrability on the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L35).

**Difference rule for paired label phases** · theorem. `phase_mul_conj`: A label phase times a conjugate label phase is the conjugate phase at the second label minus the first. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L42).

**Distinct label phases are orthogonal** · theorem. `torusMean_phase_conj`: For positive azimuth order, the torus mean of one label phase times the conjugate of another is one for equal labels and zero for distinct labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L47).

**A phase shifts the Fourier label** · theorem. `coefOf_phase_mul`: Multiplying an integrable torus function by the phase at alpha shifts its coefficient at ell to the original coefficient at ell minus alpha. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L55).

**Constants integrate on the torus box** · theorem. `torusIntegrable_const`: Every constant complex function is integrable on the finite time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L63).

**Extract a finite labelled coefficient** · theorem. `coefOf_trig`: The coefficient of a finite labelled Fourier sum is its stored coefficient on the support and zero outside the support, under label-harmonic injectivity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L66).

**Finite Fourier sums are continuous** · theorem. `trig_continuous`: A finite sum of fixed complex coefficients times label phases is continuous in time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L84).

**Bound a finite Fourier synthesis** · theorem. `norm_trig_le`: The norm of a finite phase-weighted sum is at most the sum of the norms of its coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L88).

**Finite Fourier sums integrate** · theorem. `trig_integrable`: Every finite sum of fixed complex coefficients times label phases is integrable on the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L93).

**Mean square of a finite Fourier sum** · theorem. `torusMean_trig_sq`: The torus mean of a finite Fourier sum times its conjugate equals the sum of the complex-coerced coefficient squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L97).

**Complex square-completion estimate** · theorem. `re_two_mul_conj_sub_le`: The real part of twice f times conjugate(u) minus u times conjugate(u) is at most the squared norm of f. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L119).

**Bessel bound for finitely many labels** · theorem. `coef_sq_sum_le`: The squared norms of finitely many labelled Fourier coefficients sum to at most the torus mean of the function's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L126).

**Complex three-vector cross product** · definition. `crossC`: This vector uses the alternating symbol to form the complex bilinear cross product. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L180).

**Energy bound for a complex cross product** · theorem. `crossC_norm_le`: The squared-norm sum of the complex cross product is at most the product of the two input squared-norm sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L183).

**Curl of a twelve-coordinate vector** · definition. `curlOfU`: This vector contracts the gradient block with the alternating symbol. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L193).

**Velocity of a twelve-coordinate vector** · definition. `velOfU`: This vector selects the last three coordinates of the twelve-coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L195).

**Complex coupling vector** · definition. `crossVec`: This vector combines the perturbation's curl and velocity with the given velocity and vorticity according to the coupling formula. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L197).

**Match the complex alternating signs** · theorem. `alternatingSymbol_cast_eq`: Coercing the real alternating tensor and the certificate permutation sign to complex numbers gives equal entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L199).

**The cross test represents the coupling** · theorem. `crossTest_pairing`: Pairing the full profile with the conjugate cross test equals pairing the coupling vector with the conjugate test vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L204).

**Two-energy bound for a sum** · theorem. `norm_add_sq_le_two`: The squared norm of x plus y is at most twice the sum of their squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L210).

**Bound the two coupling products** · theorem. `crossVec_norm_le`: The coupling-vector energy is at most twice the curl-energy times velocity-model energy plus twice the vorticity-model energy times velocity-profile energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L215).

**Curl positions in the packed profile** · theorem. `curlOfU_explicit`: The three curl components of a packed profile are coordinates 7 minus 5, 2 minus 6, and 3 minus 1. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L225).

**Expand coupling in profile coordinates** · theorem. `crossVec_expand_U`: The coupling vector is the sum of the input profile coordinates times its values on the standard coordinate vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L229).

**Expand coupling in model coordinates** · theorem. `crossVec_expand_WΩ`: The coupling vector splits into its coordinate expansions in the velocity-model and vorticity-model arguments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L243).

**Finite sums of Fourier coefficients** · theorem. `coefOf_lin`: The Fourier coefficient of the displayed two finite linear combinations equals the same combinations of the individual coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L247).

**Convolution of phases and coefficients** · theorem. `coefOf_sum_phase`: The Fourier coefficient of a finite phase-weighted function sum equals the sum of the corresponding shifted coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L272).

**Coupling is linear in the profile** · theorem. `crossVec_sum_U`: Applying the coupling vector to a finite scalar combination of profiles gives the same scalar combination of their coupling vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L285).

**Curl of a finite profile combination** · theorem. `curlOfU_sum`: Taking curl slots commutes with the finite scalar-weighted sum of profile vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L295).

**Velocity of a finite profile combination** · theorem. `velOfU_sum`: Taking velocity slots commutes with the finite scalar-weighted sum of profile vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L313).

**Parseval identity for a finite sum** · theorem. `mean_trig_normSq`: The torus mean of the squared norm of a finite labelled Fourier sum equals the sum of its coefficient squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L319).

**A bounded torus square integrates** · theorem. `torusIntegrable_normSq_of_bound`: A torus-integrable function with a uniform squared-norm bound has torus-integrable squared norm after complex coercion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L326).

**Bound a coupling convolution by energy** · theorem. `cross_coef_sum_le`: The sum of output coupling coefficient energies is bounded by twice the velocity-error bound times source curl energy plus twice the vorticity-error bound times source velocity energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowExpansionRestTorus.lean#L334).

### Breakdown.CertCell.AssemblyRowParts

This file defines the separate row contributions and their allowance interfaces, then states the uniform implication that combines them into a row-moment bound. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source section `RowParts`.**

**Given-field velocity coefficients** · definition. `trueVelocity`: These coefficients are the harmonic velocity coefficients of the given reference field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L20).

**Given-field vorticity coefficients** · definition. `trueVorticity`: These coefficients are the harmonic velocity coefficients of the reference vorticity field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L22).

**Long-part velocity coefficients** · definition. `longVelocity`: These coefficients are the harmonic coefficients of the row's long velocity field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L25).

**Long-part vorticity coefficients** · definition. `longVorticity`: These coefficients are the harmonic coefficients of the row's long vorticity field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L28).

**Polynomial row test on a cell** · definition. `rowTestValue`: This value evaluates the cell polynomial belonging to the selected row and velocity component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L31).

**Period-mismatch row contribution** · definition. `freqPiece`: This row vector multiplies the velocity pairing by the time frequency and the difference between the actual and model inverse periods. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L34).

**Approximation-error row contribution** · definition. `errorPiece`: This row vector records the contribution of the field approximation error. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L40).

**Long-mode row contribution** · definition. `longPiece`: This row vector records the contribution of the separate long-mode field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L50).

**One deactivated group contribution** · definition. `deactGroupPiece`: This row vector records interactions with one deactivated partner group. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L58).

**Total deactivated row contribution** · definition. `deactPiece`: This row vector sums the deactivated group contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L67).

**Actuator row contribution** · definition. `actuatorPiece`: This row vector records the coefficients of the actuator fields in the row pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L73).

**Decompose the row-moment error** · proposition definition. `RowIdentity`: This predicate requires that the right-side row moment minus the retained row and tail equals the sum of period, approximation, long, deactivated and actuator contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L77).

**Period-mismatch row allowance** · definition. `freqAllowance`: This amount bounds the period-mismatch term using the inverse-period error and the tested velocity-mode energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L86).

**Approximation-error allowance** · definition. `errorAllowance`: This density assigns the curl and velocity costs reserved for the field-error contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L91).

**Long-mode row-error allowance** · definition. `longAllowance`: This density assigns the class-dependent costs reserved for long-mode row errors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L97).

**Bound the period-mismatch row term** · proposition definition. `FreqPieceBound`: This predicate requires that the inverse-Gram squared size of the period-mismatch term is bounded by its tested velocity allowance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L102).

**Bound the approximation-error row term** · proposition definition. `ErrorPieceBound`: This predicate requires that the scaled inverse-Gram squared error is bounded by the resolved, band and deactivated approximation allowances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L108).

**Deactivated-mode row allowance** · definition. `deactAllowance`: This density assigns the row costs for the chosen deactivated partner group. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L115).

**Bound the long-mode row term** · proposition definition. `LongPieceBound`: This predicate requires that the long-scaled inverse-Gram squared term is bounded by the resolved, band and deactivated long-mode allowances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L121).

**Bound deactivated row groups** · proposition definition. `DeactPieceBound`: This predicate requires that the weighted sum of inverse-Gram group contributions is bounded by the allocated deactivated-mode allowance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L128).

**Regroup the deactivated row term** · proposition definition. `DeactSplit`: This predicate requires that the deactivated row contribution is the sum of its designated group contributions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L134).

**Bound the actuator row error** · proposition definition. `ActuatorPieceBound`: This predicate requires that the scaled inverse-Gram squared actuator error is bounded by the actuator cost, error constant and squared κ norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L139).

**Fit the row allowances into budgets** · proposition definition. `AllowanceSplit`: This predicate requires that resolved, band and deactivated allowances fit respectively into the box, band and leakage budgets, retaining the pairing slack. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L145).

**Decompose the row-moment error** · interface proposition. `RowIdentityHolds`: This interface requires that the right-side row moment minus the retained row and tail equals the sum of period, approximation, long, deactivated and actuator contributions whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L157).

Proved by `Breakdown.CertCell.Assembly.rowIdentity_holds`.

**Bound the period-mismatch row term** · interface proposition. `FreqPieceBoundHolds`: This interface requires that the inverse-Gram squared size of the period-mismatch term is bounded by its tested velocity allowance whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L165).

Proved by `Breakdown.CertCell.Assembly.freqPieceBound_holds`.

**Bound the approximation-error row term** · interface proposition. `ErrorPieceBoundHolds`: This interface requires that the scaled inverse-Gram squared error is bounded by the resolved, band and deactivated approximation allowances whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L171).

Proved by `Breakdown.CertCell.Assembly.errorPieceBound_of`, `Breakdown.CertCell.Assembly.errorPieceBound_holds`.

**Bound the long-mode row term** · interface proposition. `LongPieceBoundHolds`: This interface requires that the long-scaled inverse-Gram squared term is bounded by the resolved, band and deactivated long-mode allowances whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L181).

Proved by `Breakdown.CertCell.Assembly.longPieceBound_holds`.

**Regroup the deactivated row term** · interface proposition. `DeactSplitHolds`: This interface requires that the deactivated row contribution is the sum of its designated group contributions whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L187).

Proved by `Breakdown.CertCell.Assembly.deactSplit_holds`.

**Bound deactivated row groups** · interface proposition. `DeactPieceBoundHolds`: This interface requires that the weighted sum of inverse-Gram group contributions is bounded by the allocated deactivated-mode allowance whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L193).

Proved by `Breakdown.CertCell.Assembly.deactPieceBound_holds`.

**Fit the row allowances into budgets** · interface proposition. `AllowanceSplitHolds`: This interface requires that resolved, band and deactivated allowances fit respectively into the box, band and leakage budgets, retaining the pairing slack whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L199).

Proved by `Breakdown.CertCell.Assembly.allowanceSplit_holds`.

**Bound the actuator row error** · interface proposition. `ActuatorPieceBoundHolds`: This interface requires that the scaled inverse-Gram squared actuator error is bounded by the actuator cost, error constant and squared κ norm whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L205).

Proved by `Breakdown.CertCell.Assembly.actuatorPieceBound_holds`.

**Combine the separate row bounds** · interface proposition. `RowCombineHolds`: This interface requires that the row identity, its five bounds and the allowance split imply the row-moment expansion estimate whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowParts.lean#L211).

Proved by `Breakdown.CertCell.Assembly.rowCombine`.

### Breakdown.CertCell.AssemblyRowRemoval

This file removes row constraints from the retained profile estimate by bounding the polynomial-tail correction through the row Gram form. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source section `Apply`.**

**Projection errors have finite energy** · lemma. `grad_facts`: Every labelled gradient and velocity projection error is almost-everywhere strongly measurable and has integrable line-weighted squared norm on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L30).

**Tail coordinates have finite energy** · lemma. `profile_facts`: Periodic second-order field and pressure regularity imply that each tail coordinate is measurable and has finite line-weighted squared norm on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L71).

**Tail gradient energy in packed slots** · lemma. `strain_eq`: The gradient tail energy equals the line-weighted integral of the squared tail-profile coordinates among the first nine slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L98).

**Tail velocity energy in packed slots** · lemma. `vel_eq`: The velocity tail energy equals the line-weighted integral of the squared tail-profile coordinates among the final three slots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L118).

**Tail Gram entries as test integrals** · lemma. `pairMatrix_eq`: The selected gradient or velocity tail Gram block is the line-weighted integral of conjugate row-tail tests times row-tail tests over that slot class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L136).

**Row action on the polynomial tail** · definition. `crossRow`: This row vector measures the correction caused by replacing the full coefficient profile by its retained polynomial part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L143).

**Source section `Split`.**

**Split tail rows by label and slot class** · lemma. `tailRow_split`: The complete tail row vector equals the sum over resolved labels of its gradient-slot and velocity-slot cross rows. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L155).

**Bound a row-tail cross contribution** · lemma. `tail_bound`: The scaled tail Gram quadratic is nonnegative, and its square-completion expression with the cross row is bounded above by the scale times the selected tail-slot energy integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L179).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Remove row tails using allocated costs** · theorem. `rowRemoval_core`: The resolved row inverse square is bounded by the base moment inverse square, allocated gradient and velocity tail energies, and the leakage inverse square of the remaining row defect. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L204).

**Remove row tails with allocated costs** · theorem. `rowRemoval`: Under the stated hypotheses, the inverse retained-row form is bounded by physical row share, tail costs and the inverse leakage-Gram row remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemoval.lean#L267).

### Breakdown.CertCell.AssemblyRowRemovalAlgebra

This file supplies the quadratic-form identities, positivity and weighted projection estimates used in row removal. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source section `Algebra`.**

**Subtract matrices in a quadratic form** · lemma. `quad_sub`: The quadratic value of a matrix difference equals the difference of the two matrix quadratic values on the same vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L24).

**Add matrices inside the quadratic** · lemma. `quad_add`: The quadratic form of the sum of two matrices is the sum of their quadratic forms on the same vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L28).

**Add finitely many matrix quadratics** · lemma. `quad_sum`: The quadratic form of a finite matrix sum equals the sum of their quadratic values on the same vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L32).

**Reciprocal scaling of a matrix** · lemma. `quad_smul`: Multiplying the matrix by the reciprocal of a real c multiplies its quadratic value by the reciprocal of c. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L39).

**A quadratic is unchanged by vector sign** · lemma. `quad_neg`: Negating the input vector leaves the real-valued complex quadratic form unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L44).

**Nonnegativity of semidefinite forms** · lemma. `Breakdown.CertCell.AssemblyRowRemovalAlgebra.quad_nonneg`: A positive semidefinite complex matrix has nonnegative real quadratic value at every complex vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L47).

**A scaled inverse-form estimate** · lemma. `scaled_bound`: The stated positive matrix and positive scale give the square-completion bound for twice the real dot pairing minus the inverse-scale matrix form by the scaled inverse-matrix form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L50).

**Assemble the row removal inequality** · lemma. `assemble`: The matrix and tail-pairing hypotheses bound the target inverse quadratic by the base inverse quadratic, the allocated tail energies and the scaled leakage inverse quadratic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L65).

**The base row matrix is positive definite** · lemma. `base_posDef`: The stated positive-definiteness and matrix comparison assumptions imply positive definiteness of the base matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L130).

**Source section `Tail`.**

**Integrability after applying the weight** · lemma. `int_weighted`: The weight and profile hypotheses make the complex-coerced weighted integrand integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L161).

**Move the selected-coordinate sum outside** · lemma. `sum_three_swap`: The finite sums over two row indices and a selected coordinate set can be reordered with the coordinate sum outermost. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L169).

**A pointwise Gram quadratic is energy** · lemma. `pt_quad`: The quadratic form of the weighted test Gram matrix equals the complex coercion of the weight times the squared-norm sum of the combined tests. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L175).

**Combine a pointwise cross pairing** · lemma. `pt_dot`: The row-coordinate dot product with the weighted cross moments equals the weighted profile pairing with the conjugate combined test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L185).

**Weighted two-factor estimate** · lemma. `Breakdown.CertCell.AssemblyRowRemovalAlgebra.two_mul_le_weighted`: For positive beta, twice a times b is at most beta times a squared plus b squared divided by beta. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L194).

**Weighted profile-test products integrate** · lemma. `int_cross`: The regularity and weighted square-integrability hypotheses make the finite weighted cross pairing of the profile and row test integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L201).

**A weighted Gram controls a cross term** · lemma. `tail_piece`: For nonnegative integrable weight, finite weighted profile energy and bounded measurable tests, the scaled Gram quadratic is nonnegative and the negative cross pairing minus that quadratic is bounded by the scaled profile energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L229).

**Source section `Cell`.**

**Extract gradient energy from packed data** · lemma. `pair_strain`: The squared-norm sum over the first nine packed coordinates equals the squared-norm sum of all matrix entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L349).

**Extract velocity energy from packed data** · lemma. `pair_vel`: The squared-norm sum over the last three packed coordinates equals the squared-norm sum of the velocity vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L356).

**Cell projections are continuous** · lemma. `Breakdown.CertCell.AssemblyRowRemovalAlgebra.proj_continuous`: The cell's finite polynomial projection is a continuous function of the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L362).

**Continuity of the planar line weight** · lemma. `lineWeight_cont`: Composing the cell line weight with the radial coordinate gives a continuous planar function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L372).

**The cell rectangle is measurable** · lemma. `Breakdown.CertCell.AssemblyRowRemovalAlgebra.rect_measurable`: The closed radial-height rectangle associated with a cell box is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L376).

**The cell rectangle is compact** · lemma. `Breakdown.CertCell.AssemblyRowRemovalAlgebra.rect_compact`: The cell's closed and bounded radial-height rectangle is compact. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L378).

**Two-sided control of the line weight** · lemma. `lineWeight_bounds`: On a valid cell rectangle, line weight lies between zero and (one plus the reciprocal inner radius) times radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L380).

**The line weight has finite integral** · lemma. `weight_integrable`: The cell line weight is integrable for Lebesgue measure restricted to the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L395).

**Line weight is nonnegative on the cell** · lemma. `weight_nonneg`: The line weight is nonnegative almost everywhere on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L398).

**A dominated profile has a regular tail** · lemma. `tail_part`: A measurable scalar profile dominated in squared norm by a radial-integrable bound has measurable polynomial-projection error and finite line-weighted error energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L402).

**Source namespace `Breakdown.CertCell.Assembly.Internal.RowRemoval`.**

**One bound for finitely many tests** · lemma. `uniform_bound`: The stated finite-family continuity and compactness hypotheses give one nonnegative almost-everywhere bound for every test coordinate on the region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L436).

**Finite coordinate energy is nonnegative** · lemma. `Breakdown.CertCell.AssemblyRowRemovalAlgebra.cnormSq_nonneg`: The squared-coordinate norm of a finite complex vector is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowRemovalAlgebra.lean#L447).

### Breakdown.CertCell.AssemblyRowShareStacked

This file relates the stacked row-coordinate quadratic form to the cell row-share form through the exact coordinate embeddings. Appendix B.3: row representation and residual bounds, especially (B.26) and (B.43).

**Source namespace `Breakdown.CertCell.Assembly.Internal`.**

**Relabel a quadratic form** · theorem. `quadForm_submatrix_equiv`: Pulling a matrix back along an index equivalence gives the same quadratic form as composing the vector with the inverse equivalence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowShareStacked.lean#L18).

**A block diagonal quadratic splits** · theorem. `quadForm_blockDiagonal`: The quadratic form of a block diagonal matrix is the sum of the block quadratic forms on the corresponding subvectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowShareStacked.lean#L24).

**Scale a matrix quadratic** · theorem. `quadForm_smul`: Multiplying the matrix by a real scalar multiplies its quadratic value by that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowShareStacked.lean#L39).

**Source namespace `Breakdown.CertCell.Assembly`.**

**Read row share as an inverse Gram form** · theorem. `rowShareStacked_holds`: Under the stated hypotheses, the physical row share equals the inverse base-weight form of the stacked row moments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyRowShareStacked.lean#L48).

### Breakdown.CertCell.AssemblyStatements

This file defines the analytic quantities and interfaces that connect cell calculus, rows, pressure recovery, exterior control and tree elimination. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source section `Residual`.**

**Velocity and gradient of one mode** · definition. `bandProfile`: This vector places the nine harmonic gradient entries before the three harmonic velocity entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L23).

**Quadratic band-profile cost** · definition. `bandQuad`: This amount integrates the weighted squared band-profile coordinates over the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L27).

**Linear coupling to band profiles** · definition. `bandLinear`: This amount integrates twice the real pairing between a linear source field and the band profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L30).

**Square-integrable band coordinates** · proposition definition. `BandSquareIntegrable`: This predicate requires that each selected band coordinate is measurable and its total radius-weighted squared norm is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L35).

**Row value including the band** · definition. `rowVector`: This vector adds the finite row-map value to the row's integral pairing with the band modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L39).

**Squared gradient projection tail** · definition. `tailStrainSq`: This value sums the weighted projection-tail norms of the nine gradient components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L44).

**Squared velocity projection tail** · definition. `tailVelSq`: This value sums the three velocity projection-tail norms at one degree below the gradient cutoff. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L48).

**Squared curl projection tail** · definition. `tailCurlSq`: This value sums the three curl projection-tail norms at the gradient cutoff degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L52).

**Squared curl of one harmonic** · definition. `modeCurlSq`: This is the sum of squared norms of the three curl components of the harmonic gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L56).

**Squared gradient of one harmonic** · definition. `modeStrainSq`: This is the sum of squared norms of the nine harmonic gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L59).

**Squared velocity of one harmonic** · definition. `modeVelSq`: This is the sum of squared norms of the three harmonic velocity entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L62).

**Integrated row leakage charge** · definition. `rowLeakAmount`: This amount integrates the reserved curl and velocity costs over the row leakage labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L65).

**Integrated pairing leakage charge** · definition. `pairingLeakAmount`: This amount integrates the reserved gradient cost over the row leakage labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L70).

**Integrated resolved box penalty** · definition. `boxAmount`: This amount sums the radius-weighted box penalty on the resolved harmonic profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L74).

**Curl and velocity allowance on the band** · definition. `bandAllowance`: This amount integrates the designated curl and velocity costs on band labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L78).

**Cell share of the boundary credit** · definition. `creditAmount`: This value is the cell-calculus credit share assigned to the velocity field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L83).

**Selected pairing slack** · definition. `pairSlackAmount`: This value keeps the strain slack on the intersection of the requested labels and the prescribed slack labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L86).

**Deactivated labels carrying slack** · definition. `deactSlackLabels`: This finite set contains pairing-slack labels outside both the resolved and band sets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L89).

**Squared actuator-coordinate norm** · definition. `kappaSq`: This value sums squared norms over the actuator block of the cell vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L92).

**Integrated resolved-mode density** · definition. `resolvedAmount`: This amount integrates the label density over resolved harmonics with the cylindrical radius weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L95).

**Integrated mean stretching** · definition. `stretchAmount`: This value integrates the mean stretching density over the cell with cylindrical radius weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L99).

**Net omitted-mode allocation** · definition. `offChargeAmount`: This amount sums the full label density minus the charged off-mode density over unresolved harmonics. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L103).

**A compatible physical cell tuple** · structure. `IsCellTuple`: This predicate requires that the parameter, perturbation, pressure gradient, strong right side, energy finiteness and pressure reflection conditions hold for the same fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L110).

**Finite positive and negative pieces** · proposition definition. `CellPiecesFinite`: This predicate requires that the cell's negative piece and both charged off-mode pieces are finite for every admissible physical cell tuple. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L123).

**Split the signed cell allocation** · proposition definition. `AllocationSplit`: This predicate requires that the difference of positive and negative allocations equals the resolved density, omitted-mode charge and mean stretching. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L128).

**Angular derivative relation in the band** · proposition definition. `IsBandTurned`: This predicate requires that the radius-scaled angular gradient column equals the turn matrix applied to the velocity block almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L135).

**Physical states lie in the chosen set** · proposition definition. `CellStatesIn`: This predicate requires that every physical cell state, with all allowed real and complex auxiliary coordinates, belongs to the designated state predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L140).

**The cell potential-stage estimate** · proposition definition. `PotentialStage`: This predicate requires that the retained potential form and its band, leakage, credit and slack costs are covered by resolved density, omitted charge and stretching after energy credits. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L146).

**The cell pairing-stage estimate** · proposition definition. `PairingStage`: This predicate requires that the retained pairing form and its band cross term are bounded by the physical pairing share, gradient tail costs and pairing leakage. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L162).

**The cell row-stage estimate** · proposition definition. `RowStage`: This predicate requires that the inverse-weighted row form and resolved pairing slack are bounded by the physical row share and the allocated tail, box, leakage, band and actuator costs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L171).

**The cell tail-stage estimate** · proposition definition. `TailStage`: This predicate requires that the negative top form is bounded by tail credit after all gradient, velocity and curl tail costs are paid. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L183).

**Eliminate the band and row variables** · proposition definition. `EliminationStage`: This predicate requires that on the prescribed state space, the cell residual form is bounded by the retained potential, pairing and top forms together with the band and inverse-row terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L191).

**Regularity of all cell profiles** · proposition definition. `CellProfileRegular`: This predicate requires that all harmonic profiles have measurable coordinates and finite radius-weighted squared norms whose integrals are summable over labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L201).

**Physical band profiles are integrable** · proposition definition. `BandProfileIntegrable`: This predicate requires that every admissible physical cell tuple supplies square-integrable band coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L207).

**Physical band profiles obey turning** · proposition definition. `BandProfileTurned`: This predicate requires that every admissible physical cell tuple satisfies the angular derivative relation on band labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L210).

**Measurable harmonic bound data** · structure. `AmplitudesMeasurable`: This predicate requires that the supplied velocity, gradient, vorticity and curl-gradient amplitude bounds and their suprema are measurable for every allowed parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L213).

**Measurable exterior form densities** · proposition definition. `ExteriorDensityMeasurable`: This predicate requires that all label densities and the mean stretching are measurable on the exterior half-plane for admissible perturbations. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L218).

**Measurable cell form densities** · proposition definition. `CellDensityMeasurable`: This predicate requires that all label densities and the mean stretching are measurable on every cell rectangle for admissible perturbations. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L223).

**Measurable rotating stretching integrand** · proposition definition. `StretchIntegrandMeasurable`: This predicate requires that the stretching form is measurable jointly in the cell point, time and rotation angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L228).

**Measurable modes of the given field** · proposition definition. `GivenModeMeasurable`: This predicate requires that the given velocity, gradient, Hessian and vorticity harmonic coefficients are measurable on each cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L235).

**The assembled true-field regularity** · proposition definition. `TrueFieldRegular`: This predicate requires that profile regularity and all cell, exterior, stretching and given-mode measurability conditions hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L244).

**The assembled true-field regularity** · interface proposition. `TrueFieldRegularHolds`: This interface requires that profile regularity and all cell, exterior, stretching and given-mode measurability conditions hold together whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L248).

Proved by `Breakdown.CertCell.Assembly.trueFieldRegularHolds`.

**Finite positive and negative pieces** · interface proposition. `CellPiecesFiniteHolds`: This interface requires that the cell's negative piece and both charged off-mode pieces are finite for every admissible physical cell tuple whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L251).

Proved by `Breakdown.CertCell.Assembly.cellPiecesFiniteHolds`.

**Bound data make densities measurable** · interface proposition. `DensityMeasurableHolds`: This interface requires that admissible weak bounds, a weak second-derivative state and measurable bound data imply cell-density measurability whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L258).

A named provider for this exact interface was not identified in the source.

**Split the signed cell allocation** · interface proposition. `AllocationSplitHolds`: This interface requires that the difference of positive and negative allocations equals the resolved density, omitted-mode charge and mean stretching whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L265).

Proved by `Breakdown.CertCell.Assembly.allocationSplitHolds`.

**Physical band profiles are integrable** · interface proposition. `BandProfileIntegrableHolds`: This interface requires that every admissible physical cell tuple supplies square-integrable band coordinates whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L270).

Proved by `Breakdown.CertCell.Assembly.bandProfileIntegrable_holds`.

**Physical band profiles obey turning** · interface proposition. `BandProfileTurnedHolds`: This interface requires that every admissible physical cell tuple satisfies the angular derivative relation on band labels whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L273).

Proved by `Breakdown.CertCell.Assembly.bandProfileTurned_holds`, `Breakdown.CertCell.bandProfileTurned_closed`.

**Positive-part encoding ignores negatives** · theorem. `ofReal_eq_ofReal_max`: The extended-nonnegative coercion of a real number equals the coercion of its maximum with zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L276).

**Combine four nonnegative real charges** · theorem. `ofReal_add_four`: For four nonnegative real terms, the sum of their extended-nonnegative coercions equals the coercion of their sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L281).

**Recover a signed real number** · theorem. `max_sub_max_neg`: The positive part of t minus the positive part of minus t equals t. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L285).

**Encode a signed real budget** · theorem. `signed_budget`: The stated signed real budget and finiteness hypotheses imply the displayed extended-nonnegative inequality using positive-part terms on the appropriate sides. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L292).

**Source section `StageConditions`.**

**Velocity tail from top data** · proposition definition. `TopBound`: This predicate requires that each resolved velocity tail is bounded by the selected top quadratic block plus the gradient tail divided by its spectral gain. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L317).

**Spectral gains for gradient and curl** · interface proposition. `TailGainHolds`: This interface requires that the Hessian and curl tail gains control the corresponding gradient and curl tail norms, and the curl tail is at most twice the gradient tail whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L322).

Proved by `Breakdown.CertCell.Assembly.tailGainHolds`.

**The cell tail-stage estimate** · interface proposition. `TailStageHolds`: This interface requires that the negative top form is bounded by tail credit after all gradient, velocity and curl tail costs are paid whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L334).

Proved by `Breakdown.CertCell.Assembly.tailStage_of_parts`.

**Velocity tail from top data** · interface proposition. `TopBoundHolds`: This interface requires that each resolved velocity tail is bounded by the selected top quadratic block plus the gradient tail divided by its spectral gain whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L339).

Proved by `Breakdown.CertCell.Assembly.topBound_of`.

**The cell tail-stage estimate** · theorem. `tailStage_of_parts`: Under the stated hypotheses, the negative top form is bounded by tail credit after all gradient, velocity and curl tail costs are paid. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L346).

**Source section `Rows`.**

**Right-side row moments** · definition. `rowMoment`: This vector integrates each harmonic right-side coefficient against its polynomial row test with radius weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L416).

**Actual profile minus its projection** · definition. `tailProfile`: This vector subtracts the retained polynomial projection from each gradient and velocity coordinate, using their respective cutoff degrees. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L420).

**Integrated row-tail correction** · definition. `tailRow`: This vector pairs every resolved projection-tail profile with the corresponding row-tail test using the cell line weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L429).

**Bound the row-moment remainder** · proposition definition. `RowMomentExpansion`: This predicate requires that the inverse leakage-Gram norm of the row remainder and resolved slack are bounded by the allocated box, tail, leakage, band and actuator budgets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L434).

**Read row share as an inverse Gram form** · interface proposition. `RowShareStackedHolds`: This interface requires that the physical row share equals the inverse base-weight form of the stacked row moments whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L445).

Proved by `Breakdown.CertCell.Assembly.rowShareStacked_holds`.

**Remove row tails with allocated costs** · interface proposition. `RowRemovalHolds`: This interface requires that the inverse retained-row form is bounded by physical row share, tail costs and the inverse leakage-Gram row remainder whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L452).

Proved by `Breakdown.CertCell.Assembly.rowRemoval`.

**The cell row-stage estimate** · interface proposition. `RowStageHolds`: This interface requires that the inverse-weighted row form and resolved pairing slack are bounded by the physical row share and the allocated tail, box, leakage, band and actuator costs whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L469).

Proved by `Breakdown.CertCell.Assembly.rowStage_of_parts`.

**Source section `PotentialPairing`.**

**Partner cost for approximation error** · definition. `epsPartnerCharge`: This split charge uses the error bounds and the prescribed length scales for the profile paired with the retained part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L487).

**Partner cost for long modes** · definition. `longPartnerCharge`: This split charge multiplies the long-mode error cost by the label's cutoff-dependent factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L490).

**Tail norm of the coupling action** · definition. `couplingTail`: This sum measures the projection tail of the model action on retained upper profiles, separately for gradient or velocity coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L494).

**Partner cost for high-degree errors** · definition. `highPartnerCharge`: This form bounds the partner's curl, gradient and velocity squared norms with reciprocals of the positive balancing parameters. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L501).

**Integrated high-degree partner cost** · definition. `highPartnerAmount`: This amount integrates the high-degree partner charge over the supplied finite label set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L505).

**Source section `RowFunctionals`.**

**Bound the row-moment remainder** · interface proposition. `RowMomentExpansionHolds`: This interface requires that the inverse leakage-Gram norm of the row remainder and resolved slack are bounded by the allocated box, tail, leakage, band and actuator budgets whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L525).

Proved by `Breakdown.CertCell.Assembly.rowMomentExpansion_of_parts`, `Breakdown.CertCell.rowMomentExpansion_closed`.

**Source section `Pressure`.**

**Smooth compact solenoidal test field** · proposition definition. `IsStationaryTestField`: This predicate requires that the stationary test field is smooth, compactly supported and divergence-free everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L537).

**Solenoidal annihilator is a gradient** · interface proposition. `AnnihilatorGradientHolds`: This interface requires that a measurable locally square-integrable field annihilating all stationary solenoidal tests is a gradient field whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L540).

Proved by `Breakdown.CertCell.Assembly.annihilatorGradient_holds`.

**Annihilate space-time test fields** · proposition definition. `IsSpaceTimeAnnihilator`: This predicate requires that the vector field pairs to zero with every permitted space-time solenoidal test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L544).

**Local square norm over one period** · proposition definition. `HasLocalSquare`: This predicate requires that the squared norm has finite integral on one time period and every spatial closed ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L547).

**Harmonic coefficients annihilate tests** · interface proposition. `HarmonicAnnihilatorHolds`: This interface requires that a periodic locally square-integrable space-time annihilator has locally square-integrable cosine and sine coefficients that annihilate stationary tests whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L550).

Proved by `Breakdown.CertCell.Assembly.harmonicAnnihilator_holds`.

**Remainder to be read as pressure** · definition. `strongRemainder`: This field subtracts the transport, negative Hessian trace, coupling and actuator terms from the right side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L559).

**The remainder satisfies its identity** · theorem. `strongRightSide_remainder`: The explicitly constructed strong remainder satisfies the strong right-side equation by its defining algebraic identity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L564).

**The chosen pressure is the remainder** · theorem. `chosenPressure_eq_remainder`: The chosen pressure field is the strong remainder formed from the admissible tuple and its flip-averaged forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L572).

**Facts needed to recover pressure** · structure. `PressureFacts`: This predicate requires that the given weak model, its symmetry class and reflection, and the actuator harmonic shapes agree with the certificate data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L577).

**Reflection-average the right side** · interface proposition. `FlipAverageRightSideHolds`: This interface requires that averaging the right side with its reflection preserves measurability, periodicity, finite squared norm and the weak right-side equation whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L584).

Proved by `Breakdown.CertCell.Assembly.flipAverageRightSide_holds`.

**The pressure remainder annihilates tests** · interface proposition. `RemainderAnnihilatesHolds`: This interface requires that the remainder of an admissible weak right side annihilates all space-time solenoidal test fields whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L591).

Proved by `Breakdown.CertCell.Assembly.remainderAnnihilates_holds`.

**Regularity of the pressure remainder** · interface proposition. `RemainderRegularHolds`: This interface requires that the pressure remainder is measurable, periodic and locally square-integrable over one period whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L599).

Proved by `Breakdown.CertCell.Assembly.remainderRegular_holds`.

**Recover the periodic pressure gradient** · interface proposition. `PressureRecoveryHolds`: This interface requires that the pressure facts suffice to recover the periodic pressure-gradient interface whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L610).

Proved by `Breakdown.CertCell.Assembly.pressureRecoveryHolds_of_pressureParts`, `Breakdown.CertCell.Assembly.pressureRecovery_of_parts`, `Breakdown.CertCell.pressureRecovery_closed`.

**Recover the periodic pressure gradient** · theorem. `pressureRecovery_of_parts`: Under the stated hypotheses, the pressure facts suffice to recover the periodic pressure-gradient interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L613).

**Source section `OffModes`.**

**The covered omitted modes vanish** · interface proposition. `OffModesVanishHolds`: This interface requires that the regularity, admissibility and sound off-mode cover supply the omitted-mode vanishing condition whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L632).

Proved by `Breakdown.CertCell.Assembly.offModesVanish_of_sound`, `Breakdown.CertCell.Assembly.offModesVanishHolds`.

**Exterior density after off-mode charge** · definition. `exteriorChargeDensity`: This density is the full label density minus the off-mode density on the exterior. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L639).

**Exterior charges cover stretching** · proposition definition. `ExteriorStretchCharged`: This predicate requires that the negative exterior charged density and stretching have finite total mass and are dominated by their positive counterparts. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L646).

**Constants for exterior decay** · structure. `ExteriorDecayEntry`: This record supplies a radius and the strain, mean curl-gradient and oscillatory curl-gradient decay constants. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L655).

**Decay bounds for the exterior field** · proposition definition. `ExteriorDecay`: This predicate requires that beyond the given radius, strain decays quadratically and mean and oscillatory curl-gradient bounds decay cubically. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L661).

**Decay bounds for the exterior field** · interface proposition. `ExteriorDecayHolds`: This interface requires that beyond the given radius, strain decays quadratically and mean and oscillatory curl-gradient bounds decay cubically whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L670).

A named provider for this exact interface was not identified in the source.

**Near and far exterior charge bounds** · structure. `ExteriorChargeConditions`: This predicate requires that the near-region charge bound, far-field charge inequalities, positive length scales and nonnegative decay constants hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L675).

**Extend the charge bound to the exterior** · interface proposition. `ExteriorChargeBoundHolds`: This interface requires that the exterior decay and charge conditions yield the region charge bound on the whole exterior half-plane whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L688).

A named provider for this exact interface was not identified in the source.

**Supply the charged exterior estimate** · interface proposition. `ExteriorStretchChargedHolds`: This interface requires that the regular field, harmonic expansion, exterior charge bound and valid cover give the charged exterior stretching inequality whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L693).

Proved by `Breakdown.CertCell.Assembly.exteriorStretchCharged_of_point`, `Breakdown.CertCell.Assembly.exteriorStretchCharged`.

**Nonnegative exterior contribution** · interface proposition. `ExteriorNonnegHolds`: This interface requires that the admissible field, mode-class and valid exterior-cover conditions imply nonnegativity of the exterior form whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L702).

Proved by `Breakdown.CertCell.exteriorNonneg_of_offModeSound`.

**Source section `Tree`.**

**Rows match the chosen physical state** · proposition definition. `RowsMatchState`: This predicate requires that every used row evaluated on the chosen tree data equals the corresponding shifted-state coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L726).

**Rows match arbitrary compatible fields** · proposition definition. `RowsMatchFields`: This predicate requires that every used row evaluated on compatible periodic fields equals the corresponding shifted-field coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L731).

**Reflection of the chosen pressure** · proposition definition. `ChosenPressureFlips`: This predicate requires that the chosen pressure gradient commutes with the spatial reflection almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L748).

**Transport row matching to chosen data** · interface proposition. `RowsMatchStateOfFieldsHolds`: This interface requires that pressure recovery and reflection transfer field-level row matching to the chosen physical state whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L752).

Proved by `Breakdown.CertCell.Assembly.rowsMatchStateOfFields_holds`.

**Source section `Initial`.**

**Split the form into cells and exterior** · interface proposition. `FormSplitHolds`: This interface requires that a valid cell mesh partitions both the positive and negative form into the cell contributions and the exterior contribution whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L773).

Proved by `Breakdown.CertCell.Assembly.formSplit_holds`.

**Source section `CellLayerBreakdown`.**

**The ten residual-assembly inputs** · structure. `ResidualParts`: This predicate requires that finiteness, allocation, band integrability, potential, pairing, row, tail, turning, state and elimination conditions hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L786).

**Joint conditions for cell assembly** · structure. `AssemblyConditions`: This predicate requires that the cell, row, coupling, tail, regularity, admissibility and unused-coordinate requirements hold for the same supplied assembly data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyStatements.lean#L799).

### Breakdown.CertCell.AssemblyTailGain

This file obtains the spectral gain in the unresolved polynomial tail from the cell basis eigenvalues and the turned-mode derivative identities. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Coefficients ignore null-set changes** · theorem. `coef_congr`: Two profiles equal almost everywhere on the cell rectangle have identical cell polynomial coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L27).

**Both cell eigenvalues are nonnegative** · theorem. `eigen_nonneg`: The radial and height eigenvalues are nonnegative at every natural-number degree. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L32).

**Nonnegative cell inner-radius factor** · theorem. `innerRadius_nonneg`: The inner-radius factor of a valid cell box is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L39).

**A tail index pays the omitted level** · theorem. `min_le_eigen`: Outside the square degree cutoff, the sum of the radial and height eigenvalues is at least the smaller first-omitted eigenvalue. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L45).

**The omitted coefficients sum to the tail** · theorem. `Breakdown.CertCell.AssemblyTailGain.tail_hasSum`: For a measurable profile with finite line-weighted energy and a valid cell basis, the sum of squared coefficients outside the square degree cutoff equals its projection-tail squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L68).

**Weighted tails from derivative energy** · theorem. `grad_tail_sum`: The weak derivative and finite-energy hypotheses make the eigenvalue-weighted omitted-coefficient series summable and bound its inner-radius multiple by the gradient tail weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L92).

**Lift coefficient gains to tail energy** · theorem. `gain_core`: Weak radial and height derivative identities, weighted integrability and the coefficientwise gain inequality imply the corresponding summed tail-energy bound with angular contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L129).

**Lift a coefficient comparison to tails** · theorem. `tail_le_core`: A uniform comparison of coefficient energies beyond the degree cutoff implies the same comparison of the summed tail norms for the weighted square-integrable profiles. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L170).

**Combine radial and angular tail gains** · theorem. `gain_point`: Beyond the degree cutoff, the stated angular lower bound and axis compatibility imply that the tail-gain coefficient times S is bounded by the radial-height eigenvalue contribution plus the angular contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L186).

**Turned slopes from the gradient** · theorem. `turned_ae`: Almost everywhere in the cell, the turned slope is the stated angular linear combination of the labelled gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L212).

**The matrix rotation loses at most two** · theorem. `strain_shift`: The squared angular action on a matrix controls its entry energy multiplied by max(abs(k)-2,0) squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L236).

**Curl energy fits twice the matrix energy** · theorem. `curl_le`: The squared-norm sum of the three matrix curl components is at most twice the squared-norm sum of all matrix entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L252).

**Gain bounds for gradient and curl tails** · theorem. `label_tail_gain`: The labelled gradient and curl tails obey their Hessian and curl gain bounds, and the curl tail norm is at most twice the gradient tail norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTailGain.lean#L264).

### Breakdown.CertCell.AssemblyTiedParts

This file records the corner, odd-stream and pressure-reflection interfaces needed to keep the chosen cell data consistent across boundaries. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Harmonic data recover corner moments** · interface proposition. `HarmonicCornerDataStatement`: This predicate requires that the harmonic cell data at a corner equal the corresponding weak corner moments for compatible periodic fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTiedParts.lean#L16).

Proved by `Breakdown.CertCell.Assembly.harmonicCornerData_of`, `Breakdown.CertCell.Assembly.harmonicCornerData_holds`.

**Odd time modes have zero corner stream** · interface proposition. `OddStreamZeroStatement`: This predicate requires that an odd temporal harmonic in the specified symmetry class has zero corner-stream data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTiedParts.lean#L31).

Proved by `Breakdown.CertCell.Assembly.oddStreamZero_holds`.

**Supply chosen-pressure reflection** · interface proposition. `ChosenPressureFlipHolds`: This interface requires that the pressure facts imply that the chosen pressure gradient commutes with reflection almost everywhere whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTiedParts.lean#L38).

Proved by `Breakdown.CertCell.Assembly.chosenPressureFlip_holds`.

### Breakdown.CertCell.AssemblyTopBoundCore

This file derives the upper bound on retained and tail gradient coefficients from weak derivative pairings and the orthogonal cell basis. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Lift real test pairings to complex form** · theorem. `test_lift`: The weighted complex test pairing of F is the pairing of its cosine part plus i times the pairing of its sine part under the stated decomposition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L22).

**Lift real coefficients to complex ones** · theorem. `coef_lift`: The cell coefficient of the complex profile equals its cosine coefficient plus i times its sine coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L38).

**Radial eigenvalue from a weak derivative** · theorem. `coef_radial_of_weak`: The weak radial integration-by-parts identity expresses the radial eigenvalue times a cell coefficient as the derivative profile paired with the weighted radial basis derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L46).

**Height eigenvalues from weak derivatives** · theorem. `coef_height_of_ibp`: The weak height identity expresses the height eigenvalue times a cell coefficient as the derivative profile paired with the weighted height basis derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L104).

**Radial derivative coefficient budget** · theorem. `radial_fin_gen`: The selected radial-eigenvalue-weighted profile coefficients and selected derivative coefficients together fit within the line-weighted radial derivative energy under the specified index separation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L129).

**Height derivative coefficient budget** · theorem. `height_fin_gen`: The selected height-eigenvalue-weighted profile coefficients and selected derivative coefficients together fit within the line-weighted height derivative energy under the specified index separation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L155).

**The omitted coefficients sum to the tail** · theorem. `Breakdown.CertCell.AssemblyTopBoundCore.tail_hasSum`: For a measurable profile with finite line-weighted energy and a valid cell basis, the sum of squared coefficients outside the square degree cutoff equals its projection-tail squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L186).

**A squared projection tail is nonnegative** · theorem. `tail_nonneg`: The squared projection-tail norm is nonnegative for every cell box, degree and profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L200).

**Convert finite indices to a filtered set** · theorem. `split_eval`: The double sum over finite degree indices with a predicate equals the sum over the corresponding filtered Cartesian product of natural-number ranges. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L203).

**Control the top velocity tail** · theorem. `tail_top_bound`: The tail at degree Q minus one is bounded by the selected top radial and height derivative coefficients divided by their eigenvalues, plus the remaining derivative tails divided by the smaller eigenvalue. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L211).

**Lift real-part energy to complex energy** · theorem. `weighted_of_lift`: If a complex profile equals a cosine part plus i times a sine part almost everywhere, measurability and finite line-weighted energies of both parts give the same properties for the full profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L342).

**Finite tail energy gives full energy** · theorem. `weighted_of_tail`: For an almost-everywhere measurable profile, finite line-weighted energy of one polynomial-projection error implies finite line-weighted energy of the full profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L355).

**Top-tail bound with alternate premises** · theorem. `tail_top_bound'`: The alternate regularity premises give the same top-coefficient and derivative-tail upper bound for the tail at degree Q minus one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L374).

**Control one labelled velocity tail** · theorem. `label_component_bound`: A labelled velocity coordinate's tail is bounded by its selected top radial and axial gradient coefficients and the corresponding remaining gradient tails with the stated eigenvalue factors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L412).

**Control the full labelled velocity tail** · theorem. `label_tail_bound`: The sum of velocity-coordinate tails is bounded by the selected top radial and axial gradient coefficients plus the full gradient tail energy, with the displayed inverse eigenvalue factors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L468).

**Stored data are gradient coefficients** · theorem. `label_lowStrain_data`: The indicated low-strain harmonic-data coordinate equals the corresponding labelled gradient coefficient in the cell basis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTopBoundCore.lean#L491).

### Breakdown.CertCell.AssemblyTreeState

This file shows that the physical cell data respect the row embeddings and that unused or gauge coordinates do not change the assembled tree form. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source namespace `Breakdown.CertCell.Assembly.TreeStateInternal`.**

**Add real matrices inside the form** · theorem. `quadValue_add_left`: The real quadratic value is additive in its matrix argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L17).

**Negate a real quadratic matrix** · theorem. `quadValue_neg_left`: Negating the matrix negates its real quadratic value at every vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L21).

**Sum real matrices inside the form** · theorem. `quadValue_sum_left`: The real quadratic value of a finite matrix sum is the sum of the values of its summands. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L25).

**Repeat a real quadratic matrix** · theorem. `quadValue_nsmul_left`: The real quadratic form of n copies of a matrix is n times the original quadratic value. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L32).

**Add complex matrices inside the form** · theorem. `quadFormValue_add_left`: The complex matrix quadratic value is additive in its matrix argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L41).

**Sum complex matrices inside the form** · theorem. `quadFormValue_sum_left`: The complex matrix quadratic value of a finite matrix sum is the sum of its summands' values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L45).

**Real and complex leaf values agree** · theorem. `quadValue_realLeafForm_eq`: The real leaf quadratic at a real state equals the complex leaf quadratic after the state is coerced and passed through the embedding matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L52).

**Null directions do not change the form** · theorem. `quadFormValue_add_null`: Adding a vector annihilated by both the matrix and its conjugate transpose leaves the complex quadratic value unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L64).

**Ignore coordinates with zero rows** · theorem. `quadFormValue_eq_of_null_coords`: Two vectors have the same quadratic value when they agree at each coordinate except coordinates whose matrix row and column are both zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L74).

**Source section `Tree`.**

**Tree pieces reconstruct the cell form** · theorem. `sum_pieceForm_eq`: Summing every pair-indexed tree piece form for a cell reconstructs its cell form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L92).

**Source section `Rows`.**

**An unused reason supplies an unused row** · theorem. `unusedRow_of_unused`: The tree-row conditions turn the row's unused-reason flag into the full unused-row property. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L158).

**Cell coordinates of the row embedding** · theorem. `rowEmbed_apply_cell`: The cell-coordinate component of the real-to-complex row embedding equals the row value computed from the slaved state. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L166).

**Read a port from free coordinates** · theorem. `rowEmbed_apply_port`: The port component of the row embedding is the selected real free coordinate plus the selected imaginary coordinate with the stored conjugation sign. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L178).

**Read an actuator embedding coordinate** · theorem. `rowEmbed_apply_kappa`: The actuator component of the row embedding is the complex coercion of the selected slaved actuator coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L191).

**Read an auxiliary embedding coordinate** · theorem. `rowEmbed_apply_zeta`: The auxiliary component of the row embedding is the complex coercion of the selected free coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L200).

**Source section `Geometry`.**

**Pressure segments avoid an axis crossing** · theorem. `presSegments_off_axis`: Each pressure segment has strictly positive smaller endpoint level or has its other endpoint equal to zero, as required by the off-axis trace alternative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L215).

**Source section `Main`.**

**A head unit selects one label** · theorem. `headUnit_sum_cell`: At a cell harmonic-data coordinate, the resolved-label sum of weighted head units reduces to that coordinate's label weight times its pressure unit moment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeState.lean#L250).

### Breakdown.CertCell.AssemblyTreeStateHead

This file identifies the pressure-head coordinates under a constant pressure shift, preserving the corresponding side moments and harmonic data. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Segment test functions are continuous** · theorem. `test_continuous`: Every degree-indexed test function attached to a face segment is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L17).

**Constant pressure gives a constant mode** · theorem. `presMode_one_const`: The pressure mode of the constant-one scalar function does not depend on the radial or axial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L21).

**Add a pressure shift to a radial moment** · theorem. `radial_add`: The radial strip moment of F plus a fixed scalar times G, with the original derivative data, splits into the F moment plus the scaled G moment with zero derivative data under the integration hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L25).

**Add a pressure shift to a height moment** · theorem. `height_add`: The weighted height strip moment of F plus a fixed scalar times G, with the original derivative data, splits into the F moment plus the scaled G moment with zero derivative data under the integration hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L49).

**Pressure constants shift one mode** · theorem. `presMode_shift`: Subtracting one pressure constant instead of another changes the pressure mode almost everywhere by their difference times the constant-one pressure mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L74).

**Pressure shifts change moments linearly** · theorem. `presMoment_shift`: The pressure-segment moment changes by the constant difference times the constant-one pressure moment when the derivative data are unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L91).

**Head data differ by one gauge direction** · theorem. `headData_eq_shift`: The head data equal the true data plus the explicit gauge-normalization difference times the pressure unit-moment vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L163).

**One scalar accounts for the head gauge** · theorem. `headHarmonic_eq_shift`: There is a single complex scalar such that every head harmonic datum equals the corresponding harmonic datum plus that scalar times the pressure unit moment. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateHead.lean#L189).

### Breakdown.CertCell.AssemblyTreeStateZero

This file proves that zero velocity and derivatives give the zero compatible cell and gauge data, including the chosen pressure representatives. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source namespace `Breakdown.CertCell.Assembly.BaseStateInternal`.**

**Velocity modes of zero vanish** · theorem. `modeVel_of_zero`: Every Fourier velocity mode of the zero field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L19).

**Gradient modes of zero vanish** · theorem. `modeGrad_of_zero`: Every Fourier gradient mode of the zero linear-map field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L23).

**Hessian modes of zero vanish** · theorem. `modeHess_of_zero`: Every Fourier second-derivative mode of the zero Hessian field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L28).

**Zero fields have zero label density** · theorem. `labelDensity_of_zero`: The label density vanishes when velocity, gradient and Hessian are all zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L33).

**Zero perturbations have zero stretch** · theorem. `stretch_of_zero`: The stretching form vanishes when the perturbation velocity and gradient are zero, for every reference field and reference Hessian. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L40).

**Zero positive allocation for zero fields** · theorem. `formPos_of_zero`: The positive form allocation vanishes when velocity, gradient and Hessian are zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L45).

**Rows evaluate to zero on a zero field** · theorem. `rows_of_zero`: The certificate row vector evaluated on the zero velocity field is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L50).

**Zero inputs give zero scalar value** · theorem. `scalar_of_zero`: The scalar form vanishes when all displayed fields and actuator coefficients are zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L53).

**Zero-field value is nonpositive** · theorem. `value_of_zero`: An admissible tuple with zero velocity, gradient, Hessian, actuator coefficients and forcing has nonpositive value at the coercivity parameter. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L57).

**Zero data give zero chosen pressure** · theorem. `chosenPressure_of_zero`: Under the stated zero-data hypotheses, the chosen pressure remainder is the zero field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L71).

**The zero field has zero cosine harmonic** · theorem. `harmonicCos_of_zero`: The cosine harmonic transform of the zero field is zero at every time frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L78).

**The zero field has zero sine harmonic** · theorem. `harmonicSin_of_zero`: The negative-sine harmonic transform of the zero field is zero at every time frequency. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L83).

**The zero cosine tuple** · theorem. `cosTuple_of_zero`: Applying the cosine tuple construction to zero fields gives the zero field tuple. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L88).

**The zero sine tuple** · theorem. `sinTuple_of_zero`: Applying the sine tuple construction to zero fields gives the zero field tuple. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L91).

**Zero is a gradient field** · theorem. `gradientField_zero`: The zero vector field satisfies the gradient-field predicate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L94).

**Zero profiles have zero side moments** · theorem. `moment_of_zero`: A side moment with zero scalar profile and zero radial and height derivative profiles is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L103).

**Moments ignore null-set profile changes** · theorem. `moment_congr_ae`: Replacing the scalar profile by an almost-everywhere equal profile leaves its side moment unchanged when the derivative data stay fixed. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L108).

**Mean of an almost-everywhere constant** · theorem. `ballMean_of_const`: If the potential of the zero field equals C almost everywhere, its average over the unit ball is C. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L118).

**Normalized zero pressure vanishes** · theorem. `headPressure_of_zero`: The head-pressure representative of the zero tuple vanishes almost everywhere after its gauge normalization. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L123).

**Source section `Layout`.**

**Zero tuples have zero velocity modes** · theorem. `velMode_of_zero`: Every velocity-mode coordinate of the zero field tuple is the identically zero profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L146).

**Zero tuples have zero gradient modes** · theorem. `gradModeOf_of_zero`: Every gradient-mode coordinate of the zero field tuple is the identically zero profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L151).

**Zero tuples have zero Hessian modes** · theorem. `secondModeOf_of_zero`: Every second-derivative-mode coordinate of the zero field tuple is the identically zero profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L156).

**Zero tuples have zero pressure modes** · theorem. `pressureGradMode_of_zero`: Every pressure-gradient-mode coordinate of the zero field tuple is the identically zero profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L161).

**Zero tuples have zero key values** · theorem. `keyValue_of_zero`: Every selected skeleton-key value of the zero field tuple is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L166).

**Zero tuples have zero head data** · theorem. `headData_of_zero`: Every head datum of the zero field tuple is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L188).

**Source namespace `Breakdown.CertCell.Assembly.BaseStateInternal`.**

**Zero fields have zero head harmonics** · theorem. `headHarmonic_of_zero`: The pressure-head harmonic data vanish when all their physical field inputs are zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L212).

**Zero fields have zero key harmonics** · theorem. `keyHarmonic_of_zero`: The harmonic value of every skeleton key vanishes when all its physical field inputs are zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L215).

**Source section `Tree`.**

**Zero fields have zero gauge data** · theorem. `fieldGauge_of_zero`: Every tree field-gauge coordinate vanishes on zero velocity, gradient, Hessian and pressure data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L222).

**A zero tuple gives zero tree data** · theorem. `trueData_of_zero`: The tree's true-data vector is zero for an admissible tuple whose velocity, derivatives, transport, actuator coefficients and forcing are all zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTreeStateZero.lean#L225).

### Breakdown.CertCell.AssemblyTrueRegular

This file converts the proved field-regularity facts into the assembled true-field regularity interface. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**The assembled true-field regularity** · theorem. `trueFieldRegular_of_fieldRegular`: Under the stated hypotheses, profile regularity and all cell, exterior, stretching and given-mode measurability conditions hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegular.lean#L15).

**The assembled true-field regularity** · theorem. `trueFieldRegularHolds`: Under the stated hypotheses, profile regularity and all cell, exterior, stretching and given-mode measurability conditions hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegular.lean#L33).

### Breakdown.CertCell.AssemblyTrueRegularParts

This file establishes the coefficient measurability, weighted square bounds and density measurability needed by the cell assembly. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**The plane embedding is continuous** · theorem. `Breakdown.CertCell.AssemblyTrueRegularParts.continuous_planePoint`: The embedding (r,z) into the vector (r,0,z) is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L20).

**The plane embedding is measurable** · theorem. `measurable_planePoint`: The embedding (r,z) into the vector (r,0,z) is measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L26).

**The rectangle lies in the half-plane** · theorem. `Breakdown.CertCell.AssemblyTrueRegularParts.rect_ae_le_halfPlane`: The cell rectangle is contained in the positive radial half-plane up to a Lebesgue-null set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L28).

**Restrict a half-plane null-set relation** · theorem. `restrict_ac`: Under the stated almost-everywhere containment, measure restricted to S is absolutely continuous with respect to measure restricted to the radial half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L40).

**The cell rectangle is measurable** · theorem. `measurableSet_rect`: The closed radial-height rectangle associated with a cell box is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L44).

**Coordinate energy is measurable** · theorem. `aesm_cnormSq`: The squared-coordinate norm of a finite vector with almost-everywhere strongly measurable coordinates is almost-everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L47).

**Curl coordinates are measurable** · theorem. `aesm_curlOfGrad'`: A gradient array with almost-everywhere strongly measurable entries has almost-everywhere strongly measurable curl coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L52).

**Curl-gradient coordinates are measurable** · theorem. `aesm_curlSecond`: A second-derivative array with almost-everywhere strongly measurable entries has almost-everywhere strongly measurable curl-gradient coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L59).

**Measurable velocity modes on the plane** · theorem. `aesm_modeVel_plane`: An almost-everywhere strongly measurable space-time velocity field has measurable zero-time mode coordinates on the radial half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L66).

**Measurable gradient modes on the plane** · theorem. `aesm_modeGrad_plane`: An almost-everywhere strongly measurable space-time gradient field has measurable zero-time mode entries on the radial half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L75).

**Measurable Hessian modes on the plane** · theorem. `aesm_modeSecond_plane`: An almost-everywhere strongly measurable space-time Hessian field has measurable zero-time mode entries on the radial half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L88).

**Energy splits between packed slots** · theorem. `Breakdown.CertCell.AssemblyTrueRegularParts.sum_pairVec_sq`: The squared-norm sum of a packed matrix and vector equals the matrix entry energy plus the vector coordinate energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L103).

**Band energy in harmonic coordinates** · theorem. `bandSum_eq`: The packed band-profile energy equals the squared harmonic gradient norm plus the squared harmonic velocity norm at the corresponding plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L108).

**Measurable coordinates remain measurable** · theorem. `aesm_pairVec`: Packing almost-everywhere strongly measurable matrix entries and velocity coordinates gives almost-everywhere strongly measurable profile coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L116).

**A cell radius bounds velocity weight** · theorem. `profile_point_le`: The cell's outer-radius-and-height bound controls the radial-weighted sum of a and b by the a contribution plus the inverse-distance-weighted b contribution with the displayed geometric factor. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L125).

**Cell energy from global mode bounds** · theorem. `profile_bound`: The nonnegative cell profile integral is bounded by the full half-plane gradient integral plus the inverse-distance velocity integral multiplied by the cell's squared size bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L149).

**All label profiles have summable energy** · theorem. `profile_regular`: The field hypotheses give measurable coordinates and integrable radial-weighted energy for every label, and the series of those cell energies is summable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L184).

**Joint measurability of the mode density** · theorem. `measurable_modeDensity_joint`: The mode density is measurable jointly in the spatial and displayed real parameter variables under the density-data hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L236).

**Measurable label densities on the plane** · theorem. `aesm_labelDensity_half`: The admissible weak coefficients, measurable bound data and measurable velocity, gradient and Hessian fields make each label density almost-everywhere strongly measurable on the half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L246).

**Stretching along orbits is measurable** · theorem. `aesm_orbit_stretch`: The weak reference-field and measurable perturbation hypotheses make the stretching integrand almost-everywhere strongly measurable in plane point, time and angle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L288).

**Mean stretch is measurable on the region** · theorem. `aesm_meanStretch`: The mean-stretch density is almost-everywhere strongly measurable for volume restricted to the specified region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L300).

**Measurable restricted stretch integrand** · theorem. `aesm_stretch_integrand`: Restricting the measurable orbit stretching integrand to a region almost everywhere inside the half-plane and to the compact time-angle box preserves almost-everywhere strong measurability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L319).

**The curl vector is continuous** · theorem. `Breakdown.CertCell.AssemblyTrueRegularParts.continuous_curlVec`: The curl vector depends continuously on the underlying real linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L340).

**Measurability of the given-field modes** · theorem. `given_modes_measurable`: All labelled gradient, Hessian, velocity and vorticity coordinates of the given field are almost-everywhere strongly measurable on the region. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L344).

**Label and mean densities are measurable** · theorem. `density_measurable_on`: Every label density and the mean-stretch density are almost-everywhere strongly measurable on the specified region under the field and coefficient hypotheses. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L364).

**Intersection stays in the half-plane** · theorem. `inter_halfPlane_ae_le`: The intersection of any planar set with the radial half-plane is almost everywhere contained in that half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyTrueRegularParts.lean#L379).

### Breakdown.CertCell.AxisSideTrace

This file identifies a side trace at the axis as the limit of traces on positive-radius lines, under the axis-admissibility and regularity hypotheses. Appendix B.1–B.3: harmonic fields, traces and weak row identities.

**Source namespace `Breakdown.CertCell.SideTrace.Internal`.**

**Bound a real-linear complex combination** · theorem. `norm_real_mul_add_le`: The norm of a times x plus b times y is bounded by abs(a) times the norm of x plus abs(b) times the norm of y. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AxisSideTrace.lean#L17).

**Trace formula below the reference side** · theorem. `sideTrace_eq_below`: For an endpoint below the reference point, the side trace is the integral of the displayed affine combination of the function and its weak derivative over the intervening interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AxisSideTrace.lean#L23).

**Put a side trace on one fixed interval** · theorem. `sideTrace_eq_restrict`: The side trace equals an integral over the fixed interval from zero to b after inserting the indicator of the endpoint interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AxisSideTrace.lean#L28).

**The side trace has an axis limit** · theorem. `sideTrace_tendsto_axis`: Under the trace integrability and weak-derivative assumptions, the side trace converges to its zero-endpoint value as the endpoint tends to zero from above. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AxisSideTrace.lean#L34).

**Positive endpoints give the same trace** · theorem. `sideTrace_eq_of_pos`: The side-trace matching interface and weak derivatives on every positive interior interval make the trace independent of the chosen positive endpoint. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AxisSideTrace.lean#L118).

**Source namespace `Breakdown.CertCell.SideTrace`.**

**Trace matching extends to the axis** · theorem. `axisSideTrace`: Under the stated hypotheses, plain integrability of the function and radius-weighted integrability of its derivative extend side-trace matching to the zero-radius endpoint. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AxisSideTrace.lean#L128).

### Breakdown.CertCell.BridgeCreditStatements

This file packages the real velocity data used in a local credit patch and states the corresponding boundary credit estimate. Appendix B.1–B.3: harmonic fields, traces and weak row identities.

**Source namespace `Breakdown.CertCell.Bridge.CreditPatch`.**

**Vertical velocity data on patch segments** · definition. `Breakdown.CertCell.BridgeCreditStatements.data`: These data evaluate the vertical velocity's height-strip moment against each selected segment test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeCreditStatements.lean#L19).

**Source namespace `Breakdown.CertCell.Bridge`.**

**Credit patch bounded by mode energy** · interface proposition. `CreditPatchBoundHolds`: This interface requires that a valid credit patch bounds its finite credit form by the charged reflected velocity-mode energy on the patch whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeCreditStatements.lean#L24).

Proved by `Breakdown.CertCell.creditPatchBound_closed`, `Breakdown.CertCell.Bridge.creditPatchBound`.

### Breakdown.CertCell.BridgeStatements

This file states the analytic bridges from three-dimensional perturbations to harmonic half-plane, boundary, patch and coupling data. Appendix B.1–B.3: harmonic fields, traces and weak row identities.

**Source namespace `Breakdown.CertCell.Bridge`.**

**Reflection of the reference field** · structure. `IsFlipInvariantModel`: This predicate requires that the given field and Hessian transform equivariantly under the spatial reflection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L55).

**Arithmetic of lattice harmonic labels** · interface proposition. `LabelArithmeticHolds`: This interface requires that positive symmetry order makes the label map injective, compatible with reflection and negation, and equivalent to the divisibility and parity lattice condition whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L60).

Proved by `Breakdown.CertCell.Bridge.labelArithmetic`.

**Integrability of the velocity L6 norm** · interface proposition. `VelocitySixthIntegralHolds`: This interface requires that an admissible perturbation has finite time integral of the spatial sixth-power integral raised to the one-sixth power whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L66).

Proved by `Breakdown.CertCell.velocitySixthIntegral_closed`, `Breakdown.CertCell.Bridge.velocitySixthIntegral`.

**Shift and rotate a velocity harmonic** · interface proposition. `ModeShiftRotateHolds`: This interface requires that a periodic integrable velocity harmonic gains the specified phase and rotated vector components under time shift and axial rotation whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L72).

Proved by `Breakdown.CertCell.Bridge.modeShiftRotate`.

**Shift and rotate derivative harmonics** · interface proposition. `ModeShiftRotateTensorHolds`: This interface requires that periodic integrable gradient and Hessian harmonics gain the corresponding phase and tensor rotation under time and angle shifts whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L80).

Proved by `Breakdown.CertCell.Bridge.modeShiftRotateTensor`.

**Negated harmonics are conjugates** · interface proposition. `ModeConjugateHolds`: This interface requires that the velocity, gradient and Hessian coefficient at the negative frequency is the conjugate of the original coefficient whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L97).

Proved by `Breakdown.CertCell.Bridge.modeConjugate`.

**Reflect velocity and derivative modes** · interface proposition. `ModeFlipHolds`: This interface requires that a reflection-symmetric perturbation's velocity and derivative harmonics transform with the appropriate product of frame signs almost everywhere whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L103).

Proved by `Breakdown.CertCell.Bridge.modeFlip`.

**A nontrivial symmetry phase kills a mode** · interface proposition. `ModeOffLatticeHolds`: This interface requires that a harmonic coefficient vanishes almost everywhere when the perturbation symmetry would multiply it by a phase different from one whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L115).

Proved by `Breakdown.CertCell.Bridge.modeOffLattice`.

**Harmonics stay in the symmetry lattice** · interface proposition. `ClassSupportHolds`: This interface requires that a perturbation in the chosen symmetry class has zero velocity and derivative coefficients outside its harmonic lattice whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L123).

Proved by `Breakdown.CertCell.Bridge.classSupport_of_parts`, `Breakdown.CertCell.Bridge.classSupport`.

**Harmonics stay in the symmetry lattice** · theorem. `classSupport_of_parts`: Under the stated hypotheses, a perturbation in the chosen symmetry class has zero velocity and derivative coefficients outside its harmonic lattice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L129).

**Reduce the mode integral to half-plane** · interface proposition. `HalfPlaneReductionHolds`: This interface requires that rotation and reflection compatibility reduce the three-dimensional nonnegative mode integral to 4π times its radius-weighted half-plane integral whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L169).

Proved by `Breakdown.CertCell.Bridge.halfPlaneReduction`.

**Spatial integral equals rotation average** · interface proposition. `RotationAverageHolds`: This interface requires that integrating a measurable nonnegative function over space agrees with integrating its normalized axial rotation average whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L175).

Proved by `Breakdown.CertCell.Bridge.rotationAverage`.

**Squared Hessian Frobenius norm** · definition. `hessFrobSq`: This value sums the squared norms of the Hessian evaluated on every ordered coordinate-basis pair. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L179).

**Hessian energy equals Laplacian energy** · interface proposition. `HessianEnergyIdentityHolds`: This interface requires that the period integral of the squared Hessian Frobenius norm equals the squared Hessian-trace integral for an admissible perturbation whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L182).

Proved by `Breakdown.CertCell.Bridge.secondDerivEnergyIdentity`.

**Read physical density through cell modes** · interface proposition. `ModeDensityBridgeHolds`: This interface requires that the admissible symmetric model converts the positive and negative physical density integrals into 4π times the corresponding half-plane forms whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L188).

Proved by `Breakdown.CertCell.modeDensityBridge_closed`, `Breakdown.CertCell.Bridge.modeDensityBridge`.

**Reflection preserves each mode term** · interface proposition. `ModeTermFlipHolds`: This interface requires that compatible bound data and reflected mode coefficients preserve the scalar mode term away from the equatorial plane whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L202).

Proved by `Breakdown.CertCell.Bridge.modeTermFlip`.

**Reflection preserves stretching** · interface proposition. `StretchFlipHolds`: This interface requires that the reflected perturbation and reference-field identities preserve the physical stretching form whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L214).

Proved by `Breakdown.CertCell.Bridge.stretchFlip`.

**Ordered stretching interaction** · definition. `stretchBilin`: This bilinear expression combines strain-curl, velocity-curl-gradient and gradient-velocity terms with the exact alternating-symbol contractions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L221).

**Symmetrized stretching interaction** · definition. `stretchTriple`: This expression averages the ordered stretching interaction over the two velocity-gradient arguments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L228).

**Mean stretching as a harmonic sum** · interface proposition. `MeanStretchModeSumHolds`: This interface requires that the mean stretching equals the real absolutely summable interaction of perturbation modes with the finitely supported given-field harmonics almost everywhere whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L232).

Proved by `Breakdown.CertCell.Bridge.meanStretchModeSum`.

**Integrate mean stretching on half-plane** · interface proposition. `StretchMeanIntegralHolds`: This interface requires that the full period-space stretching integral equals 4π times the radius-weighted mean-stretching integral on the half-plane whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L247).

Proved by `Breakdown.CertCell.Bridge.stretchMeanIntegral`.

**Bound one stretching interaction** · interface proposition. `StretchTripleBoundHolds`: This interface requires that strain and curl-gradient operator bounds control the symmetrized stretching interaction by curl-curl and velocity-gradient norm products whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L261).

Proved by `Breakdown.CertCell.Bridge.stretchTripleBound`.

**Bound interacting harmonic waves** · interface proposition. `CrossWaveBoundHolds`: This interface requires that the harmonic cross interaction is bounded by own and partner cross charges with reciprocal balancing factors whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L270).

Proved by `Breakdown.CertCell.Bridge.crossWaveBound`.

**Trace recovered from above** · definition. `upperTrace`: This integral reconstructs the height-zero trace from values and a weak height derivative on a positive strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L283).

**Trace recovered from below** · definition. `lowerTrace`: This integral reconstructs the height-zero trace from values and a weak height derivative on a negative strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L286).

**Weak derivative on an interval** · proposition definition. `HasWeakDerivOn`: This predicate requires that the function and derivative are integrable and obey integration by parts against every smooth compact test inside the interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L289).

**Reflect an upper trace to a lower trace** · interface proposition. `TraceFlipHolds`: This interface requires that reflection of the function and the signed derivative takes the upper trace to the corresponding multiple of the lower trace whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L294).

Proved by `Breakdown.CertCell.Bridge.traceFlip`.

**Upper and lower traces agree** · interface proposition. `TraceMatchHolds`: This interface requires that a weak derivative through a neighborhood of zero makes the upper and lower reconstructed traces equal whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L298).

Proved by `Breakdown.CertCell.Bridge.traceMatch`.

**The trace is independent of strip height** · interface proposition. `TraceHeightHolds`: This interface requires that nested positive strips through a common weak-derivative neighborhood give the same reconstructed upper trace whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L302).

Proved by `Breakdown.CertCell.Bridge.traceHeight`.

**Velocity harmonic along a vertical line** · definition. `planeVel`: This function restricts one harmonic velocity component to a fixed-radius vertical line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L306).

**Height derivative of a velocity mode** · definition. `planeVelHeight`: This function reads the vertical gradient component of a velocity harmonic on a fixed-radius line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L309).

**Second height derivative of a mode** · definition. `planeVelHeight2`: This function reads the twice-vertical second-derivative coefficient on a fixed-radius line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L312).

**Scalar harmonic on a vertical line** · definition. `planeScalar`: This function takes the scalar harmonic coefficient at points on a fixed-radius vertical line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L316).

**Height coefficient of a scalar gradient** · definition. `planeScalarHeight`: This function takes the harmonic coefficient of the scalar gradient's vertical component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L319).

**Read a strip moment as a trace integral** · interface proposition. `StripMomentTraceHolds`: This interface requires that the weak height-strip moment equals the weighted radial integral of the upper trace when the fields and tests are integrable whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L322).

Proved by `Breakdown.CertCell.Bridge.stripMomentTrace`.

**Weak radial and height derivatives** · proposition definition. `HasWeakPlaneDerivsOn`: This predicate requires that the four integrable plane functions obey radial, height and mixed integration-by-parts identities on the rectangle interior. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L330).

**Reflect a corner moment** · interface proposition. `CornerFlipHolds`: This interface requires that height reflection and its derivative signs transform the corner moment by the prescribed scalar factor whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L338).

Proved by `Breakdown.CertCell.Bridge.cornerFlip`.

**Corner moments agree across the plane** · interface proposition. `CornerMatchHolds`: This interface requires that weak plane derivatives across the equatorial plane identify the corner moments from its two sides whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L344).

Proved by `Breakdown.CertCell.Bridge.cornerMatch`.

**Corner moment from upper traces** · interface proposition. `CornerTraceHolds`: This interface requires that an integrable corner moment equals a radial integral of the upper traces of the function and its radial derivative whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L349).

Proved by `Breakdown.CertCell.Bridge.cornerTrace`.

**Weak height derivatives of modes** · interface proposition. `ModeHeightDerivHolds`: This interface requires that velocity and gradient harmonic coefficients have the prescribed weak height derivatives on almost every positive-radius line whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L360).

Proved by `Breakdown.CertCell.modeHeightDeriv_closed`, `Breakdown.CertCell.Bridge.modeHeightDeriv`.

**Reflect the plane trace data** · interface proposition. `PlaneDataFlipHolds`: This interface requires that the velocity trace and its height derivative acquire their respective reflection signs when the harmonic label is flipped whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L370).

Proved by `Breakdown.CertCell.planeDataFlip_closed`, `Breakdown.CertCell.Bridge.planeDataFlip`.

**Radial coefficient of a velocity mode** · definition. `planeVelRadial`: This function reads the radial gradient coefficient of a velocity mode on the half-plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L380).

**Mixed radial-height coefficient** · definition. `planeVelMixed`: This function reads the radial-height second-derivative coefficient of a velocity mode. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L383).

**Reflect off-axis strip data** · interface proposition. `StripDataFlipHolds`: This interface requires that the velocity and height-derivative strip moments obey the frame-sign reflection law on strictly positive radial strips whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L386).

Proved by `Breakdown.CertCell.stripDataFlip_closed`, `Breakdown.CertCell.Bridge.stripDataFlip`.

**Reflect off-axis corner data** · interface proposition. `CornerDataFlipHolds`: This interface requires that the corner moment on a strictly positive-radius rectangle obeys the velocity component's reflection sign whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L401).

Proved by `Breakdown.CertCell.cornerDataFlip_closed`, `Breakdown.CertCell.Bridge.cornerDataFlip`.

**Reflect a scalar plane trace** · interface proposition. `ScalarPlaneFlipHolds`: This interface requires that a reflection-even scalar with the specified weak gradient has matching reflected harmonic traces on the equatorial plane whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L412).

Proved by `Breakdown.CertCell.scalarPlaneFlip_closed`, `Breakdown.CertCell.Bridge.scalarPlaneFlip`.

**Weak height derivative of scalar modes** · interface proposition. `ScalarHeightDerivHolds`: This interface requires that the scalar's harmonic coefficient has the stated vertical-gradient coefficient as its weak height derivative whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L423).

Proved by `Breakdown.CertCell.Bridge.scalarHeightDeriv`.

**Reflect scalar strip data** · interface proposition. `StripScalarFlipHolds`: This interface requires that the reflected scalar harmonic strip moments agree under the stated weak-gradient, parity and integrability conditions whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L433).

A named provider for this exact interface was not identified in the source.

**Reality relations for plane data** · interface proposition. `PlaneDataRealityHolds`: This interface requires that the harmonic plane data obey the conjugation and reflection relations required to represent the real physical fields whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L447).

Proved by `Breakdown.CertCell.Bridge.planeDataReality_of_parts`.

**Reality relations for plane data** · theorem. `planeDataReality_of_parts`: Under the stated hypotheses, the harmonic plane data obey the conjugation and reflection relations required to represent the real physical fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L457).

**Velocity trace tested on a patch** · definition. `patchTrace`: This integral pairs the vertical velocity's upper trace with the patch test and cylindrical radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L497).

**Trace test controlled by patch energy** · interface proposition. `PatchTraceBoundHolds`: This interface requires that the squared patch trace pairing is bounded by the charged mode energy times the test-gradient factor whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L501).

Proved by `Breakdown.CertCell.Bridge.patchTraceBound`.

**Finite patch credit from trace bounds** · interface proposition. `PatchCreditHolds`: This interface requires that the positive trace-test and factorization conditions bound the finite credit form by the charged velocity-mode integral whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L512).

Proved by `Breakdown.CertCell.Bridge.patchCredit`.

**Physical pairing as a mode integral** · interface proposition. `PairingModeIdentityHolds`: This interface requires that the physical pairing equals its normalized sum of radius-weighted harmonic pairings on the half-plane whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L527).

Proved by `Breakdown.CertCell.Bridge.pairingModeIdentity`.

**Pin pairing on the half-plane** · interface proposition. `PinHalfPlaneHolds`: This interface requires that the physical pin pairing is 4π times the sum of real harmonic gradient pairings on the half-plane whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L537).

Proved by `Breakdown.CertCell.Bridge.pinHalfPlane`.

**Velocity moment on a plane segment** · definition. `velocityData`: This value is the height-strip moment of one velocity harmonic against the segment's chosen test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L548).

**Finite patch-credit data** · structure. `PatchEntry`: This record supplies a radial-height patch, test functions, segment traces, factor matrices, slack and the proposed finite credit matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L553).

**Source namespace `Breakdown.CertCell.Bridge.PatchEntry`.**

**Vertical velocity data on patch segments** · definition. `Breakdown.CertCell.BridgeStatements.data`: These data evaluate the vertical velocity's height-strip moment against each selected segment test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L579).

**Complex combination of patch tests** · definition. `testCombination`: This function combines the real patch tests with the conjugates of the supplied complex coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L582).

**Source namespace `Breakdown.CertCell.Bridge`.**

**Geometry and bounds of a credit patch** · structure. `IsPatchEntry`: This predicate requires that the patch geometry, test regularity, boundary vanishing, trace identities and matrix factor-slack inequalities hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L587).

**A valid patch supplies its credit bound** · interface proposition. `PatchEntryCreditHolds`: This interface requires that the patch's finite credit form is bounded by the charged reflected velocity-mode energy for an admissible symmetric perturbation whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L615).

Proved by `Breakdown.CertCell.Bridge.patchEntryCredit`.

**Grouped source and port data** · structure. `SourceEntry`: This record supplies positive-share candidates and the port matrices for a finite family of source groups. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L623).

**Positive shares with canceling ports** · structure. `IsSourceEntry`: This predicate requires that all source shares are positive, their sum is at most one and the port matrices sum to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L630).

**Data for paired plane cancellation** · structure. `ClosedPlaneEntry`: This record supplies a pairing involution candidate, coordinate signs and the matrices assigned to paired planes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L635).

**Paired closed-plane cancellation** · structure. `IsClosedPlaneEntry`: This predicate requires that the partner map is involutive, every sign has square one and paired weights cancel after conjugation by the sign diagonal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L642).

**Data for all coupling bounds** · structure. `CouplingEntry`: This record collects patch, source, cross-wave and closed-plane entries together with the pin weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L647).

**Validity of all coupling entries** · structure. `IsCouplingEntry`: This predicate requires that the symmetry, model bounds, harmonic data, patches, sources, cross-wave data, closed planes and positive pin weight are mutually compatible. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L657).

**Coupling data supply analytic bounds** · interface proposition. `CouplingEntryHolds`: This interface requires that a valid coupling entry supplies the physical-to-half-plane density identities and the specified patch, source, pin and cross-wave bounds whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L670).

Proved by `Breakdown.CertCell.Bridge.couplingEntry_of_parts`.

**Coupling data supply analytic bounds** · theorem. `couplingEntry_of_parts`: Under the stated hypotheses, a valid coupling entry supplies the physical-to-half-plane density identities and the specified patch, source, pin and cross-wave bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeStatements.lean#L692).

### Breakdown.CertCell.BridgeTraceStatements

This file states the trace and pressure-potential interfaces, including the extra integrability and parity requirements at the axis. Appendix B.1–B.3: harmonic fields, traces and weak row identities.

**Test compatibility at the axis** · proposition definition. `IsAxisAdmissibleTest`: This predicate requires that the radial interval starts positively, or starts at zero with a test equal to radius times a continuous function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L17).

**Trace from a value and derivative** · definition. `sideTrace`: This weighted integral reconstructs the value at the chosen side from the function and its derivative on the adjoining interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L20).

**Side traces ignore interval choices** · interface proposition. `SideTraceMatchHolds`: This interface requires that a common weak derivative identifies reconstructed traces at one fixed side despite changing the opposite endpoint whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L24).

Proved by `Breakdown.CertCell.SideTrace.sideTraceMatch`.

**Trace matching extends to the axis** · interface proposition. `AxisSideTraceHolds`: This interface requires that plain integrability of the function and radius-weighted integrability of its derivative extend side-trace matching to the zero-radius endpoint whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L28).

Proved by `Breakdown.CertCell.SideTrace.axisSideTrace`.

**Radial strip moment as side traces** · interface proposition. `RadialStripTraceHolds`: This interface requires that the radial strip moment is the height integral of the weighted side trace under the stated integrability conditions whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L34).

Proved by `Breakdown.CertCell.SideTrace.radialStripTrace`.

**Height strip moment as side traces** · interface proposition. `HeightStripTraceHolds`: This interface requires that the height strip moment is the radial integral of the weighted side trace under the stated integrability conditions whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L42).

Proved by `Breakdown.CertCell.SideTrace.heightStripTrace`.

**Corner data ignore opposite endpoints** · interface proposition. `CornerPointTraceHolds`: This interface requires that weak plane derivatives identify corner moments at a fixed corner when the two opposite endpoints change whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L51).

Proved by `Breakdown.CertCell.SideTrace.cornerPointTrace`.

**Corner matching includes the axis** · interface proposition. `CornerAxisTraceHolds`: This interface requires that the weighted radial-derivative and plain function integrability conditions extend the fixed-corner identity to a zero-radius endpoint whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L59).

Proved by `Breakdown.CertCell.SideTrace.cornerAxisTrace`.

**Gradient coefficient on the half-plane** · definition. `planeGrad`: This function restricts one harmonic gradient entry to points of the radial-height plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L70).

**Second derivative on the half-plane** · definition. `planeSlope`: This function restricts the second-derivative harmonic with the source's ordered indices to the radial-height plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L73).

**Velocity coefficient on the half-plane** · definition. `planeVelocity`: This function restricts one harmonic velocity component to the radial-height plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L76).

**Weak radial derivatives of modes** · interface proposition. `ModeRadialDerivHolds`: This interface requires that velocity and gradient harmonics have the prescribed weak radial derivatives on almost every height line away from the axis whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L79).

Proved by `Breakdown.CertCell.SideTrace.modeRadialDeriv`.

**Weak derivatives on off-axis rectangles** · interface proposition. `ModePlaneDerivsHolds`: This interface requires that the harmonic velocity, gradient and Hessian entries supply the weak plane derivative and integrability identities on positive-radius rectangles whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L87).

Proved by `Breakdown.CertCell.SideTrace.modePlaneDerivs`.

**Weighted integrability at the axis** · interface proposition. `ModeAxisIntegrableHolds`: This interface requires that radius times each velocity, gradient and Hessian harmonic entry is integrable on rectangles reaching the axis whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L96).

Proved by `Breakdown.CertCell.SideTrace.modeAxisIntegrable`.

**Plain integrability of axis modes** · interface proposition. `ModeAxisPlainIntegrableHolds`: This interface requires that velocity and gradient harmonic entries are integrable without a radius weight on rectangles reaching the axis whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L104).

Proved by `Breakdown.CertCell.SideTrace.modeAxisPlainIntegrable`.

**Match radial data across cell choices** · interface proposition. `RadialDataMatchHolds`: This interface requires that radial velocity and derivative moments agree when the opposite radial endpoint changes, including an endpoint on the axis whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L111).

Proved by `Breakdown.CertCell.SideTrace.radialDataMatch_of_parts`.

**Match height data across cell choices** · interface proposition. `HeightDataMatchHolds`: This interface requires that height moments agree when the opposite height endpoint changes, with the axis-admissible test condition for derivative moments whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L121).

Proved by `Breakdown.CertCell.SideTrace.heightDataMatch_of_parts`.

**Match corner data across cell choices** · interface proposition. `CornerDataMatchHolds`: This interface requires that corner moments of the same physical harmonic agree despite changing the opposite cell endpoints whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L132).

Proved by `Breakdown.CertCell.SideTrace.cornerDataMatch_of_parts`.

**Match radial data across cell choices** · theorem. `radialDataMatch_of_parts`: Under the stated hypotheses, radial velocity and derivative moments agree when the opposite radial endpoint changes, including an endpoint on the axis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L141).

**Match height data across cell choices** · theorem. `heightDataMatch_of_parts`: Under the stated hypotheses, height moments agree when the opposite height endpoint changes, with the axis-admissible test condition for derivative moments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L234).

**Match corner data across cell choices** · theorem. `cornerDataMatch_of_parts`: Under the stated hypotheses, corner moments of the same physical harmonic agree despite changing the opposite cell endpoints. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L292).

**Local square integrability of a field** · proposition definition. `IsSquareIntegrableNear`: This predicate requires that the field is measurable and its squared norm has finite integral on every spatial closed ball. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L343).

**Weak derivatives of pressure modes** · interface proposition. `PressureModeDerivHolds`: This interface requires that a locally square-integrable gradient field gives the radial and height weak derivatives of the associated pressure harmonic whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L346).

Proved by `Breakdown.CertCell.SideTrace.pressureModeDeriv`.

**Integrability of pressure coefficients** · interface proposition. `PressureModeIntegrableHolds`: This interface requires that pressure modes are integrable up to the axis, their gradient modes are radius-weighted integrable there and plain integrable away from it whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L353).

Proved by `Breakdown.CertCell.SideTrace.pressureModeIntegrable`.

**Reflection of pressure harmonics** · interface proposition. `PressurePlaneFlipHolds`: This interface requires that a reflected gradient field gives the same pressure mode after changing the azimuthal sign and reflecting height almost everywhere whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L361).

Proved by `Breakdown.CertCell.SideTrace.pressurePlaneFlip`.

**Reflection of pressure strip moments** · interface proposition. `PressureStripFlipHolds`: This interface requires that the pressure strip moments agree under azimuthal sign reversal for axis-admissible tests and a reflected gradient field whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L366).

Proved by `Breakdown.CertCell.SideTrace.pressureStripFlip_of_parts`, `Breakdown.CertCell.SideTrace.pressureStripFlip`.

**Match pressure side moments** · interface proposition. `PressureDataMatchHolds`: This interface requires that the pressure harmonic's radial and height side moments are independent of the opposite endpoints under the stated axis conditions whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L374).

Proved by `Breakdown.CertCell.SideTrace.pressureDataMatch_of_parts`.

**Two potentials differ by a constant** · interface proposition. `PotentialConstantHolds`: This interface requires that two potentials for the same field differ by one real constant almost everywhere whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L384).

Proved by `Breakdown.CertCell.SideTrace.potentialConstant`.

**Negate a field and its potential** · interface proposition. `PotentialNegationHolds`: This interface requires that negating a potential gives a potential for the negated gradient field whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L387).

Proved by `Breakdown.CertCell.SideTrace.potentialNegation`.

**Subtract a constant from a potential** · interface proposition. `PotentialShiftHolds`: This interface requires that subtracting a real constant preserves the field represented by a potential whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L390).

Proved by `Breakdown.CertCell.SideTrace.potentialShift`.

**The chosen potential represents a field** · interface proposition. `PotentialOfGradientHolds`: This interface requires that the selected potential of a gradient field has that field as its weak gradient whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L393).

Proved by `Breakdown.CertCell.SideTrace.potentialOfGradient`.

**Local square bounds for pressure modes** · interface proposition. `HarmonicPressureSquareHolds`: This interface requires that the cosine and sine coefficients of a periodic pressure gradient are locally square-integrable whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L396).

Proved by `Breakdown.CertCell.SideTrace.harmonicPressureSquare`.

**Reflection of real pressure harmonics** · interface proposition. `HarmonicPressureFlipHolds`: This interface requires that cosine and sine coefficients of a reflected periodic pressure gradient inherit its reflection identity almost everywhere whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L400).

Proved by `Breakdown.CertCell.SideTrace.harmonicPressureFlip`.

**Reflect strip data including the axis** · interface proposition. `StripDataFlipAxisHolds`: This interface requires that velocity strip data obey the reflection law up to the axis, with the extra axis test condition for derivative data whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L406).

Proved by `Breakdown.CertCell.SideTrace.stripDataFlipAxis`.

**Reflect corner data including the axis** · interface proposition. `CornerDataFlipAxisHolds`: This interface requires that corner velocity data obey the reflection law when the opposite radial endpoint may lie on the axis whenever its displayed analytic and compatibility premises hold. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L418).

Proved by `Breakdown.CertCell.SideTrace.cornerDataFlipAxis`.

**Inputs for radial trace matching** · structure. `RadialTraceParts`: This predicate requires that side, axis, radial-strip, height-strip and weak-radial-derivative interfaces hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L428).

**Inputs for corner trace matching** · structure. `CornerPointTraceParts`: This predicate requires that fixed-corner, axis-corner and weak-plane-derivative interfaces hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L435).

**Inputs for pressure-potential traces** · structure. `PressurePotentialTraceParts`: This predicate requires that pressure derivatives, integrability, reflection, potential transformations and real harmonic properties hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L440).

**Inputs for reflection at the axis** · structure. `AxisPlaneFlipParts`: This predicate requires that the strip and corner reflection interfaces including the axis hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L451).

**Inputs for strip integrability** · structure. `StripIntegrabilityParts`: This predicate requires that the weak plane derivatives and weighted and unweighted axis-integrability interfaces hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L455).

**Reflection of pressure strip moments** · theorem. `pressureStripFlip_of_parts`: Under the stated hypotheses, the pressure strip moments agree under azimuthal sign reversal for axis-admissible tests and a reflected gradient field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L460).

**Match pressure side moments** · theorem. `pressureDataMatch_of_parts`: Under the stated hypotheses, the pressure harmonic's radial and height side moments are independent of the opposite endpoints under the stated axis conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/BridgeTraceStatements.lean#L615).

### Breakdown.CertCell.CellCalculusStatements

This file states how harmonic fields supply cell coefficients, row moments, gauge data and residual forms in the finite cell calculus. Appendix B.3: cell forms, harmonic estimates and tree assembly.

**Source namespace `Breakdown.CertCell.CellCalculus`.**

**Lattice label for time and angle** · definition. `harmonicMode`: This label is (n,(n+ν)/2), so recovering the intended frequencies requires the separate parity hypothesis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L24).

**Real cosine time coefficient** · definition. `harmonicCos`: This coefficient integrates the field against cos(2πνt) over one time period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L26).

**Negative sine time coefficient** · definition. `harmonicSin`: This coefficient is minus the integral against sin(2πνt), matching the complex Fourier convention. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L30).

**Convert frequencies to a lattice label** · interface proposition. `HarmonicModeStatement`: This predicate requires that the parity condition makes the chosen label recover the requested time frequency and azimuthal multiple. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L34).

A named provider for this exact interface was not identified in the source.

**Ordered harmonic Hessian entry** · definition. `slopeAt`: This value reads the harmonic Hessian with the index order (a,c,b). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L39).

**Radius-scaled angular derivative** · definition. `turnedSlopeAt`: This value multiplies the angular Hessian coefficient by the cylindrical radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L43).

**Matrix of harmonic gradient entries** · definition. `gradArray`: This array organizes the harmonic gradient values as a three-by-three matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L47).

**Vector of harmonic velocity entries** · definition. `velArray`: This vector organizes the three harmonic velocity values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L51).

**Squared harmonic Hessian entries** · definition. `slopeSq`: This value sums squared norms over all three indices of the harmonic Hessian entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L54).

**Squared harmonic curl-gradient entries** · definition. `curlSlopeSq`: This value sums the squared curl components of each second-derivative slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L57).

**Periodic fields with weak derivatives** · structure. `IsPeriodicSecondOrder`: This predicate requires that velocity, gradient and Hessian are measurable and periodic, represent the weak derivatives and satisfy the required finite energy conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L60).

**Periodic pressure-gradient data** · structure. `IsPeriodicPressure`: This predicate requires that the field is measurable and periodic with finite local square norm and gradient-valued cosine and sine coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L76).

**Lift complex modes from real harmonics** · interface proposition. `HarmonicLiftStatement`: This predicate requires that the real cosine and negative-sine fields are local second-order fields whose coefficients reconstruct the complex velocity and derivative modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L83).

Proved by `Breakdown.CertCell.CellCalculus.harmonicLift_holds`.

**Lift pressure modes from real harmonics** · interface proposition. `HarmonicPressureLiftStatement`: This predicate requires that the complex pressure-gradient coefficient is the cosine coefficient plus i times the negative-sine coefficient almost everywhere at positive radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L97).

Proved by `Breakdown.CertCell.CellCalculus.harmonicPressureLift_holds`.

**Cosine field tuple** · definition. `cosTuple`: This tuple contains the cosine coefficients of velocity, gradient, Hessian and pressure gradient, with zero auxiliary forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L103).

**Sine field tuple** · definition. `sinTuple`: This tuple contains the negative-sine coefficients of velocity, gradient, Hessian and pressure gradient, with zero auxiliary forcing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L107).

**Complex cell data from real lifts** · definition. `harmonicData`: These cell data add the cosine tuple's real data to i times the negative-sine tuple's data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L111).

**Cell data at a label's time frequency** · definition. `modeData`: These data evaluate the harmonic-data construction at the time frequency belonging to the cell label. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L115).

**Harmonic data obey cell relations** · theorem. `harmonicRelations_of`: Under the stated hypotheses, the physical harmonic cell data satisfy the cell layout's defining linear relations. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L126).

**Harmonic data recover side moments** · interface proposition. `HarmonicSideDataStatement`: This predicate requires that the cell side-data coordinates equal the corresponding weak harmonic strip moments for compatible periodic fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L139).

Proved by `Breakdown.CertCell.CellCalculus.harmonicSideData_holds`.

**The cell parametrization fixes true data** · interface proposition. `HarmonicParamStatement`: This predicate requires that a valid relation-based cell parametrization leaves the physical harmonic cell data unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L156).

Proved by `Breakdown.CertCell.CellCalculus.harmonicParam_of`.

**The cell parametrization fixes true data** · theorem. `harmonicParam_of`: Under the stated hypotheses, a valid relation-based cell parametrization leaves the physical harmonic cell data unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L164).

**Retained gradient derivative energy** · definition. `labelStrainEnergy`: This sum combines radial, height and angular energies of all harmonic gradient entries. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L172).

**Retained curl derivative energy** · definition. `labelVorticityEnergy`: This sum combines radial, height and angular energies of the harmonic curl components. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L179).

**Gradient derivative tail energy** · definition. `labelStrainTail`: This sum combines gradient projection-tail energy with the weighted angular tail of each gradient component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L188).

**Curl derivative tail energy** · definition. `labelVorticityTail`: This sum combines gradient projection-tail energy with the weighted angular tail of each curl component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L194).

**Weak derivative facts for a label** · interface proposition. `LabelModeFactsStatement`: This predicate requires that linear combinations of gradient-mode entries have the weighted integrability and integration-by-parts properties required by the cell energy argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L202).

Proved by `Breakdown.CertCell.CellCalculus.labelModeFacts_of`, `Breakdown.CertCell.CellCalculus.labelModeFacts_holds`.

**Resolved and tail energy fit below norm** · interface proposition. `LabelResolvedEnergyStatement`: This predicate requires that the retained gradient and curl energies plus their tails are bounded by the integrated Hessian and curl-Hessian squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L219).

Proved by `Breakdown.CertCell.CellCalculus.labelResolvedEnergy_of`, `Breakdown.CertCell.CellCalculus.labelResolvedEnergy_holds`.

**Weak derivative facts for a label** · theorem. `labelModeFacts_of`: Under the stated hypotheses, linear combinations of gradient-mode entries have the weighted integrability and integration-by-parts properties required by the cell energy argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L229).

**Resolved and tail energy fit below norm** · theorem. `labelResolvedEnergy_of`: Under the stated hypotheses, the retained gradient and curl energies plus their tails are bounded by the integrated Hessian and curl-Hessian squared norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L483).

**Coordinate norms agree with mode norms** · interface proposition. `LeafNormsStatement`: This predicate requires that the velocity, gradient, curl, Hessian and curl-gradient norms agree in the packed and indexed coordinate representations at positive radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L586).

Proved by `Breakdown.CertCell.CellCalculus.leafNorms_holds`.

**Leaf form lies below the mode density** · interface proposition. `LeafDensityLowerStatement`: This predicate requires that the Hessian floors, local matrix form and box penalty are bounded by the full coefficient density for every coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L601).

Proved by `Breakdown.CertCell.CellCalculus.leafDensityLower_holds`.

**Nonnegative pointwise leaf remainder** · interface proposition. `LeafPointwiseStatement`: This predicate requires that the coefficient-pair value minus the box and stretching penalties, with the chosen absorption, is nonnegative at each non-axis cell point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L609).

A named provider for this exact interface was not identified in the source.

**Expand physical stretching in components** · interface proposition. `ModelStretchSplitStatement`: This predicate requires that the physical stretching form equals its strain-curl, curl-gradient-velocity and alternating-symbol component terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L618).

A named provider for this exact interface was not identified in the source.

**Conjugate three-vector pairing** · definition. `cdot3`: This complex pairing sums each component of the first vector times the conjugate of the second. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L627).

**Radius-weighted row-test pairing** · definition. `rowPairing`: This integral pairs a vector field with the polynomial row test using cylindrical radius weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L629).

**Interior and boundary row fields** · structure. `RowProfile`: This record stores velocity, gradient, Laplacian and pressure-gradient fields together with their radial and height boundary traces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L632).

**Radius of a cell side** · definition. `sideRadius`: This value selects the inner radius for side zero and the outer radius for side one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L642).

**Height of a cell side** · definition. `sideHeight`: This value selects the lower height for side zero and the upper height for side one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L644).

**Outward sign of a cell side** · definition. `sideSign`: This sign is minus one on the lower-index side and plus one on the upper-index side. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L646).

**Boundary term for the gradient** · definition. `rowBoundaryGrad`: This expression sums the signed radial and height boundary pairings of the row profile's derivative traces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L648).

**Boundary term for pressure** · definition. `rowBoundaryPres`: This expression sums the signed pressure traces against the radial and vertical components of the polynomial test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L653).

**Interior linear row expression** · definition. `rowVolume`: This integral combines the gradient test pairing, time frequency, similarity drift and velocity terms in the cell interior. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L659).

**Weak identities for a row profile** · structure. `IsRowProfile`: This predicate requires that the row fields and boundary traces are measurable and integrable and satisfy the weak gradient and pressure integration-by-parts identities. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L665).

**The weak cell row formula** · interface proposition. `CellRowFormulaStatement`: This predicate requires that the tested right side equals the interior row expression minus the gradient boundary term plus pressure, coupling and drive pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L677).

Proved by `Breakdown.CertCell.CellCalculus.cellRowFormula_holds`.

**The real three-dimensional cross product** · definition. `crossVec`: This vector is the real cross product of its two inputs, written as an alternating-tensor sum in the coordinate basis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L689).

**Physical curl-velocity coupling** · definition. `couplingField`: This field is curl(v) crossed with the given field plus its vorticity crossed with v. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L692).

**Construct a row profile from a mode** · interface proposition. `LabelRowProfileStatement`: This predicate requires that each admissible harmonic has a valid row profile agreeing almost everywhere with its physical velocity, gradient, Laplacian and pressure-gradient coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L696).

Proved by `Breakdown.CertCell.CellCalculus.labelRowProfile_holds`.

**Read the low linear row from cell data** · interface proposition. `RowLowPartStatement`: This predicate requires that the interior and boundary linear row terms equal the finite own-row vector applied to the harmonic cell data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L705).

Proved by `Breakdown.CertCell.CellCalculus.rowLowPart_holds`, `Breakdown.CertCell.CellCalculus.rowLowPart_of_parts`.

**Coupling using retained projections** · definition. `lowCoupling`: This expression substitutes the retained polynomial projections of the perturbation gradient and velocity into the coupling with one model harmonic. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L722).

**Read low coupling from cell data** · interface proposition. `RowCouplingLowStatement`: This predicate requires that the row pairing of the retained projected coupling equals the finite coupling-row vector applied to the harmonic data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L727).

Proved by `Breakdown.CertCell.CellCalculus.rowCouplingLow_holds`.

**Gauge pressure on a side** · definition. `pressureSideValue`: This value evaluates the piecewise constant pressure gauge on a side moment, including the inner-radius correction for horizontal sides. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L743).

**Pressure-gauge cell coordinates** · definition. `classGaugeVector`: This cell vector is zero except in the pressure-side coordinates, where it stores the prescribed two-region pressure gauge. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L750).

**The linear row ignores pressure gauges** · interface proposition. `CellGaugeRowStatement`: This predicate requires that the permitted piecewise constant pressure-gauge vector pairs to zero with every admissible own-row test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L755).

A named provider for this exact interface was not identified in the source.

**Coupling rows ignore pressure gauges** · interface proposition. `CellGaugeCouplingStatement`: This predicate requires that the coupling-row vector pairs to zero with the piecewise constant pressure-gauge vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L762).

A named provider for this exact interface was not identified in the source.

**Rows ignore corner-stream gauges** · interface proposition. `StreamGaugeStatement`: This predicate requires that both own-row and coupling-row vectors vanish on each corner-stream coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L766).

Proved by `Breakdown.CertCell.CellCalculus.streamGauge`.

**Rows ignore corner-stream gauges** · theorem. `streamGauge`: Under the stated hypotheses, both own-row and coupling-row vectors vanish on each corner-stream coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L770).

**A nonzero forest gauge coefficient** · interface proposition. `ForestGaugeCoefficientStatement`: This predicate requires that the horizontal-side gauge value is the pressure jump times a nonzero inner-radius test moment under the specified zero outer moment condition. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L774).

A named provider for this exact interface was not identified in the source.

**The strong equation with pressure** · proposition definition. `IsStrongRightSide`: This predicate requires that the right side equals transport minus the Hessian trace plus coupling, actuator forcing and pressure gradient almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L781).

**A low-coordinate form as an integral** · interface proposition. `LowSlotFormValueStatement`: This predicate requires that the finite low-slot quadratic form equals the integrated matrix form on the retained polynomial profile. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L787).

Proved by `Breakdown.CertCell.CellCalculus.lowSlotFormValue_holds`.

**Physical fields as a cell vector** · definition. `cellState`: This vector combines the harmonic cell data, arbitrary complex ports and the two real actuator-coordinate blocks. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L796).

**Source section `CellForm`.**

**Positive part of the cell form** · definition. `cellPos`: This extended nonnegative value sums the positive label-density integrals and the positive mean stretching on a cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L806).

**Negative part of the cell form** · definition. `cellNeg`: This extended nonnegative value sums the negative label-density integrals and the negative mean stretching on a cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L811).

**Positive charged omitted-mode form** · definition. `offPos`: This extended nonnegative value sums positive off-mode density integrals outside the resolved labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L817).

**Negative charged omitted-mode form** · definition. `offNeg`: This extended nonnegative value sums negative off-mode density integrals outside the resolved labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L825).

**Weights of the two actuator blocks** · definition. `pairWeight`: This function uses κ on the first block and 2ζ on the second block. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L836).

**Source section `Entry`.**

**Indices of a cell's auxiliary ports** · abbreviation. `PortVar`: This finite type has one index for each auxiliary port declared for the cell. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L877).

**Source section `Assembly`.**

**Retained cell energy budget** · definition. `energyBudget`: This amount combines the Hessian and curl-Hessian energy after tail subtraction with the low-profile residual energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L898).

**Reserved second-derivative tail energy** · definition. `tailCredit`: This amount sums gradient and curl tail energies multiplied by the corresponding leaf lower bounds. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L914).

**The energy leaf fits its physical budget** · interface proposition. `EnergyLeafBoundStatement`: This predicate requires that the energy-leaf quadratic form on a physical cell state is bounded by the retained physical energy budget. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L921).

Proved by `Breakdown.CertCell.CellCalculus.energyLeafBound_of_periodic`.

**Residual bound with signed allocations** · proposition definition. `IsResidualFormBound`: This predicate requires that the residual form and energy budget satisfy the extended nonnegative allocation inequality for every compatible physical tuple and auxiliary state. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L929).

**Assemble the physical cell-form bound** · theorem. `cellFormAssembly_of`: Under the stated hypotheses, the cell residual and energy-leaf bounds combine into the required cell-form inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellCalculusStatements.lean#L954).

### Breakdown.CertCell.CellLayerClosed

This file closes the strip and corner reflection interfaces and the turning condition for band profiles from proved bridge facts. Appendix B: the analytic assembly feeding the extended certificate and Proposition B.14.

**Reflect strip data including the axis** · theorem. `planeFlipStrip_closed`: Under the stated hypotheses, velocity strip data obey the reflection law up to the axis, with the extra axis test condition for derivative data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L74).

**Reflect corner data including the axis** · theorem. `planeFlipCorner_closed`: Under the stated hypotheses, corner velocity data obey the reflection law when the opposite radial endpoint may lie on the axis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L80).

**Physical band profiles obey turning** · theorem. `bandProfileTurned_closed`: Under the stated hypotheses, every admissible physical cell tuple satisfies the angular derivative relation on band labels. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerClosed.lean#L103).

### Breakdown.CertCell.CellLayerConclusion

This file combines instantiated rows, initial data and the cell-form estimate into the row-rest and extended coercivity clauses. Appendix B: the analytic assembly feeding the extended certificate and Proposition B.14.

**Source namespace `Breakdown.CertCell`.**

**Row-generator pairing moments** · theorem. `generatorPairingMoments_holds`: Under the stated hypotheses, the instantiated row-generator pairings agree with their specified moments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L49).

**Rows give the class quadratic form** · theorem. `rowsClassForm_holds`: Under the stated hypotheses, the instantiated rows supply the prescribed quadratic form on their harmonic class. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L54).

**The field-instance interfaces** · theorem. `instanceParts_holds`: Under the stated hypotheses, the instantiated fields supply the row-pairing and class-form identities. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L60).

**Source section `CellLayerBreakdown`.**

**Bound the assembled half-plane form** · theorem. `halfPlaneFormBound_of_parts`: Under the stated hypotheses, the cell, exterior and coupling inputs imply the half-plane form bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L81).

**Bound the residual after row terms** · theorem. `rowRestClause_of_bridge_initial_cellForm`: Under the stated hypotheses, the residual form after the row contributions satisfies the certificate's row-rest inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L89).

**Extended certificate coercivity** · theorem. `extendedCoerciveClause_of_bridge_initial_cellForm`: Under the stated hypotheses, the instantiated cell analysis supplies the full extended coercivity clause. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerConclusion.lean#L103).

### Breakdown.CertCell.CellLayerJunctions

This file supplies the shape, harmonic and reflection interfaces needed to connect concrete spline fields to the final row and coercivity reductions. Appendix B: the analytic assembly feeding the extended certificate and Proposition B.14.

**Source namespace `Breakdown.CertCell.GivenShape`.**

**Bound slopes of joined spline gradients** · theorem. `joinedSplineGradSlopeBound_closed`: Under the stated hypotheses, the joined spline gradient has the required slope bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L91).

**Smooth type-one harmonic key** · theorem. `typeOneKeySmooth_closed`: Under the stated hypotheses, the first harmonic-key construction has the required smoothness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L94).

**Smooth type-two harmonic key** · theorem. `typeTwoKeySmooth_closed`: Under the stated hypotheses, the second harmonic-key construction has the required smoothness. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L99).

**Divergence in the cylindrical frame** · theorem. `framedDivergenceFormula_closed`: Under the stated hypotheses, the framed components satisfy the stated cylindrical divergence formula. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L106).

**Each valid key is divergence-free** · theorem. `keyDivergenceFree_closed`: Under the stated hypotheses, each valid harmonic-key field has zero divergence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L109).

**Harmonic expansion of a shape field** · theorem. `fieldHarmonicExpansion_closed`: Under the stated hypotheses, the constructed shape field has its prescribed finite harmonic expansion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L113).

**The jet representation interfaces** · theorem. `jetParts_closed`: Under the stated hypotheses, the jet data supply the required spline, matching and evaluation interfaces. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L157).

**Symmetry of the field Hessian** · theorem. `fieldSecondSymmetric_closed`: Under the stated hypotheses, the constructed field's second-derivative tensor is symmetric in its derivative arguments. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L160).

**Source namespace `Breakdown.CertCell`.**

**Integrability of the velocity L6 norm** · theorem. `velocitySixthIntegral_closed`: Under the stated hypotheses, an admissible perturbation has finite time integral of the spatial sixth-power integral raised to the one-sixth power. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L172).

**Weak height derivatives of modes** · theorem. `modeHeightDeriv_closed`: Under the stated hypotheses, velocity and gradient harmonic coefficients have the prescribed weak height derivatives on almost every positive-radius line. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L175).

**Reflect the plane trace data** · theorem. `planeDataFlip_closed`: Under the stated hypotheses, the velocity trace and its height derivative acquire their respective reflection signs when the harmonic label is flipped. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L178).

**Reflect off-axis strip data** · theorem. `stripDataFlip_closed`: Under the stated hypotheses, the velocity and height-derivative strip moments obey the frame-sign reflection law on strictly positive radial strips. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L181).

**Reflect off-axis corner data** · theorem. `cornerDataFlip_closed`: Under the stated hypotheses, the corner moment on a strictly positive-radius rectangle obeys the velocity component's reflection sign. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L185).

**Reflect a scalar plane trace** · theorem. `scalarPlaneFlip_closed`: Under the stated hypotheses, a reflection-even scalar with the specified weak gradient has matching reflected harmonic traces on the equatorial plane. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L190).

**Source section `Closure`.**

**Bound the residual after row terms** · theorem. `rowRestClause_of_parts`: Under the stated hypotheses, the residual form after the row contributions satisfies the certificate's row-rest inequality. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L286).

**Extended certificate coercivity** · theorem. `extendedCoerciveClause_of_parts`: Under the stated hypotheses, the instantiated cell analysis supplies the full extended coercivity clause. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerJunctions.lean#L296).

### Breakdown.CertCell.CellLayerPartProofs

This file supplies the remaining jet, periodicity, credit and exterior components of the analytic cell-layer package. Appendix B: the analytic assembly feeding the extended certificate and Proposition B.14.

**The scaled-jet conversion interfaces** · theorem. `scaledJetParts_closed`: Under the stated hypotheses, scaled jet coefficients supply the ordinary jet representation interfaces after conversion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L46).

**Periodic fields with weak derivatives** · theorem. `periodicSecondOrder_closed`: Under the stated hypotheses, velocity, gradient and Hessian are measurable and periodic, represent the weak derivatives and satisfy the required finite energy conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L49).

**Credit evaluation matches physical data** · theorem. `creditEvalMatches_closed`: Under the stated hypotheses, the finite credit evaluation agrees with the corresponding physical trace data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L68).

**Nonnegative exterior contribution** · theorem. `exteriorNonneg_of_offModeSound`: Under the stated hypotheses, the admissible field, mode-class and valid exterior-cover conditions imply nonnegativity of the exterior form. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L77).

**The analytic cell-layer package** · theorem. `cellLayerParts_of_cell`: Under the stated hypotheses, the initial-state, bridge, cell-form and reduction interfaces needed by the analytic cell layer hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartProofs.lean#L87).

### Breakdown.CertCell.CellLayerPartStages

This file assembles the complete analytic cell-layer package from the proved stages and a cell hypothesis. Appendix B: the analytic assembly feeding the extended certificate and Proposition B.14.

**The analytic cell-layer package** · theorem. `cellLayerParts_of_stages`: Under the stated hypotheses, the initial-state, bridge, cell-form and reduction interfaces needed by the analytic cell layer hold together. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerPartStages.lean#L16).

### Breakdown.CertCell.CellLayerStatements

This file packages the pressure-potential and reflection interfaces consumed by the cell-layer assembly. Appendix B: the analytic assembly feeding the extended certificate and Proposition B.14.

**Recover pressure reflection uniformly** · proposition definition. `PressureFlipParts`: This predicate requires that the pressure facts imply the reflection identity for the chosen pressure gradient for every cell data set. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellLayerStatements.lean#L27).

### Breakdown.CertCell.CellRowFormula

This file proves the cell row formula by integrating the weak equation against the actual polynomial row tests. Appendix B.1–B.3: harmonic fields, traces and weak row identities.

**Source namespace `Breakdown.CertCell.CellCalculus.Internal.RowForm`.**

**The cell rectangle is measurable** · theorem. `rect_meas`: The closed radial-height rectangle associated with a cell box is Lebesgue measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L17).

**The cell rectangle is compact** · theorem. `rect_cpt`: The cell's closed and bounded radial-height rectangle is compact. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L19).

**Cell radii are nonnegative** · theorem. `fst_nonneg`: Every point in the stated cell rectangle has nonnegative first coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L21).

**Cell polynomial evaluation is continuous** · theorem. `eval_cont`: Evaluating a fixed cell polynomial gives a continuous function of the radial-height point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L24).

**Complex coercion preserves C1 regularity** · theorem. `ofReal_contDiff`: The complex coercion of the given real C1 function remains C1 over the real scalar field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L28).

**Cell polynomial evaluation is C1** · theorem. `eval_contDiff`: The function obtained by evaluating a cell polynomial on planar points is continuously differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L31).

**Radial derivatives of C1 functions** · theorem. `radial_cont`: The radial partial derivative of a C1 planar function is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L38).

**Height derivatives of C1 functions** · theorem. `height_cont`: The height partial derivative of a C1 planar function is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L47).

**Bounded tests fit radial-energy profiles** · theorem. `weighted_int`: A measurable profile with finite radial-weighted squared norm has integrable radial-weighted product with a measurable bounded test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L56).

**Pair a radial-energy profile with a test** · theorem. `weighted_int_cont`: A measurable profile with finite radial-weighted squared norm has integrable radial-weighted product with a continuous test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L75).

**Domination gives coordinate energy** · theorem. `comp_int`: A measurable coordinate whose radial-weighted squared norm is bounded by an integrable function has integrable radial-weighted squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L82).

**Finite coordinate energy is nonnegative** · theorem. `Breakdown.CertCell.CellRowFormula.cnormSq_nonneg`: The squared-coordinate norm of a finite complex vector is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L90).

**One coordinate energy fits in the total** · theorem. `le_cnormSq`: The squared norm of any coordinate is at most the total squared-coordinate norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L93).

**Coordinate energy from a vector bound** · theorem. `vec_int`: A measurable vector whose squared-coordinate norm is bounded by a radial-integrable profile has integrable radial-weighted energy in each coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L96).

**A polynomial row pairing integrates** · theorem. `pair_int`: A measurable vector with finite radial-weighted energy in every coordinate has integrable radial-weighted pairing with the polynomial row test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L103).

**The angular vector map is continuous** · theorem. `turn_cont`: Each coordinate of the fixed-frequency angular turn map depends continuously on the complex vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L116).

**The polynomial test vector is continuous** · theorem. `testValue_cont`: The vector formed by evaluating the three cell test polynomials is continuous in the plane point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L120).

**Test-gradient coordinates are measurable** · theorem. `testGrad_meas`: Every conjugate test-gradient coordinate is almost-everywhere strongly measurable on the cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L123).

**Test gradients have a cell bound** · theorem. `testGrad_bound`: Each conjugate test-gradient component has one uniform norm bound on the compact cell rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L136).

**Split five integrable equation terms** · theorem. `five_split`: The integral of the displayed sum and difference of five integrable terms equals the corresponding sum and difference of their integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L155).

**Source namespace `Breakdown.CertCell.CellCalculus`.**

**The weak cell row formula** · theorem. `cellRowFormula_holds`: Under the stated hypotheses, the tested right side equals the interior row expression minus the gradient boundary term plus pressure, coupling and drive pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CellRowFormula.lean#L167).

### Breakdown.CertCell.CertComplexSlackBound

This file controls the error of a complex matrix enclosure by diagonal slack and compares the resulting quadratic form with its exact matrix. Appendix B.3: tree enclosure and slack, (B.38)–(B.42), Lemma B.7.

**Add complex matrices inside the value** · lemma. `formValue_add`: The real-valued complex quadratic is additive in its matrix argument. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L10).

**Subtract complex quadratic matrices** · lemma. `formValue_sub`: The complex form value of a matrix difference equals the difference of the two form values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L15).

**Expand a complex form into entries** · lemma. `formValue_eq_sum`: The complex quadratic value equals the double sum of the real parts of conjugate input coordinate times matrix entry times input coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L20).

**Conjugate self-product is squared norm** · lemma. `re_star_mul_self`: The real part of conjugate(z) times z equals the squared norm of z. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L25).

**Value of a complex diagonal form** · lemma. `formValue_diagonal`: The complex quadratic value of the selected real diagonal matrix equals the weighted sum of squared coordinate norms over the selected pivots. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L29).

**A complex Gram form is a sum of squares** · lemma. `formValue_pairMatrix`: The complex quadratic value of F times its conjugate transpose is the sum of squared norms of the conjugate-column pairings with the input vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L50).

**Balance a product with two weights** · lemma. `weighted_product_le`: For positive u and v, a times b is at most half the sum of (u/v) times a squared and (v/u) times b squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L63).

**Weighted row sums bound a remainder** · lemma. `remainder_lower`: Symmetric entry norms and positive weights whose weighted row sums are bounded by r imply that the complex remainder form is at least minus the r-weighted coordinate energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L71).

**A real complex diagonal is Hermitian** · lemma. `complexDiagonal_conjTranspose`: The selected diagonal matrix with real entries is equal to its conjugate transpose. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertComplexSlackBound.lean#L113).

### Breakdown.CertCell.CertCoordinateSlack

This file relates an owned tree coordinate to its optional embedding and bounds the coordinate contribution used in certificate slack. Appendix B.3: tree enclosure and slack, (B.38)–(B.42), Lemma B.7.

**Value of an optional coordinate** · definition. `optionValue`: This function reads the selected coordinate when it exists and returns zero for an absent coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertCoordinateSlack.lean#L10).

**Square an optional coordinate** · lemma. `optionValue_sq`: The square of an optional coordinate value equals the sum selecting the matching coordinate square, with no contribution for an absent coordinate. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertCoordinateSlack.lean#L13).

**Read an encoded complex coordinate** · lemma. `matrix_mulVec_apply`: The coordinate-map matrix sends a real vector to the selected real coordinate plus i times the selected imaginary coordinate with its stored sign. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertCoordinateSlack.lean#L19).

**Imaginary sign preserves energy** · lemma. `norm_sq_coordinate`: When the real sign has square one, the squared norm of a plus sign times i times b is a squared plus b squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertCoordinateSlack.lean#L30).

**Owned coordinates account for the energy** · lemma. `owned_sum`: When a complex output uses distinct real and imaginary input coordinates, the sum of their squares equals the sum of squares over precisely the coordinates it owns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertCoordinateSlack.lean#L40).

### Breakdown.CertCell.CertPivotCount

This file expands tree quadratic forms over matrix sums, diagonal pivots and rank-one columns for the finite certificate argument. Appendix B.3: tree enclosure and slack, (B.38)–(B.42), Lemma B.7.

**Add two real quadratic matrices** · theorem. `quadValue_add_matrix`: The quadratic value of a matrix sum equals the sum of the two quadratic values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertPivotCount.lean#L10).

**Subtract two real quadratic matrices** · theorem. `quadValue_sub_matrix`: The quadratic value of a matrix difference equals the difference of the two quadratic values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertPivotCount.lean#L14).

**Sum finitely many real quadratic forms** · theorem. `quadValue_sum_matrix`: The quadratic value of a finite matrix sum equals the finite sum of the individual quadratic values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertPivotCount.lean#L18).

**Value of a real diagonal form** · theorem. `quadValue_diagonal_matrix`: A real diagonal matrix has quadratic value equal to the sum of each diagonal entry times its coordinate squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertPivotCount.lean#L26).

**A rank-one real form is a square** · theorem. `quadValue_vecMulVec_self`: The quadratic value of the outer product of c with itself equals the square of the dot product of c with the input vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertPivotCount.lean#L31).

### Breakdown.CertCell.CertRealRestriction

This file transfers complex Hermitian form calculations to the real coordinate restriction used by the certificate. Appendix B.3: tree enclosure and slack, (B.38)–(B.42), Lemma B.7.

**Take real parts on real input vectors** · lemma. `re_real_quadratic`: The real part of the complex matrix quadratic on a real-coerced vector equals the real quadratic for the entrywise real part of the matrix. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertRealRestriction.lean#L10).

**Restriction preserves quadratic value** · theorem. `realRestrictionValue`: Restricting a complex form through a complex embedding and taking its real matrix gives the same quadratic value on real inputs as evaluating the complex form on their embedded vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertRealRestriction.lean#L15).

**Restriction preserves matrix addition** · theorem. `realRestrictionAdd`: The real restriction through a fixed embedding sends a matrix sum to the sum of the two real restrictions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertRealRestriction.lean#L26).

**Move the embedding to the column** · lemma. `column_pairing`: Pairing a complex column with an embedded real vector equals pairing the conjugate-transpose-transformed column with the original real-coerced vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertRealRestriction.lean#L31).

### Breakdown.CertCell.CertSlackBound

This file bounds the negative pivot contribution using the weighted diagonal slack assigned to the real certificate form. Appendix B.3: tree enclosure and slack, (B.38)–(B.42), Lemma B.7.

**Add real quadratic forms** · theorem. `quadValue_add_forms`: The quadratic value of the sum of two real matrices is the sum of their quadratic values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertSlackBound.lean#L10).

**Subtract real quadratic forms** · theorem. `quadValue_sub_forms`: The quadratic value of the difference of two real matrices is the difference of their quadratic values. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertSlackBound.lean#L14).

**Value of a selected pivot diagonal** · theorem. `quadValue_pivotDiagonal`: The quadratic value of the pivot diagonal equals the sum over selected pivots of each pivot weight times its coordinate squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertSlackBound.lean#L18).

**A real Gram form is a sum of squares** · theorem. `quadValue_pairMatrix`: The quadratic value of F times its transpose equals the sum of the squared column pairings of F with the input vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertSlackBound.lean#L34).

**Weighted bound for an absolute product** · theorem. `two_abs_mul_le_weighted`: For positive u and v, twice abs(a) times abs(b) is at most a squared times u/v plus b squared times v/u. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertSlackBound.lean#L39).

**A row-sum bound controls a real form** · theorem. `neg_weighted_le_quadValue`: A symmetric real matrix with the stated positive-weight row-sum bounds has quadratic value at least minus the corresponding weighted coordinate-square sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertSlackBound.lean#L44).

### Breakdown.CertCell.CertTreeLowerBound

Expands quadratic forms through sums and signed certificate-tree transitions. These identities turn the leaf and pivot conditions into a lower bound at the root. Appendix B: cell-system construction and finite certificate analysis.

**Quadratic forms preserve addition.** Proved result. Under the stated hypotheses, the quadratic form of a sum of matrices is the sum of their quadratic forms. (`quad_add_forms`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L9)).

**Quadratic forms preserve subtraction.** Proved result. Under the stated hypotheses, the quadratic form of a matrix difference is the difference of the quadratic forms. (`quad_sub_forms`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L13)).

**Quadratic forms preserve finite sums.** Proved result. Under the stated hypotheses, evaluating a finite sum of matrices gives the sum of their quadratic values. (`quad_finset_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L17)).

**Diagonal quadratic form.** Proved result. Under the stated hypotheses, a diagonal matrix contributes the weighted sum of squared coordinates. (`quad_diagonal_form`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L24)).

**Outer product gives a square.** Proved result. Under the stated hypotheses, the quadratic form of a vector outer product is the square of its dot product. (`quad_outer_form`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertTreeLowerBound.lean#L29)).

### Breakdown.CertCell.Certificate

Transfers a complex node bound to real coordinates and concludes nonnegativity from a signed state certificate. The result remains conditional on the certificate's finite algebraic conditions. Appendix B: cell-system construction and finite certificate analysis.

**Real bound from a complex node.** Proved result. Under the stated hypotheses, the complex node estimate supplies the real quadratic lower bound. (`complexNodeRealBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Certificate.lean#L14)).

**State certificate gives nonnegativity.** Proved result. Under the stated hypotheses, a valid signed state certificate makes the target function nonnegative everywhere. (`stateCertificateNonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Certificate.lean#L18)).

### Breakdown.CertCell.CertificateEnclosureStatements

Defines certificate conditions that tolerate interval enclosures and accumulated front errors. It derives real and complex node bounds from those conditions and propagates them through the signed tree. Appendix B: cell-system construction and finite certificate analysis.

**Real enclosure gives a node bound.** Proposition definition. The interface requires that a passing real node enclosure bounds the front plus pivot gain minus column loss by the node input. (`RealNodeEnclosureBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L10)).

**Complex enclosure gives a node bound.** Proposition definition. The interface requires that a passing complex node enclosure bounds the real node front plus gains minus losses by its input. (`ComplexNodeEnclosureBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L15)).

**Signed state enclosure conditions.** Proposition structure. The interface requires that the state, root, node enclosures, pivot count and base value satisfy the enclosure certificate conditions. (`IsSignedStateEnclosureCertificate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L20)).

**Exact real node gives an enclosure.** Proved result. Under the stated hypotheses, an exact real node condition gives an enclosure with both error matrices zero. (`realNodeEnclosure_of_condition`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L34)).

**Exact complex node gives an enclosure.** Proved result. Under the stated hypotheses, an exact complex node condition gives an enclosure with both error matrices zero. (`complexNodeEnclosure_of_condition`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L49)).

**Exact node gives an enclosure.** Proved result. Under the stated hypotheses, a passing exact node gives either a real or a complex enclosure. (`nodeEnclosure_of_condition`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L68)).

**Exact certificate gives enclosures.** Proved result. Under the stated hypotheses, a signed state certificate supplies all signed state enclosure conditions. (`isSignedStateEnclosureCertificate_of_certificate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L74)).

**Enclosures give a signed tree.** Proved result. Under the stated hypotheses, the node enclosure bounds and root conditions make the tree a signed tree. (`isSignedTree_of_nodeEnclosures`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L87)).

**Enclosures give nonnegativity.** Proved result. Under the stated hypotheses, terminal validity and the two enclosure bounds imply nonnegativity from an enclosure certificate. (`stateEnclosureCertificateNonneg_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L96)).

**Weighted product bound.** Proved result. Under the stated hypotheses, a product is bounded by half the sum of two reciprocal-weighted squares when the weights are positive. (`mul_le_weighted_half`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L106)).

**Weighted row bound for a form.** Proved result. Under the stated hypotheses, a symmetric matrix with nonnegative entries is bounded by its weighted row sums on squared coordinates. (`quadValue_le_weightedRows`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L114)).

**Pivot diagonal evaluates to squares.** Proved result. Under the stated hypotheses, the pivot diagonal quadratic form sums the specified pivot squares. (`quadValue_pivotDiagonal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L146)).

**Quadratic form of a difference.** Proved result. Under the stated hypotheses, subtracting matrices subtracts their quadratic values. (`quadValue_sub'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L157)).

**Quadratic form of a sum.** Proved result. Under the stated hypotheses, adding matrices adds their quadratic values. (`quadValue_add'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L161)).

**Complex form of a difference.** Proved result. Under the stated hypotheses, subtracting complex matrices subtracts their real quadratic values. (`complexFormValue_sub'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L226)).

**Complex diagonal form.** Proved result. Under the stated hypotheses, the complex pivot diagonal gives a weighted sum of squared coordinate norms. (`complexFormValue_complexDiagonal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L230)).

**Certificate bounds give enclosures.** Proved result. Under the stated hypotheses, the terminal, slack, restriction and coordinate bounds imply the enclosure certificate conclusion. (`stateEnclosureCertificateNonneg_of_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateEnclosureStatements.lean#L338)).

### Breakdown.CertCell.CertificateStatements

Defines terminal tests, pivot gains, column losses, signed state transitions and admissible gauge changes. These finite algebraic objects express the certificate obligations used to establish quadratic nonnegativity. Appendix B: cell-system construction and finite certificate analysis.

**Coordinates absent from a form.** Proposition definition. The interface requires that the quadratic form ignores changes in the selected slaved coordinates. (`IsIndependentOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L15)).

**Terminal positivity criterion.** Proposition definition. The interface requires that a state with the stated positive subspace dimension and ignored coordinates makes the target nonnegative. (`StateTerminalTest`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L20)).

**Pivot gain.** Definition. This defines the sum of pivot slacks times squared coordinates at a node. (`pivotGain`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L34)).

**Column loss.** Definition. This defines the sum of squared column dot products assigned to a node. (`columnLoss`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L38)).

**Root form.** Definition. This defines the root front with all pivot diagonals added and all column outer products subtracted. (`rootForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L43)).

**Signed tree conditions.** Proposition structure. The interface requires that the root is the unique parentless node and every node satisfies its quadratic bound. (`IsSignedTree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L50)).

**Root form lies below leaf sum.** Proposition definition. The interface requires that every signed tree bounds its root quadratic form by its total leaf form. (`SignedTreeLowerBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L56)).

**Pivot count supplies positivity.** Proposition definition. The interface requires that a passing pivot count supplies a positive subspace of at least the slaved dimension. (`PivotCountPositive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L60)).

**Signed certificate terminal rule.** Proposition definition. The interface requires that a signed tree and passing pivot count turn the state inequality into global nonnegativity. (`SignedCertificateTerminal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L64)).

**Tree certificate has a signed form.** Proposition definition. The interface requires that a tree certificate admits a signed-tree representation with the stated terminal dimension bound. (`TreeCertificateIsSigned`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L69)).

**Real signed slack bound.** Proposition definition. The interface requires that weighted row bounds on the real slack remainder give the stated lower bound with pivot gains and column losses. (`SignedSlackBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L76)).

**Complex quadratic value.** Definition. This defines the real part of the Hermitian pairing of a vector with its matrix image. (`complexFormValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L84)).

**Complex signed slack bound.** Proposition definition. The interface requires that weighted row bounds on a Hermitian slack remainder give the complex quadratic lower bound. (`ComplexSignedSlackBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L87)).

**Real restriction preserves value.** Proposition definition. The interface requires that restricting a complex form along a real coordinate map preserves its real quadratic value. (`RealRestrictionValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L96)).

**Real restriction preserves sums.** Proposition definition. The interface requires that real restriction distributes over addition of complex matrices. (`RealRestrictionAdd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L100)).

**Complex column splits into two squares.** Proposition definition. The interface requires that a nonnegative multiple of a complex column norm is the sum of its two real column squares. (`ComplexColumnSplit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L104)).

**Coordinate slack after realification.** Proposition definition. The interface requires that coordinate realification transports the pivot norm squares to the corresponding real coordinate squares. (`CoordinateSlack`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L116)).

**Complex node yields a real bound.** Proposition definition. The interface requires that the complex slack estimate transports through coordinate realification to the stated real lower bound. (`ComplexNodeRealBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L122)).

**Signed involution data.** Data structure. `Breakdown.CertCell.Certificate.SignedInvolution` stores a permutation and the real signs used for signed conjugation. (`SignedInvolution`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L134)).

**Signed involution conditions.** Proposition structure. The interface requires that the permutation and signs satisfy the involution and sign compatibility conditions. (`IsSignedInvolution`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L138)).

**Signed conjugate vector.** Definition. This defines signed conjugation after applying the coordinate permutation. (`conjVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L147)).

**Signed conjugate matrix.** Definition. This defines matrix conjugation with permuted coordinates and their two signs. (`conjMatrix`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L149)).

**Signed conjugation preserves a form.** Proposition definition. The interface requires that signed vector conjugation is equivalent to evaluating the signed conjugate matrix. (`ConjugateFormValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L154)).

**Transport a conjugate lower bound.** Proposition definition. The interface requires that a lower bound transfers to the conjugate form when the comparison function transforms compatibly. (`ConjugateHalfLowerBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L158)).

**Conjugate form on a real subspace.** Proposition definition. The interface requires that a conjugation-fixed coordinate subspace gives equal quadratic values for a matrix and its conjugate. (`ConjugateOnRealSubspace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L163)).

**Lower a state form.** Proposition definition. The interface requires that a lower quadratic form remains a state after adding unused free coordinates. (`StateLowerStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L169)).

**Change slaved coordinates.** Proposition definition. The interface requires that a right-invertible change of slaved coordinates preserves the state inequality under the stated form bound. (`StateChangeStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L176)).

**Restrict free coordinates.** Proposition definition. The interface requires that restricting the free variables through a linear map preserves the state inequality. (`StateRestrictStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L184)).

**Eliminate slaved coordinates.** Proposition definition. The interface requires that a lower form independent of the discarded slaved block gives a state on the retained block. (`StateEliminateStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L192)).

**Add a null form and constraints.** Proposition definition. The interface requires that a nonpositive null form and vanishing linear constraints may be added to the state lower bound. (`StateNullFormStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L200)).

**Use identities in a state.** Proposition definition. The interface requires that a coordinate map preserves the state inequality when the form bound holds on the constraint subspace. (`StateIdentityStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L210)).

**Index for copied coordinates.** Definition. This defines the index map that forgets which copy of a shared coordinate is used. (`copyIndex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L218)).

**Unshare state coordinates.** Proposition definition. The interface requires that duplicating shared coordinates and adding free variables preserves the stated state bound. (`StateUnshareStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L221)).

**Remove gauge coordinates.** Proposition definition. The interface requires that a normalized invariant gauge direction allows the selected slaved coordinates to be removed. (`StateGaugeStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L229)).

**Gauge from null vectors.** Proposition definition. The interface requires that a right inverse on the selected coordinates normalizes null directions into gauge directions. (`GaugeFromNullVectors`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L239)).

**Row dominance gives a right inverse.** Proposition definition. The interface requires that strict row diagonal dominance makes the real square matrix right-invertible. (`RowDominantRightInverse`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L247)).

**Triangular matrix has a right inverse.** Proposition definition. The interface requires that a rank-triangular matrix with nonzero diagonal has a right inverse. (`TriangularRightInverse`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L251)).

**Duplicate free coordinates.** Proposition definition. The interface requires that the stated copy identity and bilinear correction produce a valid state with duplicated free coordinates. (`StateFreeCopyStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L256)).

**Real node conditions.** Proposition structure. The interface requires that the real node data meet the symmetry, row, front, pivot and column conditions. (`PassesRealNodeCondition`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L279)).

**Complex node conditions.** Proposition structure. The interface requires that the complex node data meet the Hermitian, coordinate, row, front, pivot and column conditions. (`PassesComplexNodeCondition`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L292)).

**Either real or complex node.** Proposition definition. The interface requires that the node has valid real data or valid complex data. (`PassesNodeCondition`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L313)).

**Signed state certificate data.** Data structure. `Breakdown.CertCell.Certificate.SignedStateCertificate` stores the state coordinates, free map and signed tree for a target function. (`SignedStateCertificate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L317)).

**Signed state certificate conditions.** Proposition structure. The interface requires that the base value, state inequality, signed tree and pivot count hold. (`IsSignedStateCertificate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L327)).

**Certificate nonnegativity interface.** Proposition definition. The interface requires that every valid signed state certificate implies global nonnegativity of its target. (`StateCertificateNonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L337)).

**Certificate layer interfaces.** Interface. The interface requires that the terminal, tree, slack, realification and state-transformation interfaces all hold. (`CertificateLayerHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L341)). No named provider or direct consumer of this interface was found in the library.

**Terminal rule from three bounds.** Proved result. Under the stated hypotheses, the state terminal test, signed-tree lower bound and positive pivot count imply the signed certificate rule. (`signedCertificateTerminal_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L371)).

**Real node bound from complex pieces.** Proved result. Under the stated hypotheses, complex slack, real restriction, column splitting and coordinate slack give the real node bound. (`complexNodeRealBound_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L385)).

**Tree terminal nonnegativity.** Proved result. Under the stated hypotheses, a valid tree certificate and the state bound imply that the target is nonnegative. (`tree_terminal_of_signed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L405)).

**Node conditions give a signed tree.** Proved result. Under the stated hypotheses, passing node conditions and the root conditions make the tree signed. (`isSignedTree_of_nodeConditions`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L419)).

**Certificate rule from node bounds.** Proved result. Under the stated hypotheses, terminal validity and real and complex node estimates give state-certificate nonnegativity. (`stateCertificateNonneg_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CertificateStatements.lean#L471)).

### Breakdown.CertCell.ClassSupportLinks

Connects the label arithmetic and half-turn phase rule to the harmonic classes supporting a field. The resulting class-support statement determines which labels contribute to the class form. Appendix B: cell-system construction and finite certificate analysis.

**Half-turn phase selects lattice modes.** Proved result. Under the stated hypotheses, a trivial half-turn phase forces the frequency into the harmonic lattice. (`latticeHarmonic_of_halfTurnPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ClassSupportLinks.lean#L15)).

**Classes contain the supported modes.** Proved result. Under the stated hypotheses, velocity, gradient and second-derivative modes vanish almost everywhere at frequencies outside the permitted lattice. (`classSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ClassSupportLinks.lean#L46)).

### Breakdown.CertCell.CornerAxisTrace

Expresses a corner trace as an integrable rectangle moment and studies the limit as its inner radial endpoint approaches the axis. The argument supplies the axis-compatible corner trace from the weak radial and height derivatives. Appendix B: cell-system construction and finite certificate analysis.

**Corner trace integrand.** Definition. This defines the four-term affine combination of a field and its two first and mixed derivatives. (`cornerIntegrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L17)).

**Corner moment as an integral.** Proved result. Under the stated hypotheses, the corner moment is the rectangle integral of its integrand with the two orientation signs. (`cornerMoment_eq_integrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L23)).

**Axis cutoff integrand.** Definition. This defines the corner integrand restricted to the rectangle with inner radius δ. (`axisCut`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L28)).

**Radii approaching the axis.** Definition. This defines the axis-approaching radius as the fixed corner radius divided by twice the successor of the natural-number index. (`axisStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L31)).

**Axis approximation is positive.** Proved result. Under the stated hypotheses, every approximating radius is positive when the outer radius is positive. (`axisStep_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L33)).

**Axis approximation stays below half.** Proved result. Under the stated hypotheses, each approximating radius is at most half the outer radius. (`axisStep_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L37)).

**Axis approximation stays inside.** Proved result. Under the stated hypotheses, each approximating radius is strictly below the positive outer radius. (`axisStep_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L45)).

**Axis approximation tends to zero.** Proved result. Under the stated hypotheses, the chosen sequence of inner radii converges to zero. (`axisStep_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L48)).

**The radial axis is null.** Proved result. Under the stated hypotheses, the radial coordinate is nonzero almost everywhere in the plane. (`ae_fst_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L53)).

**Remove a measurable radial weight.** Proved result. Under the stated hypotheses, almost-everywhere nonvanishing radius lets measurability pass from the weighted function to the function. (`aesm_of_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L61)).

**Corner integrand is measurable.** Proved result. Under the stated hypotheses, the four-term corner integrand is almost everywhere strongly measurable. (`cornerIntegrand_aesm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L71)).

**Corner moment with an axis cutoff.** Proved result. Under the stated hypotheses, the corner moment on the truncated rectangle equals the cutoff integral over the rectangle reaching the axis. (`key_moment`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L82)).

**Uniform bound for the axis cutoff.** Proved result. Under the stated hypotheses, the cutoff integrand is dominated by the stated weighted norms independently of a sufficiently small inner radius. (`axisCut_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L97)).

**Corner integrands converge at the axis.** Proved result. Under the stated hypotheses, the corner integrands converge pointwise as the inner radius approaches zero. (`integrand_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L161)).

**Corner moments converge at the axis.** Proved result. Under the stated hypotheses, the stated weighted integrability conditions allow the corner moment to converge to its axis value. (`axis_limit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L181)).

**Corner traces reach the axis.** Proved result. Under the stated hypotheses, the corner moment with auxiliary radial endpoint zero equals the moment with any permitted auxiliary radial and height endpoints. (`cornerAxisTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerAxisTrace.lean#L227)).

### Breakdown.CertCell.CornerDataFlipAxis

Proves how side and corner traces behave under height reflection, almost-everywhere replacement and an axis endpoint. These identities give the reflected local corner data used by the cell construction. Appendix B: cell-system construction and finite certificate analysis.

**Upper side trace.** Proved result. Under the stated hypotheses, the side trace from zero to positive height is the upper trace. (`side_upper`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L16)).

**Lower side trace.** Proved result. Under the stated hypotheses, the side trace from zero to negative height is the lower trace. (`side_lower`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L28)).

**Upper trace after reflection.** Proved result. Under the stated hypotheses, reflecting height exchanges the upper and lower traces with the specified scalar factor. (`upper_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L40)).

**Upper traces respect a.e. equality.** Proved result. Under the stated hypotheses, almost-everywhere equal field and derivative data give equal upper traces. (`upper_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L52)).

**Weak derivative respects a.e. equality.** Proved result. Under the stated hypotheses, replacing a weak derivative by an almost-everywhere equal function preserves the weak derivative. (`weak_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L60)).

**Combine two side traces.** Proved result. Under the stated hypotheses, the stated relation between the coefficients combines the two side traces into the alternate form. (`side_comb`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L69)).

**Reflected traces agree across heights.** Proved result. Under the stated hypotheses, the reflected weak data give equal weighted trace combinations for the two positive heights. (`line_step`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L108)).

**Corner moment from upper traces.** Proved result. Under the stated hypotheses, the corner moment is a radial integral of the indicated weighted upper traces. (`corner_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L154)).

**Corner derivative data are integrable.** Proved result. Under the stated hypotheses, the four required velocity, gradient and weighted mixed-derivative profiles are integrable on the rectangle. (`data_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L174)).

**Mixed slope agrees a.e..** Proved result. Under the stated hypotheses, the mixed mode derivative agrees almost everywhere off the axis with the chosen plane slope. (`slope_swap_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L199)).

**Axis corner data reflect correctly.** Proved result. Under the stated hypotheses, reversing the label gives the frame sign times the original corner velocity moment, including an auxiliary endpoint on the axis. (`cornerDataFlipAxis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipAxis.lean#L285)).

### Breakdown.CertCell.CornerDataFlipLinks

Connects weak plane data and almost-everywhere reflection identities to the packaged corner-data flip statement. It supplies the local weak derivatives needed by the corner trace argument. Appendix B: cell-system construction and finite certificate analysis.

**Plane modes after reflection.** Proved result. Under the stated hypotheses, the velocity, gradient and second-derivative modes transform almost everywhere with their frame signs. (`ae_plane_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L21)).

**Corner moment respects a.e. data.** Proved result. Under the stated hypotheses, almost-everywhere equality of the four inputs preserves the corner moment. (`cornerMoment_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L70)).

**Weak plane derivative data.** Proved result. Under the stated hypotheses, the plane modes have the stated local integrability and weak derivative identities. (`plane_weak_data`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L80)).

**Commute a real test factor.** Proved result. Under the stated hypotheses, the real test factor may be moved across the complex integrand. (`integral_mul_comm_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L155)).

**Restrict a weak identity.** Proved result. Under the stated hypotheses, a weak integral identity restricts to the rectangle when both test functions vanish outside it. (`weak_on_rectangle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L159)).

**Weak derivatives on rectangles.** Proved result. Under the stated hypotheses, the plane velocity and derivative modes form a weak plane-derivative tuple on rectangles away from the axis. (`plane_derivs_on`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L168)).

**Trace does not depend on height.** Proved result. Under the stated hypotheses, the upper trace is independent of the positive auxiliary height for the stated weak derivative data. (`trace_heights`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L190)).

**Corner data reflect correctly.** Proved result. Under the stated hypotheses, reversing the label gives the frame sign times the original corner velocity moment when both radial endpoints are positive. (`cornerDataFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerDataFlipLinks.lean#L200)).

### Breakdown.CertCell.CornerFlip

Uses the measure-preserving height-negation map to reflect rectangle moments and corner traces. The final statement records the component signs and exchanged height endpoints. Appendix B: cell-system construction and finite certificate analysis.

**Height reflection equivalence.** Definition. This defines the measurable equivalence that negates height and leaves radius fixed. (`heightNegEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L15)).

**Height reflection coordinates.** Proved result. Under the stated hypotheses, the measurable reflection sends the pair to radius and negative height. (`heightNegEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L18)).

**Reflection preserves plane measure.** Proved result. Under the stated hypotheses, height reflection preserves two-dimensional volume. (`heightNegEquiv_measurePreserving`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L20)).

**Reflect a rectangle.** Proved result. Under the stated hypotheses, the preimage of the reflected rectangle is the original rectangle. (`heightNeg_preimage`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L24)).

**Reflect a rectangle integral.** Proved result. Under the stated hypotheses, negating height transfers the set integral to the reflected rectangle. (`flipped_setIntegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L45)).

**Orientation sign under reflection.** Proved result. Under the stated hypotheses, negating the integrand has the same effect as reversing the height orientation sign. (`edgeSign_zero_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L52)).

**Flat rectangle integral vanishes.** Proved result. Under the stated hypotheses, the set integral over a rectangle of zero height is zero. (`flat_integral_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L64)).

**Corner moments respect reflection.** Proved result. Under the stated hypotheses, reflecting height and applying the derivative signs multiplies the corner moment by the scalar factor and reverses its height endpoint. (`cornerFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerFlip.lean#L73)).

### Breakdown.CertCell.CornerMatch

Tests the weak height derivative with piecewise linear tents to compare corner traces from adjacent height intervals. Matching follows from the trace identities and the stated weak regularity conditions. Appendix B: cell-system construction and finite certificate analysis.

**Tent combination for corner matching.** Definition. This defines the tent-weighted combination of the field and its first and mixed derivatives. (`tentCombination`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L13)).

**Weak height identity on the plane.** Proved result. Under the stated hypotheses, the height derivative of a test pairs with the field as the negative test pairing with its weak derivative. (`height_identity_full`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L19)).

**Tent-weighted integrability.** Proved result. Under the stated hypotheses, the product of the one-variable weights and the field is integrable on the rectangle. (`integrableOn_weight_tent`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L30)).

**Slope of the upper tent.** Proved result. Under the stated hypotheses, the tent slope on the upper half is the reciprocal negative height. (`tentSlope_upper`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L44)).

**Upper tent formula.** Proved result. Under the stated hypotheses, the upper tent is the affine function joining one at zero to zero at its endpoint. (`tentFn_upper`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L48)).

**Slope of the lower tent.** Proved result. Under the stated hypotheses, the tent slope on the lower half is the reciprocal positive height. (`tentSlope_lower`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L52)).

**Lower tent formula.** Proved result. Under the stated hypotheses, the lower tent is the affine function joining zero at its endpoint to one at zero. (`tentFn_lower`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L56)).

**Weak identity with a height tent.** Proved result. Under the stated hypotheses, a height tent can replace the smooth height test in the weak derivative identity. (`tent_height_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L60)).

**Tent derivative terms cancel.** Proved result. Under the stated hypotheses, the tent-slope and tent-weighted derivative integrals sum to zero. (`tent_weight_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L139)).

**Corner tent combination vanishes.** Proved result. Under the stated hypotheses, the radial test pairing with the corner tent combination is zero. (`tent_combination_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L152)).

**Corner moments match across height.** Proved result. Under the stated hypotheses, the weak derivative conditions make the corner moments with opposite auxiliary heights equal. (`cornerMatch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerMatch.lean#L211)).

### Breakdown.CertCell.CornerPointTrace

Develops weak radial and height differentiation for the rectangle moment defining a corner trace. It proves that the trace is independent of its permitted auxiliary radial and height endpoints. Appendix B: cell-system construction and finite certificate analysis.

**Weak derivative along a direction.** Proposition definition. The interface requires that the field has the specified distributional derivative against smooth compactly supported tests in the domain. (`WeakAlong`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L15)).

**Whole-plane weak identity.** Proved result. Under the stated hypotheses, the supported weak derivative identity may be written as a whole-plane integral. (`whole_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L19)).

**Swap second derivatives of a test.** Proved result. Under the stated hypotheses, the two iterated directional derivatives of the smooth test agree. (`second_swap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L30)).

**Recover the fourth weak derivative.** Proved result. Under the stated hypotheses, the three stated weak derivative identities imply the missing radial derivative identity for the height derivative. (`mixed_of_three`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L41)).

**Radial tent as a weak test.** Proved result. Under the stated hypotheses, the radial tent and its slope satisfy the weak derivative pairing identity. (`radial_tent`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L55)).

**Height tent as a weak test.** Proved result. Under the stated hypotheses, the height tent and its slope satisfy the weak derivative pairing identity. (`height_tent`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L132)).

**Corner term is integrable.** Proved result. Under the stated hypotheses, the corner term is integrable on the stated set. (`term_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L210)).

**Corner moment as a corner term.** Proved result. Under the stated hypotheses, the corner moment is the signed rectangle integral of the corner term. (`moment_eq_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L226)).

**Radial corner terms cancel locally.** Proved result. Under the stated hypotheses, the two-sided radial corner construction has zero rectangle integral. (`radial_zero_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L232)).

**Height corner terms cancel locally.** Proved result. Under the stated hypotheses, the two-sided height corner construction has zero rectangle integral. (`height_zero_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L323)).

**Move the auxiliary radial endpoint.** Proved result. Under the stated hypotheses, the corner moment is unchanged by the permitted change of auxiliary radial endpoint. (`radial_move`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L402)).

**Move the auxiliary height endpoint.** Proved result. Under the stated hypotheses, the corner moment is unchanged by the permitted change of auxiliary height endpoint. (`height_move`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L448)).

**Choose interior auxiliary endpoints.** Proved result. Under the stated hypotheses, the corner moment equals the version with the two specified interior auxiliary endpoints. (`corner_normal_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L494)).

**Corner traces ignore auxiliary ends.** Proved result. Under the stated hypotheses, the weak derivative conditions make the corner moment independent of its permitted auxiliary radial and height endpoints. (`cornerPointTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerPointTrace.lean#L532)).

### Breakdown.CertCell.CornerTrace

Separates the corner integrand into section traces and applies iterated integration. This identifies the rectangle-moment definition with the expected boundary-corner combination. Appendix B: cell-system construction and finite certificate analysis.

**Split the corner integrand.** Proved result. Under the stated hypotheses, the four corner terms rearrange into the two upper-trace integrands. (`cornerIntegrand_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerTrace.lean#L15)).

**Upper trace from a section integral.** Proved result. Under the stated hypotheses, the section integral equals the negative upper trace. (`sectionTrace_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerTrace.lean#L26)).

**Section trace integrand is integrable.** Proved result. Under the stated hypotheses, the affine combination defining the section trace is integrable on the height interval. (`sectionTrace_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerTrace.lean#L31)).

**Integrate a rectangle by sections.** Proved result. Under the stated hypotheses, the rectangle integral becomes a radial integral of the two upper traces. (`rectangle_iterated`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerTrace.lean#L37)).

**Corner trace from strip traces.** Proved result. Under the stated hypotheses, the corner moment is the oriented radial integral of the upper traces of the field and its radial derivative with their affine weights. (`cornerTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CornerTrace.lean#L83)).

### Breakdown.CertCell.CouplingGlobalLeaf

Proves the scalar completing-the-square estimate used to absorb coupling terms. It then combines local leaf bounds into the global coupling inequality. Appendix B: cell-system construction and finite certificate analysis.

**Complete a weighted square.** Proved result. Under the stated hypotheses, twice a product minus the reciprocal-weighted square is bounded by the weighted second square. (`twice_product_sub_square_div_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingGlobalLeaf.lean#L9)).

**Complete the global leaf square.** Proved result. Under the stated hypotheses, the mixed leaf term minus its reciprocal-weight square is bounded by the positive-weight square of the leaf variable. (`globalLeaf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingGlobalLeaf.lean#L17)).

### Breakdown.CertCell.CouplingInverseCredit

Converts an inverse matrix factorization into the real quadratic credit bound. The proof uses conjugate-transpose identities to justify the inverse-form calculation. Appendix B: cell-system construction and finite certificate analysis.

**Real symmetric matrix is Hermitian.** Proved result. Under the stated hypotheses, embedding the real symmetric matrix into complex entries gives a Hermitian matrix. (`real_map_conjTranspose_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseCredit.lean#L16)).

**Real inverse survives complex casting.** Proved result. Under the stated hypotheses, the complex embeddings of the matrix and its real inverse multiply to the identity. (`real_map_mul_inv_eq_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseCredit.lean#L23)).

**Dual pairing bounds inverse credit.** Proved result. Under the stated hypotheses, a uniform squared dual-pairing bound gives the same upper bound for the inverse positive-definite quadratic form. (`inverseFormCredit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseCredit.lean#L36)).

### Breakdown.CertCell.CouplingInverseFactor

Establishes real and complex matrix identities for the factored inverse coupling form. These yield the completing-the-square lower bound for the inverse factor. Appendix B: cell-system construction and finite certificate analysis.

**Transpose becomes conjugate transpose.** Proved result. Under the stated hypotheses, embedding a real transpose equals the conjugate transpose of the embedded matrix. (`map_real_transpose`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L16)).

**Complex casting preserves products.** Proved result. Under the stated hypotheses, embedding a real matrix product gives the product of the embedded matrices. (`map_real_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L21)).

**Real part of pairing is symmetric.** Proved result. Under the stated hypotheses, the two reversed Hermitian pairings have equal real parts. (`re_dot_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L26)).

**Move a conjugate transpose.** Proved result. Under the stated hypotheses, a conjugate transpose can move from the matrix action to the first vector in the Hermitian pairing. (`dot_conjTranspose_mulVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L33)).

**Real positive form stays nonnegative.** Proved result. Under the stated hypotheses, the real part of the complexified positive form is nonnegative. (`re_quad_nonneg_of_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L37)).

**Inverse form bounds a cross term.** Proved result. Under the stated hypotheses, the inverse quadratic form bounds the cross term after subtracting the original quadratic penalty. (`cross_bound_inverse`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L52)).

**Real scaling of a pairing.** Proved result. Under the stated hypotheses, a real scalar factors out of the real Hermitian pairing. (`real_smul_dot_re`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L65)).

**Real scaling of a quadratic form.** Proved result. Under the stated hypotheses, scaling a vector by a real scalar scales its quadratic value by the scalar square. (`real_smul_quad_re`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L70)).

**Inverse form from a factor bound.** Proved result. Under the stated hypotheses, the inverse quadratic form is at least the squared norm of the factor applied to the vector divided by one plus the factorization error. (`inverseFormFactor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingInverseFactor.lean#L78)).

### Breakdown.CertCell.CouplingStatements

Defines source, cross and inverse coupling forms together with their credit, share and port conditions. The interfaces state the finite inequalities that combine into the global leaf bound. Appendix B: cell-system construction and finite certificate analysis.

**Cross form.** Definition. This defines the real Hermitian pairing between one vector and the matrix image of another. (`crossForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L15)).

**Diagonal sign matrix.** Definition. This defines the diagonal complex matrix whose entries are the given real signs. (`signDiag`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L18)).

**Source form.** Definition. This defines the total source quadratic form, its linear coupling and inverse-weighted corrections. (`sourceForm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L21)).

**Source bracket.** Definition. This defines one share of the source form with its port contribution and inverse-weighted correction. (`sourceBracket`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L26)).

**Source copies give a summed bound.** Interface. The interface requires that positive shares with total at most one and zero total port allow the separate source lower bounds to be summed. (`SourceCopiesHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L31)). No named provider or direct consumer of this interface was found in the library.

**Split a positive port form.** Interface. The interface requires that positivity of the combined matrix gives the stated cross-term lower bound after port splitting. (`PortSplitHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L41)). No named provider or direct consumer of this interface was found in the library.

**Split a squared sum.** Interface. The interface requires that positive shares with total at most one and cancelling ports bound the negative squared norm of the sum. (`SumSplitHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L47)). No named provider or direct consumer of this interface was found in the library.

**Split rows with inverse forms.** Interface. The interface requires that the positive matrix and Schur-type conditions give the stated inverse-form row splitting inequality. (`RowSplitHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L53)). No named provider or direct consumer of this interface was found in the library.

**Share ports sum to zero.** Interface. The interface requires that shares summing to one make the constructed redistribution ports sum to zero. (`SharePortSumHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L61)). No named provider or direct consumer of this interface was found in the library.

**Plane partners cancel.** Interface. The interface requires that the signed partner involution cancels both the quadratic plane sum and the stated linear port sum. (`PlanePairCancelHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L65)). No named provider or direct consumer of this interface was found in the library.

**Inverse form credit interface.** Interface. The interface requires that a uniform squared dual-pairing bound gives the same upper bound for the inverse positive-definite quadratic form. (`InverseFormCreditHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L74)). Proof route: `Breakdown.CertCell.Coupling.inverseFormCredit`.

**Inverse factorization interface.** Interface. The interface requires that the inverse quadratic form is at least the squared norm of the factor applied to the vector divided by one plus the nonnegative factorization error. (`InverseFormFactorHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L79)). Proof route: `Breakdown.CertCell.Coupling.inverseFormFactor`.

**Quadratic pairing remainder.** Interface. The interface requires that a negative weighted square and its Gram penalty bound the real linear pairing from below. (`PairingSquareRemainderHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L84)). No named provider or direct consumer of this interface was found in the library.

**Global leaf interface.** Interface. The interface requires that the mixed leaf term minus its reciprocal-weight square is bounded by the positive-weight square of the leaf variable. (`GlobalLeafHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L90)). Proof route: `Breakdown.CertCell.Coupling.globalLeaf`.

**Single factor lower bound.** Interface. The interface requires that the positive approximate factorization bounds the quadratic form plus its linear term from below. (`SingleFactorBoundHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CouplingStatements.lean#L95)). No named provider or direct consumer of this interface was found in the library.

### Breakdown.CertCell.CreditEvalLinks

Matches label modes with time harmonics and identifies patch credit data with the actual field traces. It also verifies the zero-field gradient and pressure cases needed by the evaluation interface. Appendix B: cell-system construction and finite certificate analysis.

**Recover a label from its time index.** Proved result. Under the stated hypotheses, the harmonic mode reconstructed from the label time and azimuthal index equals the original label. (`mode_of_labelTime`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalLinks.lean#L14)).

**Label time has the required parity.** Proved result. Under the stated hypotheses, the sum of the azimuthal label and its time label is even. (`even_label_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalLinks.lean#L23)).

**Zero field is a gradient.** Proved result. Under the stated hypotheses, the zero vector field is a gradient field. (`zero_isGradientField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalLinks.lean#L27)).

**Zero pressure is periodic.** Proved result. Under the stated hypotheses, the zero pressure field satisfies the periodic pressure condition. (`zero_isPeriodicPressure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalLinks.lean#L30)).

**Side velocity ignores pressure.** Proved result. Under the stated hypotheses, side velocity data are independent of the pressure-gradient input. (`sideVelocity_pressure_free`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalLinks.lean#L43)).

**Strip moment ignores auxiliary height.** Proved result. Under the stated hypotheses, the indicated axial velocity strip moment is independent of the positive auxiliary height. (`strip_height_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalLinks.lean#L52)).

**Credit data match field evaluations.** Proved result. Under the stated hypotheses, valid credit evaluation data equal the patch data computed from the velocity and gradient fields. (`creditEvalMatches`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalLinks.lean#L76)).

### Breakdown.CertCell.CreditEvalStatements

Defines the credit data extracted from a field on a patch. Its interfaces require this data to match the certificate entries and bound the sum of leaf credits. Appendix B: cell-system construction and finite certificate analysis.

**Credit data from cell states.** Definition. This defines patch credit coordinates by selecting entries of their owning cell states. (`creditData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalStatements.lean#L20)).

**Credit evaluation interface.** Interface. The interface requires that valid credit evaluation data equal the patch's analytic field data. (`CreditEvalMatchesHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalStatements.lean#L27)). Proof route: `Breakdown.CertCell.creditEvalMatches_closed`, `Breakdown.CertCell.CreditEval.creditEvalMatches`.

**Credit leaves fit their shares.** Interface. The interface requires that twice the sum of the quadratic credit-patch values is at most the sum of the cell credit shares. (`CreditLeavesBoundHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditEvalStatements.lean#L33)). Proof route: `Breakdown.CertCell.creditLeavesBound_closed`, `Breakdown.CertCell.creditLeavesBound`.

### Breakdown.CertCell.CreditLeavesBound

Bounds an integral over a covered region by the sum over its leaf intersections. Applied to the patch credit estimate, this produces the stated bound for all covered leaves. Appendix B: cell-system construction and finite certificate analysis.

**Integrate over a finite cover.** Proved result. Under the stated hypotheses, a nonnegative integral over the covered set is at most the sum of the integrals over its pieces. (`setIntegral_le_sum_inter_of_cover`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditLeavesBound.lean#L14)).

**Sum of leaf credits is bounded.** Proved result. Under the stated hypotheses, twice the sum of the quadratic credit-patch values is at most the sum of the cell credit shares. (`creditLeavesBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditLeavesBound.lean#L41)).

### Breakdown.CertCell.CreditPatchBound

Packages patch data as a valid certificate entry and evaluates the zero correction forms. The final patch bound supplies the local estimate used when leaf credits are summed. Appendix B: cell-system construction and finite certificate analysis.

**Patch entry without a factor.** Definition. `Breakdown.CertCell.Bridge.Internal.CreditPatchBound.toEntry` constructs a patch entry with the given test data and zero factor and credit data. (`toEntry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditPatchBound.lean#L12)).

**Zero complex form.** Proved result. Under the stated hypotheses, the zero complex matrix has zero quadratic value. (`quadForm_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditPatchBound.lean#L34)).

**Zero real form.** Proved result. Under the stated hypotheses, the zero real matrix has zero quadratic value. (`realQuadForm_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditPatchBound.lean#L38)).

**Zero-factor patch is valid.** Proved result. Under the stated hypotheses, the constructed patch entry satisfies the patch validity conditions. (`toEntry_valid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditPatchBound.lean#L42)).

**Patch credit is charged to velocity.** Proved result. Under the stated hypotheses, the patch credit form is bounded by the radius-weighted integral of its charge times the reflected velocity-mode squared norm. (`creditPatchBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CreditPatchBound.lean#L80)).

### Breakdown.CertCell.CrossWaveBound

Builds a finite Fourier-grid argument for resonant triples of time harmonics. Exact phase orthogonality and Young-type estimates bound the resulting cross-wave contribution. Appendix B: cell-system construction and finite certificate analysis.

**Finite-grid phase.** Definition. This defines the complex exponential sampled at a finite angular grid point. (`gridPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L13)).

**Multiply grid phases.** Proved result. Under the stated hypotheses, multiplying two grid phases adds their frequency indices. (`gridPhase_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L16)).

**Conjugate a grid phase.** Proved result. Under the stated hypotheses, complex conjugation negates the grid frequency. (`gridPhase_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L24)).

**Finite-grid orthogonality.** Proved result. Under the stated hypotheses, the grid sum is the grid size for frequency zero and zero for the permitted nonzero frequencies. (`gridPhase_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L32)).

**Azimuthal phase on the grid.** Proved result. Under the stated hypotheses, sampling the azimuthal phase at the specified angle gives the grid phase. (`azimuthPhase_grid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L77)).

**Curl is additive.** Proved result. Under the stated hypotheses, the algebraic curl of two gradient arrays adds componentwise. (`curlOfGrad_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L86)).

**Curl respects complex scaling.** Proved result. Under the stated hypotheses, a complex scalar factors out of the algebraic curl. (`curlOfGrad_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L90)).

**Curl gradient is additive.** Proved result. Under the stated hypotheses, the algebraic curl gradient adds across second-derivative arrays. (`curlGradOfSecondDeriv_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L95)).

**Curl gradient respects scaling.** Proved result. Under the stated hypotheses, a complex scalar factors out of the algebraic curl gradient. (`curlGradOfSecondDeriv_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L99)).

**Stretching is additive in the model.** Proved result. Under the stated hypotheses, adding the model derivative arrays adds the stretching bilinear values. (`stretchBilin_add_model`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L104)).

**Scale the stretching model.** Proved result. Under the stated hypotheses, scaling the model derivative arrays scales the stretching bilinear value. (`stretchBilin_smul_model`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L111)).

**Stretching is additive on the left.** Proved result. Under the stated hypotheses, adding the left perturbation data adds the stretching bilinear values. (`stretchBilin_add_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L118)).

**Scale the left stretching input.** Proved result. Under the stated hypotheses, scaling the left perturbation data scales the stretching bilinear value. (`stretchBilin_smul_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L125)).

**Stretching is additive on the right.** Proved result. Under the stated hypotheses, adding the right perturbation data adds the stretching bilinear values. (`stretchBilin_add_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L132)).

**Scale the right stretching input.** Proved result. Under the stated hypotheses, scaling the right perturbation data scales the stretching bilinear value. (`stretchBilin_smul_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L139)).

**Curl of a finite mode sum.** Proved result. Under the stated hypotheses, the algebraic curl of a finite weighted mode sum is the weighted sum of curls. (`curlOfGrad_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L146)).

**Curl gradient of a finite sum.** Proved result. Under the stated hypotheses, the curl gradient of a finite weighted sum is the corresponding sum of curl gradients. (`curlGradOfSecondDeriv_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L153)).

**Curl commutes with conjugation.** Proved result. Under the stated hypotheses, conjugating the gradient array conjugates its algebraic curl. (`curlOfGrad_star`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L161)).

**Conjugation preserves squared norm.** Proved result. Under the stated hypotheses, componentwise conjugation preserves the squared complex norm. (`cnormSq_star`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L165)).

**Squared complex norm is nonnegative.** Proved result. Under the stated hypotheses, the sum of squared component norms is nonnegative. (`cnormSq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L168)).

**Squared norm as a complex sum.** Proved result. Under the stated hypotheses, the real squared norm embedded in the complex numbers is the sum of each entry times its conjugate. (`cnormSq_ofReal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L171)).

**Grid mean of a complex square.** Proved result. Under the stated hypotheses, finite-grid orthogonality removes cross terms between the permitted distinct frequencies. (`grid_mean_sq_complex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L175)).

**Grid mean of squared norms.** Proved result. Under the stated hypotheses, the grid sum of the mode-sum squared norm is the grid size times the sum of mode squared norms. (`grid_mean_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L211)).

**Stretching linear in the model.** Definition. `Breakdown.CertCell.Bridge.tripleModelMap` packages the stretching triple as a complex linear map of its model input. (`tripleModelMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L222)).

**Stretching linear in the left input.** Definition. `Breakdown.CertCell.Bridge.tripleLeftMap` packages the stretching triple as a complex linear map of its left input. (`tripleLeftMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L233)).

**Stretching linear in the right input.** Definition. `Breakdown.CertCell.Bridge.tripleRightMap` packages the stretching triple as a complex linear map of its right input. (`tripleRightMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L244)).

**Expand the stretching triple.** Proved result. Under the stated hypotheses, the stretching triple of finite sums expands into the corresponding triple sum. (`stretchTriple_expand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L255)).

**Grid mean keeps resonant triples.** Proved result. Under the stated hypotheses, averaging the stretching triple over the grid keeps only frequencies satisfying the resonance equation. (`grid_mean_triple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L277)).

**Grid mean of cross charges.** Proved result. Under the stated hypotheses, the grid sum of cross charges is the grid size times the sum of separate mode charges. (`grid_mean_crossCharge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L303)).

**Reciprocal-weight product bound.** Proved result. Under the stated hypotheses, twice a product is bounded by the two reciprocal-weighted squares. (`twice_mul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L332)).

**Weighted pair estimate.** Proved result. Under the stated hypotheses, the stated mixed products are bounded by the two reciprocal-weighted quadratic charges. (`weighted_pair_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L339)).

**Conjugation preserves cross charge.** Proved result. Under the stated hypotheses, conjugating both mode arrays preserves the cross charge. (`crossCharge_star`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L354)).

**Combine the mean estimate.** Proved result. Under the stated hypotheses, twice the mean amplitude is bounded by the first weighted charge mean plus the reciprocal-weight second charge mean. (`mean_bound_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L359)).

**Cross-wave bound.** Proved result. Under the stated hypotheses, the cross-wave estimate follows from finite-grid averaging and the quadratic charges. (`crossWaveBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/CrossWaveBound.lean#L377)).

### Breakdown.CertCell.Defs

Introduces the label frequencies, scalar and Hessian fields, deactivation rule and class-weighted forms. It also defines the mean and negative stretching quantities used in the cell estimates. Appendix B: cell-system construction and finite certificate analysis.

**Time frequency of a label.** Definition. This defines the angular time frequency as two pi times the time index divided by the period. (`labelTimeFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L16)).

**Second derivative at a label.** Definition. This defines the second-derivative mode for the label on the meridian plane. (`labelHess`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L18)).

**Scalar mode at a label.** Definition. This defines the time and angular average of the scalar field for the label. (`labelScalar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L22)).

**Deactivated label.** Proposition definition. The interface requires that the label belongs to neither the resolved set nor the band set of the cell. (`IsDeactivated`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L33)).

**Cell or exterior region.** Definition. `Breakdown.CertCell.CellMesh.regionOf` selects the exterior for no cell and the cell rectangle for a specified cell. (`regionOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L35)).

**Class of a label.** Definition. `Breakdown.CertCell.classOfLabel` assigns the harmonic represented by the label to its mode class. (`classOfLabel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L53)).

**Strain weight of a label.** Definition. `Breakdown.CertCell.strainWeightOf` selects the strain weight of the label's mode class. (`strainWeightOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L56)).

**Vorticity weight of a label.** Definition. `Breakdown.CertCell.vorticityWeightOf` selects the vorticity weight of the label's mode class. (`vorticityWeightOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L59)).

**Fixed model second derivative.** Definition. `Breakdown.CertCell.CellLayerData.modelHess` uses the given second-derivative field independently of the parameter vector. (`modelHess`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L66)).

**Actuator from cell values.** Definition. `Breakdown.CertCell.CellLayerData.actuatorField` builds the actuator field from its cell values and azimuthal order. (`actuatorField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L68)).

**Class of the zero mode.** Definition. `Breakdown.CertCell.CellLayerData.baseClass` selects the class containing the zero harmonic. (`baseClass`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L71)).

**Multiplier right-hand side.** Definition. This defines the second-derivative pairing and the weighted curl and velocity mode pairings. (`multiplierRight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L75)).

**Mean stretching density.** Definition. This defines the normalized time and angular mean of the stretching form at a meridian point. (`meanStretch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L89)).

**Negative stretching mean.** Definition. This defines the nonnegative integral of the negative stretching density over time and angle. (`stretchNegMean`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L93)).

**Negative part of the form.** Definition. This defines the sum of the negative mode contributions and negative stretching contribution. (`formNeg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L97)).

**Scalar correction to the form.** Definition. This defines the multiplier, row and pin correction terms in the scalar part of the form. (`formScalar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L102)).

**Five-coefficient mode value.** Definition. `Breakdown.CertCell.ModeCoefficients.value` evaluates the five mode coefficients on the corresponding squared amplitudes. (`value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L112)).

**Mode density equals its coefficients.** Proved result. Under the stated hypotheses, the mode density is the five-coefficient quadratic value. (`modeDensity_eq_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/Defs.lean#L115)).

### Breakdown.CertCell.EnergyAeCongr

Shows that local pairings, test suprema, projections and energy values are unchanged by almost-everywhere equality on the integration domain. These transport lemmas allow weak fields to be replaced by convenient representatives. Appendix B: cell-system construction and finite certificate analysis.

**Pairing respects a.e. equality.** Proved result. Under the stated hypotheses, replacing the field by an almost-everywhere equal field on the cell preserves the test pairing. (`pairOn_congr_restrict_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyAeCongr.lean#L15)).

**Test supremum respects a.e. equality.** Proved result. Under the stated hypotheses, the test supremum depends only on the field's almost-everywhere class on the cell. (`testSupremum_congr_restrict_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyAeCongr.lean#L23)).

**Equivalent predicates choose equally.** Proved result. Under the stated hypotheses, pointwise equivalent predicates give the same chosen witness or default. (`dite_choose_congr_of_iff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyAeCongr.lean#L29)).

**Projection respects a.e. equality.** Proved result. Under the stated hypotheses, the polynomial projection is unchanged by almost-everywhere equality on the cell. (`proj_congr_restrict_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyAeCongr.lean#L37)).

**Energies respect a.e. equality.** Proved result. Under the stated hypotheses, the radial, height and angular energies are unchanged by almost-everywhere equal inputs. (`energyAeCongr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyAeCongr.lean#L46)).

### Breakdown.CertCell.EnergyLeafBound

Evaluates sums and block-diagonal quadratic forms and applies the resulting identities to a leaf's energy matrix. This converts the matrix lower bound into the leaf energy estimate. Appendix B: cell-system construction and finite certificate analysis.

**Energy form of a sum.** Proved result. Under the stated hypotheses, the real complex quadratic value distributes over matrix addition. (`value_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyLeafBound.lean#L15)).

**Embedding a form in a zero block.** Proved result. Under the stated hypotheses, adjoining zero blocks preserves the original quadratic value. (`value_fromBlocks`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyLeafBound.lean#L20)).

**Action of a block diagonal matrix.** Proved result. Under the stated hypotheses, each output block is the corresponding matrix applied to its input block. (`mulVec_blockDiagonal'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyLeafBound.lean#L29)).

**Block diagonal quadratic value.** Proved result. Under the stated hypotheses, the block diagonal quadratic form is the sum of the block quadratic values. (`value_blockDiagonal'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyLeafBound.lean#L40)).

**Line weight times radial factor.** Proved result. Under the stated hypotheses, the product of the line weight and normalized radial factor is the radius. (`lineWeight_mul_rHat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyLeafBound.lean#L52)).

**Resolved mode block is bounded.** Proved result. Under the stated hypotheses, the mode block value is bounded by the retained Hessian, curl-Hessian and low-mode integrals. (`modeBlock_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyLeafBound.lean#L67)).

### Breakdown.CertCell.EnergyLeafBoundForm

States the bridge between the finite harmonic energy form and the analytic energy of the lifted field. The statement records the cell, label and admissibility hypotheses needed for that equality. Appendix B: cell-system construction and finite certificate analysis.

**Harmonic energy form interface.** Interface. The interface requires that the harmonic energy form equals the weighted label strain and vorticity energies. (`HarmonicEnergyFormValueStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/EnergyLeafBoundForm.lean#L13)). Proof route: `Breakdown.CertCell.CellCalculus.harmonicEnergyFormValue_of`, `Breakdown.CertCell.CellCalculus.harmonicEnergyFormValue_of_lift`, `Breakdown.CertCell.CellCalculus.harmonicEnergyFormValue`.

### Breakdown.CertCell.FormNegativeFinite

Proves measurability and integrability of the negative stretching contribution using rotational orbits and a majorant. The resulting finiteness statement supplies the analytic side of the negative-form estimate. Appendix B: cell-system construction and finite certificate analysis.

**Measurable majorant with equal integral.** Proved result. Under the stated hypotheses, a nonnegative function has a measurable majorant with the same lower integral. (`measurable_majorant`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L21)).

**Rotation is two-pi periodic.** Proved result. Under the stated hypotheses, adding two pi to the rotation angle leaves the point unchanged. (`axialRot_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L41)).

**The time-orbit map is measurable.** Proved result. Under the stated hypotheses, the map from meridian, time and angle to the spacetime orbit is measurable. (`measurable_orbitMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L45)).

**Negative stretching is finite.** Proved result. Under the stated hypotheses, the weighted half-plane lower integral of the negative stretching mean is finite. (`stretchNeg_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L54)).

**Squared complex norm is continuous.** Proved result. Under the stated hypotheses, the squared norm on a finite complex coordinate space is continuous. (`continuous_cnormSq_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L113)).

**Squared complex norm is nonnegative.** Proved result. Under the stated hypotheses, the squared norm on the finite complex coordinate space is nonnegative. (`cnormSq_nonneg_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L117)).

**Curl-gradient square bound.** Proved result. Under the stated hypotheses, the squared curl-gradient norm is at most twice the second-derivative array square. (`cnormSq_curlGradSecond_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L121)).

**Bound the negative mode value.** Proved result. Under the stated hypotheses, the negative five-coefficient value is bounded by the stated absolute coefficient bound and weighted squares. (`neg_value_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L134)).

**Negative mode sum is finite.** Proved result. Under the stated hypotheses, the sum of lower integrals of negative label densities is finite. (`modes_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L153)).

**Rotation respects real scaling.** Proved result. Under the stated hypotheses, rotation of a scaled vector scales each rotated coordinate. (`axialRot_smul_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L246)).

**Constant factors leave mode averages.** Proved result. Under the stated hypotheses, a real constant factors out of the mode average. (`modeAverage_const_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L251)).

**Inverse radius leaves velocity modes.** Proved result. Under the stated hypotheses, multiplying velocity by inverse radius multiplies each mode by inverse radius. (`modeVel_inv_norm_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L256)).

**Scale a squared complex norm.** Proved result. Under the stated hypotheses, multiplying all entries by a real constant multiplies the squared norm by its square. (`cnormSq_const_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L263)).

**Norm on the meridian plane.** Proved result. Under the stated hypotheses, the squared spatial norm of a meridian point is radius squared plus height squared. (`norm_planePoint_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L270)).

**Inverse-radius velocity sum is finite.** Proved result. Under the stated hypotheses, the summed weighted mode squares divided by radius squared plus height squared have finite lower integral. (`velocity_inverse_sum_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L274)).

**Gradient mode square sum is finite.** Proved result. Under the stated hypotheses, the weighted half-plane sum of gradient mode squares has finite lower integral. (`gradient_sum_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L304)).

**Second-derivative mode sum is finite.** Proved result. Under the stated hypotheses, the weighted half-plane sum of second-derivative mode squares has finite lower integral. (`secondDeriv_sum_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeFinite.lean#L312)).

### Breakdown.CertCell.FormNegativeInverseSquare

Establishes a cylindrical inverse-square estimate for square-integrable gradient data. The perturbation bound controls the weighted field term used in the negative-form argument. Appendix B: cell-system construction and finite certificate analysis.

**Matrix square is nonnegative.** Proved result. Under the stated hypotheses, the matrix column-square sum is nonnegative. (`matSq_nonneg_slice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeInverseSquare.lean#L14)).

**Matrix square is continuous.** Proved result. Under the stated hypotheses, the matrix column-square sum is continuous. (`matSq_continuous_slice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeInverseSquare.lean#L17)).

**Spatial inverse-square bound.** Proved result. Under the stated hypotheses, the inverse-radius velocity square is bounded by four times the gradient square integral. (`slice_inverseSquare_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeInverseSquare.lean#L21)).

**Periodic inverse-square bound.** Proved result. Under the stated hypotheses, the period integral of velocity square divided by radius squared is bounded by four times the period gradient square. (`perturbation_inverseSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeInverseSquare.lean#L53)).

### Breakdown.CertCell.FormNegativeSquareSum

Bounds finite sums of harmonic-mode squares by the orbit integral. The time and angular estimates combine into the square-sum control needed for the negative part of the form. Appendix B: cell-system construction and finite certificate analysis.

**Orbit Fourier coefficients.** Definition. This defines the componentwise time and angular Fourier coefficients of the transformed field. (`orbitModes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L18)).

**Label harmonics are injective.** Proved result. Under the stated hypotheses, positive azimuthal order makes the label-to-harmonic map injective. (`labelHarmonic_injective_of_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L22)).

**Move a periodic integration interval.** Proved result. Under the stated hypotheses, the lower integral of a periodic function is unchanged between the two stated angular periods. (`lintegral_Icc_eq_Ioo_of_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L31)).

**Torus square-sum estimate.** Proved result. Under the stated hypotheses, the sum of squared torus Fourier coefficients is bounded by the normalized square integral. (`torus_sum_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L41)).

**The spacetime orbit is continuous.** Proved result. Under the stated hypotheses, the time and rotated-position orbit map is continuous. (`continuous_orbitPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L54)).

**Pointwise Fourier square-sum estimate.** Proved result. Under the stated hypotheses, the sum of squared orbit coefficients is bounded by the normalized time and angular square integral. (`point_sum_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L59)).

**Orbit modes respect a.e. fields.** Proved result. Under the stated hypotheses, almost-everywhere equal fields have equal orbit modes almost everywhere on the half-plane. (`ae_orbitModes_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L98)).

**Orbit squared norms are measurable.** Proved result. Under the stated hypotheses, the squared orbit-mode norm is almost everywhere measurable on the half-plane. (`aemeasurable_orbitModes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L116)).

**Integrated amplitude square-sum bound.** Proved result. Under the stated hypotheses, the weighted half-plane sum of mode amplitudes is bounded by the normalized spacetime energy. (`amplitude_sum_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L128)).

**Rotated coordinates preserve norm.** Proved result. Under the stated hypotheses, the sum of squared rotated coordinates equals the squared vector norm. (`sum_sq_rotCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L202)).

**Rotated coordinates are continuous.** Proved result. Under the stated hypotheses, a rotated coordinate is continuous jointly in angle and vector. (`continuous_rotCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L207)).

**Column squares through an adjoint.** Proved result. Under the stated hypotheses, the sum of squared images of an orthonormal basis equals the corresponding adjoint column sum. (`sum_sq_apply_basis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L211)).

**An isometry preserves column squares.** Proved result. Under the stated hypotheses, applying an isometry to the input basis preserves the matrix square. (`sum_sq_apply_isometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L223)).

**Rotated gradient square.** Proved result. Under the stated hypotheses, the sum of squared rotated gradient coordinates equals the matrix square. (`sum_sq_rotGradCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L232)).

**Rotated second-derivative square.** Proved result. Under the stated hypotheses, the sum of squared rotated second-derivative coordinates equals the second-derivative square. (`sum_sq_rotSecondDerivCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L240)).

**Velocity label square-sum bound.** Proved result. Under the stated hypotheses, the weighted label velocity square sum is bounded by the normalized period velocity energy. (`labelAmplitude_sum_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L265)).

**Gradient label square-sum bound.** Proved result. Under the stated hypotheses, the weighted label gradient square sum is bounded by the normalized period gradient energy. (`labelGradAmplitude_sum_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L282)).

**Second-derivative label square sum.** Proved result. Under the stated hypotheses, the weighted label second-derivative square sum is bounded by the normalized period second-derivative energy. (`labelSecondDerivAmplitude_sum_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/FormNegativeSquareSum.lean#L301)).

### Breakdown.CertCell.GaugeKeyConj

Tracks complex conjugation through harmonic profiles, pressure modes, potentials and gauge keys. It proves the conjugation identities while keeping the additive freedom of a chosen pressure potential explicit. Appendix B: cell-system construction and finite certificate analysis.

**Cosine ignores frequency sign.** Proved result. Under the stated hypotheses, the cosine coefficient is unchanged when the time frequency is negated. (`harmonicCos_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L18)).

**Sine changes with frequency sign.** Proved result. Under the stated hypotheses, negating the time frequency negates the sine coefficient. (`harmonicSin_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L23)).

**Cosine tuple ignores frequency sign.** Proved result. Under the stated hypotheses, the cosine field tuple is unchanged by frequency negation. (`cosTuple_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L28)).

**Sine tuple changes sign.** Proved result. Under the stated hypotheses, negating frequency negates the sine field tuple. (`sinTuple_negFreq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L33)).

**Frame coordinates preserve negation.** Proved result. Under the stated hypotheses, negating a vector negates its frame coordinates. (`frameVec_negVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L38)).

**Velocity modes preserve negation.** Proved result. Under the stated hypotheses, negating the velocity field negates its angular mode. (`modeVec_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L42)).

**Gradient modes preserve negation.** Proved result. Under the stated hypotheses, negating the gradient field negates its angular mode. (`modeMat_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L47)).

**Second modes preserve negation.** Proved result. Under the stated hypotheses, negating the second-derivative field negates its angular mode. (`modeThird_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L53)).

**Radial moments preserve negation.** Proved result. Under the stated hypotheses, negating both radial strip inputs negates the strip moment. (`radialStripMoment_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L59)).

**Height moments preserve negation.** Proved result. Under the stated hypotheses, negating both height strip inputs negates the strip moment. (`heightStripMoment_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L68)).

**Corner moments preserve negation.** Proved result. Under the stated hypotheses, negating the four corner inputs negates the corner moment. (`cornerMoment_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L77)).

**Segment moments preserve negation.** Proved result. Under the stated hypotheses, negating the field and derivative inputs negates the segment moment. (`moment_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L86)).

**Moments respect a.e. data.** Proved result. Under the stated hypotheses, almost-everywhere equality of the field input preserves the segment moment. (`moment_congr_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L93)).

**Layout velocity preserves negation.** Proved result. Under the stated hypotheses, negating the field tuple negates its layout velocity mode. (`velMode_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L106)).

**Layout gradient preserves negation.** Proved result. Under the stated hypotheses, negating the field tuple negates its layout gradient mode. (`gradModeOf_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L110)).

**Layout second mode preserves negation.** Proved result. Under the stated hypotheses, negating the field tuple negates its layout second-derivative mode. (`secondModeOf_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L114)).

**Pressure gradient preserves negation.** Proved result. Under the stated hypotheses, negating the field tuple negates its pressure-gradient mode. (`pressureGradMode_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L118)).

**Negating a potential.** Proved result. Under the stated hypotheses, the negative potential represents the negative gradient field. (`isPotentialOf_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L125)).

**Potential paired with a test derivative.** Proved result. Under the stated hypotheses, the potential times the compactly supported test derivative is integrable. (`test_mul_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L133)).

**Potentials differ by a constant.** Proved result. Under the stated hypotheses, two potentials of the same field differ almost everywhere by a constant. (`potential_unique`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L141)).

**Chosen potential represents its field.** Proved result. Under the stated hypotheses, the chosen potential represents the field whenever a potential exists. (`potentialOf_spec_of_exists`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L157)).

**Default potential when none exists.** Proved result. Under the stated hypotheses, the chosen potential is zero if the field has no potential. (`potentialOf_of_not_exists`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L163)).

**Normalized potential under negation.** Proved result. Under the stated hypotheses, the normalized potential of the negative field is almost everywhere the negative normalized potential. (`headPotential_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L168)).

**Pressure modes under negation.** Proved result. Under the stated hypotheses, almost-everywhere negation of potentials negates their pressure modes almost everywhere. (`presMode_ae_negPot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L200)).

**Head pressure under negation.** Proved result. Under the stated hypotheses, negating the field tuple negates head pressure almost everywhere. (`headPressure_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L216)).

**Skeleton keys preserve negation.** Proved result. Under the stated hypotheses, negating the field tuple negates its skeleton-key value. (`keyValue_negField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L221)).

**Zero velocity mode is real.** Proved result. Under the stated hypotheses, the zero angular velocity mode equals its complex conjugate. (`velMode_zero_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L244)).

**Zero gradient mode is real.** Proved result. Under the stated hypotheses, the zero angular gradient mode equals its complex conjugate. (`gradModeOf_zero_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L249)).

**Zero second mode is real.** Proved result. Under the stated hypotheses, the zero angular second-derivative mode equals its complex conjugate. (`secondModeOf_zero_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L254)).

**Zero pressure-gradient mode is real.** Proved result. Under the stated hypotheses, the zero angular pressure-gradient mode equals its complex conjugate. (`pressureGradMode_zero_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L260)).

**Conjugation reverses pressure mode.** Proved result. Under the stated hypotheses, conjugating a pressure mode negates its angular frequency. (`presMode_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L266)).

**Zero head-pressure mode is real.** Proved result. Under the stated hypotheses, the zero angular head-pressure mode equals its complex conjugate. (`headPressure_zero_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L271)).

**Zero-mode key value is real.** Proved result. Under the stated hypotheses, a skeleton key of angular mode zero has a real value. (`keyValue_conj_of_modeZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L276)).

**Key harmonic under frequency reversal.** Proved result. Under the stated hypotheses, reversing time frequency conjugates a skeleton key of angular mode zero. (`keyHarmonic_negFreq_eq_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L308)).

**Zero-mode keys respect conjugation.** Proved result. Under the stated hypotheses, reversing the time frequency conjugates each key harmonic whose angular mode is zero. (`fieldKeyConj_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L322)).

**Gauge coefficients respect conjugation.** Proved result. Under the stated hypotheses, the field gauge coefficient of the conjugate class is the complex conjugate of the original coefficient. (`fieldGaugeConj_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyConj.lean#L325)).

### Breakdown.CertCell.GaugeKeyDefs

Defines the inverse gauge matrix used to recover coefficients from gauge-key values. Its algebraic properties are established in the companion gauge files. Appendix B: cell-system construction and finite certificate analysis.

**Weighted inverse gauge matrix.** Definition. This defines the complex gauge inverse by dividing the incidence inverse by the deleted-key weight. (`inverse`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyDefs.lean#L16)).

### Breakdown.CertCell.GaugeKeyRealLabel

Proves that zero-frequency label data, pressure modes and gauge keys are real. The pressure-potential argument first removes its almost-everywhere constant freedom by normalization. Appendix B: cell-system construction and finite certificate analysis.

**Conjugation reverses pressure mode.** Proved result. Under the stated hypotheses, conjugating a real potential's pressure mode reverses its angular frequency. (`conj_presMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L18)).

**Zero velocity mode is real.** Proved result. Under the stated hypotheses, the zero angular velocity mode is fixed by conjugation. (`velMode_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L27)).

**Zero gradient mode is real.** Proved result. Under the stated hypotheses, the zero angular gradient mode is fixed by conjugation. (`gradModeOf_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L32)).

**Zero second mode is real.** Proved result. Under the stated hypotheses, the zero angular second-derivative mode is fixed by conjugation. (`secondModeOf_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L37)).

**Zero pressure-gradient mode is real.** Proved result. Under the stated hypotheses, the zero angular pressure-gradient mode is fixed by conjugation. (`pressureGradMode_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L43)).

**Zero head-pressure mode is real.** Proved result. Under the stated hypotheses, the zero angular head-pressure mode is fixed by conjugation. (`headPressure_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L49)).

**Zero-mode key value is real.** Proved result. Under the stated hypotheses, the specified zero-mode skeleton key is fixed by conjugation. (`keyValue_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L54)).

**Zero-frequency sine vanishes.** Proved result. Under the stated hypotheses, the sine coefficient at time frequency zero vanishes. (`harmonicSin_zero_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L87)).

**Zero-frequency sine tuple vanishes.** Proved result. Under the stated hypotheses, the sine field tuple at frequency zero is the zero tuple. (`sinTuple_zero_label`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L92)).

**Zero field is a gradient.** Proved result. Under the stated hypotheses, the zero field satisfies the gradient-field condition. (`zero_gradientField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L97)).

**Moment of zero data vanishes.** Proved result. Under the stated hypotheses, the segment moment of zero field and derivative data is zero. (`moment_of_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L106)).

**Moment respects a.e. equality.** Proved result. Under the stated hypotheses, almost-everywhere equal field data give equal segment moments. (`moment_ae_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L111)).

**Average of a constant potential.** Proved result. Under the stated hypotheses, the unit-ball mean of the chosen zero-field potential is its almost-everywhere constant value. (`ballMean_potential_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L121)).

**Head pressure of zero data vanishes.** Proved result. Under the stated hypotheses, head pressure of the zero tuple vanishes almost everywhere. (`headPressure_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L126)).

**Velocity mode of zero data.** Proved result. Under the stated hypotheses, the zero tuple has zero velocity modes. (`velMode_of_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L149)).

**Gradient mode of zero data.** Proved result. Under the stated hypotheses, the zero tuple has zero gradient modes. (`gradModeOf_of_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L154)).

**Second mode of zero data.** Proved result. Under the stated hypotheses, the zero tuple has zero second-derivative modes. (`secondModeOf_of_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L159)).

**Pressure mode of zero data.** Proved result. Under the stated hypotheses, the zero tuple has zero pressure-gradient modes. (`pressureGradMode_of_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L164)).

**Key value of zero data.** Proved result. Under the stated hypotheses, every skeleton-key value of the zero tuple vanishes. (`keyValue_of_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L169)).

**Zero-label key has no imaginary part.** Proved result. Under the stated hypotheses, the zero-time key harmonic of angular mode zero has zero imaginary part. (`keyHarmonic_label_zero_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L193)).

**Zero-frequency keys are real.** Proved result. Under the stated hypotheses, keys with zero angular mode and zero time frequency have zero imaginary part. (`fieldRealLabelZero_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyRealLabel.lean#L205)).

### Breakdown.CertCell.GaugeKeyStatements

Defines gauge-key states and the hypotheses required to control them. The interfaces state conjugation, real-label, plane-pair and coefficient-recovery properties. Appendix B: cell-system construction and finite certificate analysis.

**Field hypotheses for gauge keys.** Proposition definition. The interface requires that the parameter, symmetry, perturbation, periodic pressure and pressure-reflection conditions hold. (`fieldHyp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L17)).

**Gauge-adjusted key state.** Definition. This defines the field key harmonic with the sum of its gauge-direction corrections. (`keyState`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L33)).

**A key part is covered.** Proposition definition. The interface requires that the real or imaginary key part is stored in the skeleton or belongs to the omitted set. (`KeyPartCovered`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L37)).

**Gauge coefficients conjugate.** Interface. The interface requires that the gauge coefficient of a conjugate class is the conjugate of the original coefficient. (`GaugeConjHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L40)). Proof route: `Breakdown.CertCell.TreeEntry.gaugeConj_of`.

**Deleted gauge keys vanish.** Proposition definition. The interface requires that the gauge-adjusted state vanishes at every deleted key. (`DeletedPartZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L44)).

**Negating a label negates its time.** Proved result. Under the stated hypotheses, the time index of a negated label is the negative time index. (`labelTime_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L48)).

**Gauge value as an inverse shift.** Proved result. Under the stated hypotheses, the gauge value is the prescribed inverse-matrix shift of the deleted field keys. (`gaugeValue_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L51)).

**Gauge shift deletes the chosen keys.** Proved result. Under the stated hypotheses, the deleted-key zero interface follows from the indicated gauge data. (`deletedPartZero_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L55)).

**Field key conjugation requirement.** Interface. The interface requires that zero-angular-mode key harmonics conjugate when time frequency is reversed. (`FieldKeyConjHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L61)). Proof route: `Breakdown.CertCell.TreeEntry.fieldKeyConj_holds`.

**Real zero-label key requirement.** Proposition definition. The interface requires that zero-angular-mode keys at time frequency zero have zero imaginary part. (`FieldRealLabelZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L67)).

**Omitted plane parts vanish.** Proposition definition. The interface requires that the selected real or imaginary parts of omitted plane-pair keys vanish under the field hypotheses. (`FieldPlanePairZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L72)).

**Omitted odd plane keys vanish.** Proposition definition. The interface requires that omitted odd plane keys vanish under the field hypotheses. (`FieldPlaneOddZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L78)).

**Field gauge conjugation requirement.** Proposition definition. The interface requires that field gauge coefficients conjugate under the class involution. (`FieldGaugeConj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L84)).

**Deleted field keys vanish.** Proposition definition. The interface requires that the field gauge correction makes all designated deleted keys zero. (`FieldDeletedZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L89)).

**Omitted field key parts vanish.** Proposition definition. The interface requires that every omitted real or imaginary field key part vanishes under the field hypotheses. (`FieldKeyPartZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L94)).

**Field gauge conditions.** Interface. The interface requires that field gauge conjugation, deleted-key vanishing and omitted-part vanishing all hold. (`FieldGaugeHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L100)). Proof route: `Breakdown.CertCell.TreeEntry.fieldGaugeHolds_of`.

**Field gauge as an inverse shift.** Proved result. Under the stated hypotheses, the field gauge coefficient is the inverse-matrix shift of the deleted key harmonics. (`fieldGauge_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L105)).

**Deleted field keys are zero.** Proved result. Under the stated hypotheses, the gauge construction supplies the deleted field-key zero requirement. (`fieldDeletedZero_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L110)).

**Field gauge respects conjugation.** Proved result. Under the stated hypotheses, the indicated conjugation data supply the field gauge conjugation requirement. (`fieldGaugeConj_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L116)).

**Omitted field parts are zero.** Proved result. Under the stated hypotheses, the stated symmetry and gauge facts give omitted field-part vanishing. (`fieldKeyPartZero_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L128)).

**Assemble the field gauge conditions.** Proved result. Under the stated hypotheses, the field gauge obeys conjugation and makes every deleted key and omitted real or imaginary key part vanish. (`fieldGaugeHolds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L171)).

**Admissible gauge conjugation.** Proved result. Under the stated hypotheses, the gauge coefficient of an admissible tuple conjugates under the class involution. (`gaugeConj_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyStatements.lean#L176)).

### Breakdown.CertCell.GaugeKeyValues

Evaluates the gauge matrix against its inverse and proves the corresponding coefficient identities. These calculations identify the gauge-key values on the chosen basis fields. Appendix B: cell-system construction and finite certificate analysis.

**Real or imaginary key part.** Definition. `Breakdown.CertCell.GaugeKey.keyPart` selects the imaginary part when the flag is true and the real part otherwise. (`keyPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L11)).

**Gauge directions affect pressure keys.** Proved result. Under the stated hypotheses, a nonzero gauge direction has its class label and a zero-angular pressure-key shape. (`dir_support`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L17)).

**Gauge matrix times its inverse.** Proved result. Under the stated hypotheses, the gauge matrix multiplied by the chosen inverse is the identity. (`matrix_mul_inverse`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L26)).

**Deleted weights respect conjugation.** Proved result. Under the stated hypotheses, conjugate deleted-key classes have equal weights. (`conj_weight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L43)).

**Inverse respects conjugate classes.** Proved result. Under the stated hypotheses, simultaneously conjugating both class indices preserves the inverse entry. (`inverse_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L46)).

**Gauge inverse entries are real.** Proved result. Under the stated hypotheses, each entry of the gauge inverse is fixed by complex conjugation. (`inverse_star`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L50)).

**Gauge shift value.** Definition. This defines minus the inverse gauge matrix applied to the deleted key values. (`shiftValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L53)).

**Gauge shift cancels deleted keys.** Proved result. Under the stated hypotheses, adding the gauge shift through the gauge matrix cancels each deleted key value. (`deleted_shift_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L55)).

**Gauge shifts conjugate.** Proved result. Under the stated hypotheses, conjugate input key values give conjugate shift values. (`shift_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L66)).

**Real gauge shift.** Proved result. Under the stated hypotheses, the indicated gauge shift has zero imaginary part. (`shift_real`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugeKeyValues.lean#L75)).

### Breakdown.CertCell.GaugePlaneFlipFacts

Defines plane velocity and gradient traces for axis-admissible tests. It collects their height-reflection and zero-trace properties for the omitted-plane gauge analysis. Appendix B: cell-system construction and finite certificate analysis.

**Test admissible at the axis.** Proposition definition. The interface requires that the inner radius is positive or the test has a continuous radial factor at radius zero. (`IsAxisAdmissibleTest`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L15)).

**Gradient on the meridian plane.** Definition. `Breakdown.CertCell.PlaneFlipFacts.planeGrad` selects the indicated gradient-mode component at time zero on the meridian plane. (`planeGrad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L18)).

**Second derivative on the meridian.** Definition. `Breakdown.CertCell.PlaneFlipFacts.planeSlope` selects the indicated second-derivative mode with the stated index order on the meridian plane. (`planeSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L21)).

**Velocity on the meridian plane.** Definition. `Breakdown.CertCell.PlaneFlipFacts.planeVelocity` selects a velocity-mode component at time zero on the meridian plane. (`planeVelocity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L24)).

**Local square-integrability condition.** Proposition definition. The interface requires that the field is almost everywhere strongly measurable and has finite square integral on every closed ball. (`IsSquareIntegrableNear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L27)).

**Axis strip reflection interface.** Interface. The interface requires that height strip velocity and gradient moments transform with the indicated frame signs, including the axis test condition. (`StripDataFlipAxisHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L30)). Proof route: `Breakdown.CertCell.planeFlipStrip_closed`, `Breakdown.CertCell.SideTrace.stripDataFlipAxis`.

**Axis corner reflection interface.** Interface. The interface requires that the corner moment transforms by its frame sign under reflection, allowing an auxiliary endpoint on the axis. (`CornerDataFlipAxisHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L42)). Proof route: `Breakdown.CertCell.planeFlipCorner_closed`, `Breakdown.CertCell.SideTrace.cornerDataFlipAxis`.

**Pressure strip reflection interface.** Interface. The interface requires that pressure strip moments at opposite angular modes agree under the potential, reflection and axis-test hypotheses. (`PressureStripFlipHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L52)). Proof route: `Breakdown.CertCell.SideTrace.pressureStripFlip_of_parts`, `Breakdown.CertCell.SideTrace.pressureStripFlip`.

**Shift a potential by a constant.** Interface. The interface requires that subtracting a constant preserves the potential relation. (`PotentialShiftHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L60)). Proof route: `Breakdown.CertCell.SideTrace.potentialShift`.

**Choose a potential for a gradient.** Interface. The interface requires that the chosen potential represents every gradient field. (`PotentialOfGradientHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L63)). Proof route: `Breakdown.CertCell.SideTrace.potentialOfGradient`.

**Harmonic pressure is locally square.** Interface. The interface requires that the sine and cosine pressure-gradient coefficients have finite square integral on every closed ball. (`HarmonicPressureSquareHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L66)). Proof route: `Breakdown.CertCell.SideTrace.harmonicPressureSquare`.

**Harmonic pressure reflects.** Interface. The interface requires that the sine and cosine pressure coefficients inherit the pressure field's almost-everywhere reflection symmetry. (`HarmonicPressureFlipHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L70)). Proof route: `Breakdown.CertCell.SideTrace.harmonicPressureFlip`.

**Perturbation gives periodic derivatives.** Interface. The interface requires that every admitted perturbation supplies the periodic second-order field condition. (`PeriodicSecondOrderHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneFlipFacts.lean#L76)). Proof route: `Breakdown.CertCell.CellCalculus.periodicSecondOrder_of_perturbation`, `Breakdown.CertCell.periodicSecondOrder_closed`.

### Breakdown.CertCell.GaugePlaneOdd

Evaluates velocity, gradient, corner and stream keys on odd harmonic lifts. These evaluations reduce odd-plane gauge coefficients to the corresponding zero-trace facts. Appendix B: cell-system construction and finite certificate analysis.

**Velocity key as harmonic strip data.** Proved result. Under the stated hypotheses, the velocity key harmonic is the cosine strip moment plus i times the sine strip moment. (`keyHarmonic_velocity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOdd.lean#L16)).

**Gradient key as harmonic strip data.** Proved result. Under the stated hypotheses, the gradient key harmonic is the radially weighted cosine strip moment plus i times its sine counterpart. (`keyHarmonic_gradient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOdd.lean#L26)).

**Corner key as harmonic corner data.** Proved result. Under the stated hypotheses, the corner key harmonic is the cosine corner moment plus i times the sine corner moment. (`keyHarmonic_corner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOdd.lean#L35)).

**Stream key as harmonic strip data.** Proved result. Under the stated hypotheses, the stream key harmonic is the radial-weighted axial velocity strip combination. (`keyHarmonic_stream`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOdd.lean#L45)).

**Odd plane key vanishes.** Proved result. Under the stated hypotheses, the indicated odd plane skeleton-key harmonic is zero. (`keyHarmonic_planeOdd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOdd.lean#L54)).

**Odd plane-key interface holds.** Proved result. Under the stated hypotheses, the omitted odd plane-key vanishing requirement holds. (`fieldPlaneOddZero_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOdd.lean#L134)).

### Breakdown.CertCell.GaugePlaneOddCore

Establishes null-set, integrability and reflection facts for strip and box integrals. They support the proof that odd plane traces vanish without requiring pointwise identities on exceptional sets. Appendix B: cell-system construction and finite certificate analysis.

**Rectangle with a null side is null.** Proved result. Under the stated hypotheses, a rectangle whose height set is null has zero plane volume. (`box_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L18)).

**Strip on a null rectangle vanishes.** Proved result. Under the stated hypotheses, the height strip moment vanishes on the null rectangle. (`strip_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L26)).

**Radius is nonzero almost everywhere.** Proved result. Under the stated hypotheses, the first coordinate is nonzero almost everywhere in the plane. (`ae_fst_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L31)).

**Restrict an a.e. positive-radius fact.** Proved result. Under the stated hypotheses, the almost-everywhere property holds under the indicated restricted measure. (`ae_restrict_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L38)).

**Combine complex set integrals.** Proved result. Under the stated hypotheses, the integral of the combined function equals the first integral plus i times the second. (`setIntegral_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L44)).

**Strip integrand is integrable.** Proved result. Under the stated hypotheses, the affine field-and-derivative combination times the strip test is integrable. (`strip_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L49)).

**Radially weighted strip is integrable.** Proved result. Under the stated hypotheses, the strip integrand with radial weight is integrable. (`strip_weighted_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L60)).

**Corner integrand.** Definition. This defines the four affine terms used to evaluate a corner trace. (`cornerIntegrand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L76)).

**Corner moment by its integrand.** Proved result. Under the stated hypotheses, the corner moment equals the signed rectangle integral of the four-term integrand. (`cornerMoment_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L82)).

**Corner integrand is integrable.** Proved result. Under the stated hypotheses, the four-term corner integrand is integrable on the stated domain. (`corner_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L87)).

**Even zero-azimuth label.** Proved result. Under the stated hypotheses, the harmonic of the even zero-azimuth label is the stated pure time frequency. (`labelHarmonic_even`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L99)).

**Lift even modes to local fields.** Proved result. Under the stated hypotheses, the cosine and sine lifts are local second-order fields and reproduce the plane velocity and derivative modes almost everywhere. (`lift_even`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddCore.lean#L107)).

### Breakdown.CertCell.GaugePlaneOddMain

Combines axis admissibility, reflected test traces and strip identities to prove the odd-plane gauge result. The conclusion applies to the stated harmonic labels and local admissible fields. Appendix B: cell-system construction and finite certificate analysis.

**Reflection fixes zero azimuth.** Proved result. Under the stated hypotheses, reflection leaves the pure time-frequency harmonic unchanged. (`flipLabel_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L16)).

**Radial weight makes an axis test.** Proved result. Under the stated hypotheses, a continuous test multiplied by radius satisfies the axis-admissibility condition. (`axis_admissible`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L20)).

**Segment test is continuous.** Proved result. Under the stated hypotheses, the segment's test polynomial is continuous. (`test_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L26)).

**Combine harmonic strip moments.** Proved result. Under the stated hypotheses, the combined strip moment is the first moment plus i times the second. (`strip_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L30)).

**Combine harmonic corner moments.** Proved result. Under the stated hypotheses, the combined corner moment is the first moment plus i times the second. (`corner_combine`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L48)).

**Local velocity and gradient integrals.** Proved result. Under the stated hypotheses, the stated zero-azimuth velocity and gradient modes are integrable on the rectangle. (`mode_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L66)).

**Weighted second mode is square.** Proved result. Under the stated hypotheses, the second-derivative mode is measurable and its radius-weighted square is integrable. (`third_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L75)).

**Weighted second mode is integrable.** Proved result. Under the stated hypotheses, the radius-weighted second-derivative mode is integrable on the cell. (`third_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L87)).

**Second mode is integrable off axis.** Proved result. Under the stated hypotheses, the unweighted second-derivative mode is integrable under the stated off-axis hypotheses. (`third_plain`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddMain.lean#L105)).

### Breakdown.CertCell.GaugePlaneOddZero

Shows that the relevant strip velocity, strip gradient and corner traces vanish for the odd reflected data. These are the zero values used by the odd-plane gauge keys. Appendix B: cell-system construction and finite certificate analysis.

**Odd velocity strip vanishes.** Proved result. Under the stated hypotheses, the indicated cosine-plus-i-sine velocity strip combination is zero. (`strip_velocity_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddZero.lean#L19)).

**Odd gradient strip vanishes.** Proved result. Under the stated hypotheses, the indicated radially weighted gradient strip combination is zero. (`strip_gradient_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddZero.lean#L45)).

**Odd corner moment vanishes.** Proved result. Under the stated hypotheses, the indicated cosine-plus-i-sine corner combination is zero. (`corner_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlaneOddZero.lean#L75)).

### Breakdown.CertCell.GaugePlanePair

Packages the plane trace facts and uses them to show that the relevant field-plane pairing is zero. The argument depends on the separately supplied trace and admissibility conditions. Appendix B: cell-system construction and finite certificate analysis.

**Plane trace facts.** Proposition structure. The interface requires that the harmonic lift, periodicity, reflected traces and normalized pressure facts all hold. (`PlaneTraceFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePair.lean#L13)).

**Plane-pair omission interface holds.** Proved result. Under the stated hypotheses, the field plane-pair zero requirement follows from the stated trace facts. (`fieldPlanePairZero_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePair.lean#L31)).

### Breakdown.CertCell.GaugePlanePairBase

Transports strip and corner traces across almost-everywhere equality and degenerate intervals. It assembles the elementary trace facts needed for vanishing plane pairings. Appendix B: cell-system construction and finite certificate analysis.

**Radius is nonzero almost everywhere.** Proved result. Under the stated hypotheses, the radial coordinate is nonzero almost everywhere for plane volume. (`ae_fst_ne_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L15)).

**Strip moments respect a.e. data.** Proved result. Under the stated hypotheses, almost-everywhere equality of both inputs preserves a height strip moment. (`heightStrip_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L23)).

**Corner moments respect a.e. data.** Proved result. Under the stated hypotheses, almost-everywhere equality of the four inputs preserves a corner moment. (`corner_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L35)).

**Empty radial strip vanishes.** Proved result. Under the stated hypotheses, the height strip moment is zero for the indicated nonpositive radial interval. (`heightStrip_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L49)).

**Segment tests are continuous.** Proved result. Under the stated hypotheses, the segment test is continuous. (`segTest_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L57)).

**Reflection equals frequency reversal.** Proved result. Under the stated hypotheses, the zero-time-frequency condition makes reflection equal negation of the harmonic. (`flipLabel_of_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L61)).

**Plane labels have zero time frequency.** Proved result. Under the stated hypotheses, the stated even plane label has time-frequency coordinate zero. (`planeLabel_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L64)).

**Velocity modes conjugate.** Proved result. Under the stated hypotheses, negating a harmonic conjugates its plane velocity mode. (`planeVelocity_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L73)).

**Gradient modes conjugate.** Proved result. Under the stated hypotheses, negating a harmonic conjugates its plane gradient mode. (`planeGrad_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L80)).

**Second modes conjugate.** Proved result. Under the stated hypotheses, negating a harmonic conjugates its plane second-derivative mode. (`planeSlope_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L87)).

**Zero velocity field has zero modes.** Proved result. Under the stated hypotheses, the zero velocity field has zero angular modes. (`modeVec_zero_field`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L96)).

**Zero gradient field has zero modes.** Proved result. Under the stated hypotheses, the zero gradient field has zero angular modes. (`gradMode_zero_field`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L100)).

**Zero second field has zero modes.** Proved result. Under the stated hypotheses, the zero second-derivative field has zero angular modes. (`modeThird_zero_field`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L104)).

**Time-zero lift agrees with modes.** Proved result. Under the stated hypotheses, the plane velocity and derivative modes agree almost everywhere with the zero-time cosine tuple. (`lift_at_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairBase.lean#L108)).

### Breakdown.CertCell.GaugePlanePairKeys

Evaluates velocity, gradient, pressure, corner and stream gauge keys on plane fields. The resulting identities connect plane traces to the gauge-key representation. Appendix B: cell-system construction and finite certificate analysis.

**Plane velocity key is a strip moment.** Proved result. Under the stated hypotheses, the plane velocity key equals its unit-height strip moment. (`keyValue_velocity_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L18)).

**Plane gradient key is a strip moment.** Proved result. Under the stated hypotheses, the plane gradient key equals its radially weighted unit-height strip moment. (`keyValue_gradient_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L24)).

**Plane pressure key is a strip moment.** Proved result. Under the stated hypotheses, the plane pressure key equals the radially weighted head-pressure strip moment. (`keyValue_pressure_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L30)).

**Plane corner key is a corner moment.** Proved result. Under the stated hypotheses, the plane corner key equals its specified corner moment. (`keyValue_corner_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L36)).

**Radial test is axis-admissible.** Proved result. Under the stated hypotheses, multiplying the continuous test by radius gives an admissible test for a nonnegative inner radius. (`axisAdmissible_of_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L44)).

**A conjugation rule forces a part zero.** Proved result. Under the stated hypotheses, the indicated signed conjugation equation forces the selected real or imaginary part to vanish. (`keyPart_zero_of_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L50)).

**Velocity plane key conjugation.** Proved result. Under the stated hypotheses, conjugating the plane velocity key multiplies it by the frame sign. (`velocity_key_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L72)).

**Gradient plane key conjugation.** Proved result. Under the stated hypotheses, conjugating the plane gradient key multiplies it by the negative frame sign. (`gradient_key_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L90)).

**Corner plane key conjugation.** Proved result. Under the stated hypotheses, conjugating the plane corner key multiplies it by the frame sign. (`corner_key_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L109)).

**Plane pressure key is real.** Proved result. Under the stated hypotheses, the plane pressure key is fixed by complex conjugation. (`pressure_key_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairKeys.lean#L125)).

### Breakdown.CertCell.GaugePlanePairZero

Evaluates zero-angle sine harmonics and the associated zero field traces. These calculations establish the vanishing plane-pair gauge values for the stated labels. Appendix B: cell-system construction and finite certificate analysis.

**Zero-frequency sine vanishes.** Proved result. Under the stated hypotheses, the time-zero sine coefficient is zero. (`harmonicSin_at_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L12)).

**Zero-frequency sine tuple vanishes.** Proved result. Under the stated hypotheses, the time-zero sine tuple is the zero tuple. (`sinTuple_at_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L17)).

**Zero field is a gradient.** Proved result. The zero vector field is the weak gradient of the constant scalar potential zero on R³. (`isGradientField_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L22)).

**Zero height strip moment.** Proved result. Under the stated hypotheses, zero field and derivative inputs give a zero height strip moment. (`heightStrip_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L25)).

**Zero radial strip moment.** Proved result. Under the stated hypotheses, zero field and derivative inputs give a zero radial strip moment. (`radialStrip_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L29)).

**Zero segment moment.** Proved result. Under the stated hypotheses, zero field and derivative inputs give a zero segment moment. (`segMoment_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L33)).

**Segment moments respect a.e. data.** Proved result. Under the stated hypotheses, almost-everywhere equal field inputs give equal segment moments. (`segMoment_congr_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L38)).

**Zero tuple has zero velocity modes.** Proved result. Under the stated hypotheses, all layout velocity modes of the zero tuple vanish. (`velMode_zeroTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L53)).

**Zero tuple has zero gradient modes.** Proved result. Under the stated hypotheses, all layout gradient modes of the zero tuple vanish. (`gradModeOf_zeroTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L58)).

**Zero tuple has zero second modes.** Proved result. Under the stated hypotheses, all layout second-derivative modes of the zero tuple vanish. (`secondModeOf_zeroTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L63)).

**Zero tuple has zero pressure modes.** Proved result. Under the stated hypotheses, all pressure-gradient modes of the zero tuple vanish. (`pressureGradMode_zeroTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L68)).

**Zero head pressure vanishes a.e..** Proved result. Under the stated hypotheses, the zero tuple's head pressure vanishes almost everywhere. (`headPressure_zeroTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L73)).

**Zero tuple has zero key values.** Proved result. Under the stated hypotheses, all skeleton-key values of the zero tuple vanish. (`keyValue_zeroTuple`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L99)).

**Time-zero key uses the cosine tuple.** Proved result. Under the stated hypotheses, the zero-time key harmonic is the key value of the cosine tuple. (`keyHarmonic_at_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GaugePlanePairZero.lean#L120)).

### Breakdown.CertCell.GeneratorFlip

Calculates how generator coordinates, polynomial profiles and their coefficients transform under the label reflection. These signs supply the finite generator flip identities. Appendix B: cell-system construction and finite certificate analysis.

**Frame signs square to one.** Proved result. Under the stated hypotheses, each frame sign multiplied by itself is one. (`sign_mul_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L13)).

**Reflection acts by coordinate signs.** Proved result. Under the stated hypotheses, reflection multiplies each coordinate by its frame sign. (`flip_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L17)).

**Reflection fixes the first coordinate.** Proved result. Under the stated hypotheses, reflection leaves coordinate zero unchanged. (`flip_coord_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L20)).

**Reflection negates the second coordinate.** Proved result. Under the stated hypotheses, reflection negates coordinate one. (`flip_coord_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L24)).

**Reflection negates height.** Proved result. Under the stated hypotheses, reflection negates coordinate two. (`flip_coord_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L28)).

**Reflection as a linear map.** Definition. `Breakdown.CertCell.Internal.GeneratorFlip.flipLinear` packages the spatial reflection as a real linear map. (`flipLinear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L32)).

**Linear reflection evaluates correctly.** Proved result. Under the stated hypotheses, the linear reflection has the specified pointwise reflection action. (`flipLinear_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L43)).

**Label reflection is involutive.** Proved result. Under the stated hypotheses, reflecting a label twice returns the original label. (`labelFlip_involutive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L45)).

**Reflection preserves a cell solid.** Proved result. Under the stated hypotheses, a reflected point belongs to the cell solid exactly when the original point does. (`flip_mem_solid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L49)).

**Meridian coordinates after reflection.** Proved result. Under the stated hypotheses, reflection preserves radius and negates the meridian height. (`pointPlane_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L57)).

**Angle after reflection.** Proved result. Under the stated hypotheses, the reflected angle is the negative angle, possibly shifted by two pi. (`pointAngle_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L61)).

**Reflect the cylindrical frame.** Proved result. Under the stated hypotheses, reflecting a frame vector gives its frame sign times the vector at the negative angle. (`flip_frameUnit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L77)).

**Frame is two-pi periodic.** Proved result. Under the stated hypotheses, adding two pi leaves a cylindrical frame vector unchanged. (`frameUnit_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L84)).

**Label phase is two-pi periodic.** Proved result. Under the stated hypotheses, adding two pi to the angle preserves the label phase. (`labelPhase_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L87)).

**Reflect the label and the angle.** Proved result. Under the stated hypotheses, reflecting the label and negating angle preserve the label phase. (`labelPhase_labelFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L97)).

**Reflected cell values.** Proved result. Under the stated hypotheses, the reflected label and height give the component's frame sign times the original cell value. (`planeValue_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L104)).

**Reflected phase times cell value.** Proved result. Under the stated hypotheses, the phase and cell coefficient transform together by the component frame sign. (`phase_planeValue_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L118)).

**Reflect the finite cell sum.** Proved result. Under the stated hypotheses, the reflected finite mode sum is the spatial reflection of the original sum. (`cell_sum_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L128)).

**Cell vector field is equivariant.** Proved result. Under the stated hypotheses, the cell vector field commutes with spatial reflection. (`cellVecField_flip_equivariant`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/GeneratorFlip.lean#L146)).

### Breakdown.CertCell.HalfPlaneReduction

Relates cylindrical coordinates to axial rotations and height reflection. It reduces rotation-invariant spatial integrals to weighted half-plane integrals and combines the upper and lower height contributions. Appendix B: cell-system construction and finite certificate analysis.

**Cylindrical point as a rotation.** Proved result. Under the stated hypotheses, the cylindrical-coordinate map is rotation of the corresponding meridian point. (`cylArg_eq_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L19)).

**Reflection reverses rotations.** Proved result. Under the stated hypotheses, reflection after rotation equals rotation by the negative angle after reflection. (`flipPoint_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L24)).

**Reflect a meridian point.** Proved result. Under the stated hypotheses, negating meridian height gives the spatially reflected meridian point. (`planePoint_neg_height`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L29)).

**Spatial reflection is involutive.** Proved result. Under the stated hypotheses, reflecting a point twice returns it. (`flipPoint_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L33)).

**Linear spatial reflection.** Definition. `Breakdown.CertCell.Bridge.Internal.HalfPlaneReduction.flipLinear` packages the spatial reflection as a real linear map. (`flipLinear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L37)).

**Reflection preserves null sets.** Proved result. Under the stated hypotheses, the preimage of a null set under reflection is null. (`flipPoint_preimage_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L46)).

**A null invariant set misses meridians.** Proved result. Under the stated hypotheses, the stated null set is avoided by almost every positive-radius meridian point. (`plane_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L52)).

**Rotation-invariant cylindrical integral.** Proved result. Under the stated hypotheses, the space lower integral equals two pi times the radius-weighted meridian lower integral. (`rotation_invariant_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L67)).

**Meridian lower-integral formula.** Proved result. Under the stated hypotheses, the invariant lower integral reduces to the stated radius-weighted meridian integral. (`meridian_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L87)).

**Split a meridian into two halves.** Proved result. Under the stated hypotheses, the meridian integral is the sum of the upper half-plane integral and its reflected counterpart. (`meridian_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L104)).

**Reflected half-plane modes agree a.e..** Proved result. Under the stated hypotheses, the reflected-label mode at negative height agrees almost everywhere with the original half-plane mode. (`flip_height_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HalfPlaneReduction.lean#L135)).

### Breakdown.CertCell.HarmonicCornerData

Commutes harmonic time averaging with corner and stream trace integrals. The resulting formulas identify the local corner data of a lifted harmonic field. Appendix B: cell-system construction and finite certificate analysis.

**Split harmonic corner data.** Proved result. Under the stated hypotheses, the corner moment of the combined data is the cosine moment plus i times the sine moment. (`corner_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L22)).

**A continuous factor keeps integrability.** Proved result. Under the stated hypotheses, the stated scalar factor times the complex field is integrable. (`one_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L46)).

**Corner combination is integrable.** Proved result. Under the stated hypotheses, the four-term corner expression is integrable on the cell rectangle. (`corner_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L50)).

**Stream combination is integrable.** Proved result. Under the stated hypotheses, the radius-weighted axial strip expression is integrable on the cylinder rectangle. (`stream_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L92)).

**Corner rectangle equals its cell.** Proved result. Under the stated hypotheses, the rectangle between the two layout corners is exactly the cell rectangle. (`corner_rect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L104)).

**Corner radial endpoints differ.** Proved result. Under the stated hypotheses, the two layout corner radii are distinct. (`corner_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L113)).

**Corner touches axis or stays away.** Proved result. Under the stated hypotheses, the opposite corner radius is zero or the cell has positive inner radius. (`corner_case`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L120)).

**Recover harmonic corner values.** Proved result. Under the stated hypotheses, harmonic corner velocity and stream data equal their analytic corner and height-strip moments at the permitted parities. (`harmonicCornerData_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L136)).

**Harmonic data recover corner moments.** Proved result. Under the stated hypotheses, harmonic corner velocity and stream data equal their analytic corner and height-strip moments at the permitted parities. (`harmonicCornerData_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicCornerData.lean#L184)).

### Breakdown.CertCell.HarmonicEnergyValue

Combines axis null sets, label-mode identities and harmonic parity to evaluate the harmonic energy form. Its main bridge is conditional on the supplied lift identities. Appendix B: cell-system construction and finite certificate analysis.

**The axis is null.** Proved result. Under the stated hypotheses, radius is nonzero almost everywhere in the meridian plane. (`axis_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicEnergyValue.lean#L14)).

**Recover the mode label.** Proved result. Under the stated hypotheses, the harmonic-mode constructor recovers the label from its time index and first coordinate. (`label_mode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicEnergyValue.lean#L20)).

**Mode label parity.** Proved result. Under the stated hypotheses, the label's azimuthal and time indices have even sum. (`label_even`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicEnergyValue.lean#L26)).

**Energy form from component identities.** Proved result. Under the stated hypotheses, the harmonic energy form equals the weighted sum of the label strain and vorticity energies. (`harmonicEnergyFormValue_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicEnergyValue.lean#L32)).

### Breakdown.CertCell.HarmonicEnergyValueClosed

Closes the harmonic energy bridge using the established lift construction. The finite harmonic form therefore agrees with the analytic local energy under the stated cell and field hypotheses. Appendix B: cell-system construction and finite certificate analysis.

**Energy form from harmonic lifts.** Proved result. Under the stated hypotheses, the harmonic energy form equals the weighted sum of the label strain and vorticity energies. (`harmonicEnergyFormValue_of_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicEnergyValueClosed.lean#L18)).

**Harmonic energy form evaluates.** Proved result. Under the stated hypotheses, the harmonic energy form equals the weighted sum of the label strain and vorticity energies. (`harmonicEnergyFormValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicEnergyValueClosed.lean#L22)).

### Breakdown.CertCell.HarmonicLocal

Proves measurability, integrability and weak differentiation for harmonic averages of local fields. It shows that the lifted velocity, gradient and second derivative preserve the required local admissibility. Appendix B: cell-system construction and finite certificate analysis.

**Swap spacetime measurability.** Proved result. Under the stated hypotheses, switching the time and space arguments preserves almost-everywhere strong measurability for the stated product measure. (`aesm_swap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L18)).

**Time average is measurable.** Proved result. Under the stated hypotheses, the weighted time average is almost everywhere strongly measurable in space. (`aesm_avg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L26)).

**Almost every time slice is measurable.** Proved result. Under the stated hypotheses, almost every time slice is almost everywhere strongly measurable in space. (`aesm_slice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L31)).

**Weighted power-integral inequality.** Proved result. Under the stated hypotheses, the power of a lower integral is bounded by the stated weighted power integral. (`lintegral_rpow_le_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L37)).

**Power of the time average is finite.** Proved result. Under the stated hypotheses, the spatial integral of the powered time average is finite. (`lintegral_rpow_avg_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L74)).

**Time averaging preserves Lp control.** Proved result. Under the stated hypotheses, the weighted time average lies in the specified Lp space. (`memLp_avg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L150)).

**Linear map from its columns.** Proved result. Under the stated hypotheses, a linear map applied to a vector is the sum of the vector coordinates times its basis columns. (`apply_eq_sum_cols`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L170)).

**Operator norm by column norms.** Proved result. Under the stated hypotheses, the operator norm is bounded by the sum of its three column norms. (`norm_le_sum_cols`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L178)).

**Operator square by column squares.** Proved result. Under the stated hypotheses, the squared operator norm is at most three times the sum of column squares. (`norm_sq_le_cols`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L189)).

**Coordinate vectors have norm one.** Proved result. Under the stated hypotheses, each coordinate unit vector has norm one. (`norm_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L200)).

**Column norm by operator norm.** Proved result. Under the stated hypotheses, each column norm is at most the operator norm. (`col_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L203)).

**Column squares by operator square.** Proved result. Under the stated hypotheses, the sum of the three column squares is at most three times the squared operator norm. (`sum_cols_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L207)).

**A linear value by one plus square.** Proved result. Under the stated hypotheses, a real value is at most one plus its square. (`le_one_add_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L214)).

**Square root by one plus value.** Proved result. Under the stated hypotheses, the half power is bounded by one plus the value. (`rpow_half_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L221)).

**Square integral is finite.** Proved result. Under the stated hypotheses, the given domination makes the spacetime square integral finite. (`sq_lt_top_of_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L228)).

**Square-root integral is finite.** Proved result. Under the stated hypotheses, the time integral of the spatial square-root energy is finite. (`rpow_half_lintegral_lt_top_of_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L243)).

**Local L1 from a square bound.** Proved result. Under the stated hypotheses, the field is integrable on the stated bounded spacetime region by its square bound. (`hloc_of_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L256)).

**Sixth power in extended norm.** Proved result. Under the stated hypotheses, the nonnegative real sixth power equals the sixth power of the extended norm. (`enorm_pow_six`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L273)).

**Local L1 from a sixth-power bound.** Proved result. Under the stated hypotheses, the field is integrable on the stated bounded spacetime region by its sixth-power bound. (`hloc_six`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L278)).

**Bounded scalar does not enlarge norm.** Proved result. Under the stated hypotheses, the stated scalar multiplication does not increase the extended norm. (`smul_enorm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L309)).

**Time averages exist a.e..** Proved result. Under the stated hypotheses, the weighted time slice is integrable for almost every spatial point. (`ae_integrable_avg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L318)).

**Test-weighted spacetime integrability.** Proved result. Under the stated hypotheses, the test-weighted field is integrable on the space-time product. (`integrable_test_prod`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L340)).

**Swap the test and time integrals.** Proved result. Under the stated hypotheses, the weighted time average may be exchanged with the spatial test pairing. (`swap_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L378)).

**Test derivatives remain supported.** Proved result. Under the stated hypotheses, the coordinate derivative of the smooth compactly supported test is continuous and compactly supported. (`test_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L398)).

**Linear maps pass through averages.** Proved result. Under the stated hypotheses, the continuous linear map passes through the weighted time average almost everywhere. (`clm_avg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L407)).

**Weighted averages are local fields.** Proved result. Under the stated hypotheses, the weighted averages of velocity, gradient and second derivative form a local second-order field. (`local_of_weight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L417)).

**Sine harmonic as a weighted integral.** Proved result. Under the stated hypotheses, the sine harmonic is the integral weighted by negative sine. (`harmonicSin_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L559)).

**Harmonics are local second-order fields.** Proved result. Under the stated hypotheses, the cosine and sine field triples each satisfy the local second-order conditions. (`harmonic_local`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicLocal.lean#L566)).

### Breakdown.CertCell.HarmonicPressureFlip

Computes the action of height reflection on coordinates and pressure gradients. These identities prove the reflected pressure relation for harmonic lifts. Appendix B: cell-system construction and finite certificate analysis.

**Reflection fixes coordinate zero.** Proved result. Under the stated hypotheses, reflection preserves coordinate zero. (`flipPoint_coord_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L17)).

**Reflection negates coordinate one.** Proved result. For the half-turn R(y₁,y₂,y₃) = (y₁,−y₂,−y₃), the second Cartesian component of Ry is −y₂ at every point. (`flipPoint_coord_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L20)).

**Reflection negates coordinate two.** Proved result. For the half-turn R(y₁,y₂,y₃) = (y₁,−y₂,−y₃), the third Cartesian component of Ry is −y₃ at every point. (`flipPoint_coord_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L23)).

**Reflection coordinate formula.** Proved result. Under the stated hypotheses, reflection preserves coordinate zero and negates the other coordinates. (`flipPoint_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L26)).

**Reflection as a continuous equivalence.** Definition. `Breakdown.CertCell.SideTrace.Internal.HarmonicFlip.flipLinearEquiv` constructs the continuous linear reflection equivalence. (`flipLinearEquiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L33)).

**Continuous reflection evaluates.** Proved result. Under the stated hypotheses, the continuous linear equivalence acts as spatial reflection. (`flipLinearEquiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L54)).

**Slice a spacetime reflection equality.** Proved result. Under the stated hypotheses, the almost-everywhere spacetime reflection identity holds for almost every spatial and time slice. (`ae_slices_of_ae_prod`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L56)).

**Reflection passes through time averaging.** Proved result. Under the stated hypotheses, the weighted time integral inherits the field's reflection identity almost everywhere. (`weighted_integral_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L63)).

**Pressure harmonics respect reflection.** Proved result. Under the stated hypotheses, cosine and sine pressure-gradient harmonics preserve height-reflection symmetry almost everywhere. (`harmonicPressureFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/HarmonicPressureFlip.lean#L78)).
<!-- /passage:front -->

