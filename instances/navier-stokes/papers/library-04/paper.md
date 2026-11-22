
<!-- passage:front -->
# Library guide 4: Breakdown/Cert

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) **4** [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Cert.CoercivePieceAbsorb` to `Breakdown.Cert.CoerciveSmoothMuWave` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Cert.CoercivePieceAbsorb

The piece-weight density is split into base, curl-piece, and velocity-piece contributions and summed with their remainders and nonpositive block correction to close the signed inequality.

**Paper context:** Appendix B, Proposition B.1: absorption for the extended piece-weight multiplier.

**Theorem: Subadditive direction for period sums.** The sum of two nonnegative period integrals is at most the period integral of their pointwise sum. Source: `Breakdown.Coercive.Internal.PieceAbsorb.le_lintegral_add_iter` (`Breakdown/Cert/CoercivePieceAbsorb.lean:16`).

**Theorem: Add nonnegative period integrals.** Under the stated measurability hypothesis, the nonnegative period integral of a sum equals the sum of its two period integrals. Source: `Breakdown.Coercive.Internal.PieceAbsorb.lintegral_add_iter` (`Breakdown/Cert/CoercivePieceAbsorb.lean:21`).

**Theorem: Transfer the integrated signed bound.** The assumed density comparison transfers to the signed integrated bound after including the positive and negative stretching contributions. Source: `Breakdown.Coercive.Internal.PieceAbsorb.transfer` (`Breakdown/Cert/CoercivePieceAbsorb.lean:41`).

**Theorem: Discard the negative part in ENNReal.** Converting a real number to a nonnegative extended real gives the same result as first taking its maximum with zero. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ofReal_eq_max` (`Breakdown/Cert/CoercivePieceAbsorb.lean:83`).

**Theorem: Positive parts of a summable family sum.** The positive parts of the stated summable real family form a summable family. Source: `Breakdown.Coercive.Internal.PieceAbsorb.summable_max` (`Breakdown/Cert/CoercivePieceAbsorb.lean:88`).

**Theorem: Sum positive parts in extended reals.** The extended-real sum of converted real terms equals the conversion of the real sum of their positive parts under the stated summability hypothesis. Source: `Breakdown.Coercive.Internal.PieceAbsorb.tsum_ofReal_eq` (`Breakdown/Cert/CoercivePieceAbsorb.lean:91`).

**Theorem: Recover a signed sum from positive parts.** The real series sum equals the sum of its positive parts minus the sum of its negative parts under the stated summability hypothesis. Source: `Breakdown.Coercive.Internal.PieceAbsorb.tsum_max_sub` (`Breakdown/Cert/CoercivePieceAbsorb.lean:96`).

**Theorem: Divergent positive parts give infinity.** If the positive-part series is not summable, the corresponding nonnegative extended-real series equals infinity. Source: `Breakdown.Coercive.Internal.PieceAbsorb.tsum_ofReal_top` (`Breakdown/Cert/CoercivePieceAbsorb.lean:106`).

**Theorem: Convert a signed series inequality.** The real summed density bound yields the corresponding inequality between its nonnegative extended-real positive and negative parts. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ennreal_of_real_sums` (`Breakdown/Cert/CoercivePieceAbsorb.lean:113`).

**Theorem: The piece block is nonpositive.** The piece block correction is at most zero under the stated piece-weight and amplitude hypotheses. Source: `Breakdown.Coercive.Internal.PieceAbsorb.pieceBlock_nonpos` (`Breakdown/Cert/CoercivePieceAbsorb.lean:157`).

**Theorem: Split the piecewise mode density.** The mode density is its base density plus the sum of curl-piece densities and the sum of velocity-piece densities. Source: `Breakdown.Coercive.Internal.PieceAbsorb.modeDensity_split` (`Breakdown/Cert/CoercivePieceAbsorb.lean:182`).

**Theorem: Sum the absorbed piece discrepancies.** The density-minus-positive series and remainder series are summable, and their total discrepancy is bounded by the remainder sum plus the block correction. Source: `Breakdown.Coercive.Internal.PieceAbsorb.real_step` (`Breakdown/Cert/CoercivePieceAbsorb.lean:192`).

**Theorem: A signed pointwise piece-density bound.** The nonnegative extended-real positive and negative density parts satisfy the absorbed inequality with the positive contribution, remainder, and block correction. Source: `Breakdown.Coercive.Internal.PieceAbsorb.pointwise_step` (`Breakdown/Cert/CoercivePieceAbsorb.lean:232`).

**Theorem: Absorb the piece interaction costs.** The supplied hypotheses establish conversion of a split piece-remainder bound into the signed total piece-density inequality. Source: `Breakdown.Coercive.pieceAbsorbStepHolds_of` (`Breakdown/Cert/CoercivePieceAbsorb.lean:252`).

### Breakdown.Cert.CoercivePieceAbsorbEdge

Harmonic interactions crossing a mode-piece boundary are expanded, absorbed into squares, and reindexed so their cost is charged to the correct incoming and outgoing weights.

**Paper context:** Appendix B, Proposition B.1: boundary-interaction bookkeeping for mode pieces.

**Definition: Summable mode energies at a point.** Require summability of all five squared velocity and derivative amplitudes at the point. Source: `Breakdown.Coercive.Internal.PieceAbsorb.IsGoodPoint` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:13`).

**Theorem: Absorb an edge product into squares.** The stated nonnegative coefficients and discriminant bound imply c p q ≤ A p² + B q². Source: `Breakdown.Coercive.Internal.PieceAbsorb.absorb_le` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:19`).

**Theorem: Proposition indicators are nonnegative.** The real-valued indicator of a proposition is nonnegative. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ind_nonneg` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:28`).

**Theorem: An indicator is at most one.** The real-valued indicator of a proposition is at most one. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ind_le_one` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:32`).

**Theorem: Bounded weights preserve square sums.** Multiplying the stated square-summable family by the bounded scalar weights gives a summable weighted-square family. Source: `Breakdown.Coercive.Internal.PieceAbsorb.summable_bdd_mul` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:36`).

**Theorem: Bound the incoming harmonic cost.** The absolute incoming cost is at most the finite sum of the harmonic coefficient magnitudes. Source: `Breakdown.Coercive.Internal.PieceAbsorb.abs_inward_le` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:43`).

**Theorem: Bound the outgoing harmonic cost.** The absolute outgoing cost is at most twice the finite sum of the harmonic coefficient magnitudes. Source: `Breakdown.Coercive.Internal.PieceAbsorb.abs_outward_le` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:57`).

**Theorem: Absorb one boundary-crossing term.** The conditional interaction across a piece boundary is bounded by the allocated incoming amplitude square and the outgoing neighboring amplitude squares. Source: `Breakdown.Coercive.Internal.PieceAbsorb.edge_term_le` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:78`).

**Theorem: Bound a scalar product by squares.** The absolute value of c p q is at most |c| times p² + q². Source: `Breakdown.Coercive.Internal.PieceAbsorb.abs_mul_le_half` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:101`).

**Theorem: Bound a boundary-crossing product.** The conditional boundary interaction has absolute value at most |c| times its nonnegative weight times the three participating amplitude squares. Source: `Breakdown.Coercive.Internal.PieceAbsorb.edge_term_abs` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:108`).

**Theorem: Expand the boundary interaction sum.** The edge sum is the finite harmonic sum selected by membership of a mode or its negative and nonmembership of the corresponding neighboring mode. Source: `Breakdown.Coercive.Internal.PieceAbsorb.edgeSum_eq` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:124`).

**Theorem: Expand the incoming harmonic cost.** The incoming cost is the harmonic coefficient sum selected by piece membership and the corresponding boundary-crossing condition. Source: `Breakdown.Coercive.Internal.PieceAbsorb.inward_eq` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:131`).

**Theorem: A zero selector preserves nonnegativity.** Selecting either a nonnegative value or zero gives a nonnegative result. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ite_nonneg_of` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:137`).

**Theorem: Deleting a nonnegative term decreases it.** For a nonnegative real a, choosing either a or zero is at most a. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ite_le_of` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:140`).

**Theorem: Backward shifts preserve square sums.** A fixed backward shift of the integer mode indices preserves summability of the squared amplitudes. Source: `Breakdown.Coercive.Internal.PieceAbsorb.summable_shift_sub` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:143`).

**Theorem: Forward shifts preserve square sums.** A fixed forward shift of the integer mode indices preserves summability of the squared amplitudes. Source: `Breakdown.Coercive.Internal.PieceAbsorb.summable_shift_add` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:147`).

**Theorem: Charge shifted edges to outgoing costs.** The shifted boundary-charge series is summable and bounded by the outgoing-cost weighted square series after reindexing. Source: `Breakdown.Coercive.Internal.PieceAbsorb.reindex_le` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:152`).

**Theorem: Sum the absorbed edge interactions.** The edge-interaction series is summable and bounded by the allocated incoming and outgoing weighted amplitude-square sums. Source: `Breakdown.Coercive.Internal.PieceAbsorb.edge_le` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:227`).

**Theorem: Incoming weighted squares are summable.** The piece-restricted incoming-cost weighted amplitude squares form a summable mode family. Source: `Breakdown.Coercive.Internal.PieceAbsorb.summable_inward_term` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:272`).

**Theorem: Outgoing weighted squares are summable.** The outgoing-cost weighted amplitude squares form a summable mode family. Source: `Breakdown.Coercive.Internal.PieceAbsorb.summable_outward_term` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:283`).

**Theorem: Restricted square sums converge.** The amplitude-square family restricted by piece membership remains summable. Source: `Breakdown.Coercive.Internal.PieceAbsorb.summable_ind_term` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:290`).

**Theorem: Square the norm on a mode piece.** The squared piece norm equals the sum of the squared amplitudes selected by membership in the piece or its negative. Source: `Breakdown.Coercive.Internal.PieceAbsorb.pieceNorm_sq` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:294`).

**Theorem: Absorb a product of piece norms.** The product of two piece norms is bounded by the allocated weighted sums of their squared amplitudes under the stated coefficient inequality. Source: `Breakdown.Coercive.Internal.PieceAbsorb.block_le` (`Breakdown/Cert/CoercivePieceAbsorbEdge.lean:299`).

### Breakdown.Cert.CoercivePieceAbsorbEps

The curl-piece density is expanded into local and boundary costs, then its summed discrepancy is bounded by the curl remainder and block correction.

**Paper context:** Appendix B, Proposition B.1: absorption of the curl-piece contributions.

**Theorem: Base density is summable.** Under the stated hypotheses, the base density is summable over its index set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.base_summable` (`Breakdown/Cert/CoercivePieceAbsorbEps.lean:20`).

**Theorem: Expand the curl-piece absorption costs.** Subtracting the positive curl-frequency contribution from the curl-piece density leaves the explicit local and boundary-interaction costs with negative signs. Source: `Breakdown.Coercive.Internal.PieceAbsorb.eps_density_identity` (`Breakdown/Cert/CoercivePieceAbsorbEps.lean:37`).

**Theorem: Absorb the curl-piece density sum.** The curl-piece density discrepancy and remainder series are summable, and their total discrepancy is bounded by the remainder sum plus the curl block correction. Source: `Breakdown.Coercive.Internal.PieceAbsorb.eps_piece_le` (`Breakdown/Cert/CoercivePieceAbsorbEps.lean:72`).

### Breakdown.Cert.CoercivePieceAbsorbMeasure

Measurability, amplitude summability, and good-point conditions make the pointwise piece absorption estimates valid almost everywhere on the period slab.

**Paper context:** Appendix B, Proposition B.1: integration prerequisites for piece absorption.

**Definition: Volume over one time period.** Use the product of volume on the closed unit time interval and spatial volume. Source: `Breakdown.Coercive.Internal.PieceAbsorb.slabMeasure` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:22`).

**Theorem: The slab measure is restricted volume.** The product measure for one time period equals space-time volume restricted to the unit time slab. Source: `Breakdown.Coercive.Internal.PieceAbsorb.slabMeasure_eq` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:26`).

**Theorem: Finite energies give summable slices.** Finiteness of the sum of the integrated nonnegative terms implies almost-everywhere summability on the period slab. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ae_summable_of_tsum_lintegral` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:29`).

**Theorem: Bound the alternating symbol.** Every alternating-symbol value has absolute value at most one. Source: `Breakdown.Coercive.Internal.PieceAbsorb.alternatingSymbol_abs_le` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:44`).

**Theorem: Bound one complex coordinate.** The norm of a complex coordinate is at most the square root of the sum of all coordinate norm squares. Source: `Breakdown.Coercive.Internal.PieceAbsorb.norm_le_sqrt_cnormSq` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:47`).

**Theorem: Squared complex norm is nonnegative.** The squared complex norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.PieceAbsorb.cnormSq_nonneg'` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:53`).

**Theorem: Curl square is controlled by gradient.** The squared curl contraction is at most twice the squared norm of the gradient array. Source: `Breakdown.Coercive.Internal.PieceAbsorb.cnormSq_curlOfGrad_le` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:56`).

**Theorem: Curl-gradient square bound.** The squared curl-gradient contraction is at most twice the squared norm of the second-derivative array. Source: `Breakdown.Coercive.Internal.PieceAbsorb.cnormSq_curlGradOfSecondDeriv_le` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:81`).

**Theorem: Second-derivative mode is measurable.** Under the stated hypotheses, the second-derivative mode is strongly measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aestronglyMeasurable_modeSecondDeriv` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:110`).

**Theorem: Second-derivative mode is measurable.** Under the stated hypotheses, the second-derivative mode is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aemeasurable_modeSecondDeriv` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:124`).

**Theorem: Squared complex norm is measurable.** Under the stated hypotheses, the squared complex norm is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aemeasurable_ofReal_cnormSq` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:130`).

**Theorem: Restrict the joint derivative to space.** The spatial slice derivative equals the joint space-time derivative composed with the inclusion of the spatial factor. Source: `Breakdown.Coercive.Internal.PieceAbsorb.fderiv_slice_eq` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:135`).

**Theorem: Spatial derivative is continuous.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.Internal.PieceAbsorb.continuous_fderiv_slice` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:144`).

**Theorem: Measurability of the spatial Hessian.** Under the stated hypotheses, the joint spatial Hessian field is measurable. Source: `Breakdown.Coercive.Internal.PieceAbsorb.measurable_secondDeriv_slice` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:153`).

**Theorem: Measurable complex square-sum norms.** Under the stated hypotheses, the square-sum norm of the complex array is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_sqrt_cnormSq` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:157`).

**Theorem: Velocity amplitude is measurable.** Under the stated hypotheses, the velocity amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_velAmp` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:164`).

**Theorem: Gradient amplitude is measurable.** Under the stated hypotheses, the gradient amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_gradAmp` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:168`).

**Theorem: Vorticity amplitude is measurable.** Under the stated hypotheses, the vorticity amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_vortAmp` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:173`).

**Theorem: Measurability of Hessian amplitudes.** Under the stated hypotheses, the second-derivative amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_secondDerivAmp` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:181`).

**Theorem: Curl-gradient amplitude is measurable.** Under the stated hypotheses, the vorticity-gradient amplitude is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_vortGradAmp` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:186`).

**Theorem: Boundary interaction sums are measurable.** The finite harmonic boundary sum of the stated measurable coefficient and amplitude families is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_edgeSum` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:195`).

**Definition: Stretching as a function of field data.** Evaluate the strain, vorticity-gradient, and mixed stretching polynomial on the supplied pointwise field data. Source: `Breakdown.Coercive.Internal.PieceAbsorb.stretchOfData` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:214`).

**Theorem: Stretching through pointwise data.** The stretching form equals its algebraic data expression evaluated at the field, gradient, and background first and second derivatives. Source: `Breakdown.Coercive.Internal.PieceAbsorb.stretchForm_eq` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:221`).

**Theorem: Stretching is continuous in its data.** Under the stated hypotheses, the stretching form in its pointwise field data is continuous. Source: `Breakdown.Coercive.Internal.PieceAbsorb.continuous_stretchOfData` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:225`).

**Theorem: Stretching form is measurable.** Under the stated hypotheses, the stretching form is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aem_stretchForm` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:229`).

**Theorem: The piece block is nonpositive.** The piece block correction is at most zero under the stated data and good-point hypotheses. Source: `Breakdown.Coercive.Internal.PieceAbsorb.block_nonpos_of` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:240`).

**Theorem: Summable mode squares almost everywhere.** Almost every point of the time slab satisfies the good-point specification for the five squared mode-amplitude families. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ae_goodPoint` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:265`).

**Theorem: Measurable positive-side density sum.** Under the stated hypotheses, the sum of positive piece, remainder, block, and stretching parts is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aemeasurable_hypothesisSide` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:345`).

**Theorem: Measurability of negative stretching.** Under the stated hypotheses, the negative part of the stretching form is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceAbsorb.aemeasurable_stretchNeg` (`Breakdown/Cert/CoercivePieceAbsorbMeasure.lean:430`).

### Breakdown.Cert.CoercivePieceAbsorbMu

Mode-negation symmetry and harmonic reindexing control the velocity-piece pressure and boundary terms, giving the summed velocity-piece absorption inequality.

**Paper context:** Appendix B, Proposition B.1: absorption of the velocity-piece contributions.

**Theorem: Negating a mode conjugates its average.** The mode average at the negative integer frequency is the complex conjugate of the original average for real input data. Source: `Breakdown.Coercive.Internal.PieceAbsorb.modeAverage_neg` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:14`).

**Theorem: Gradient amplitude is even in the mode.** Negating both integer mode indices leaves the gradient amplitude unchanged. Source: `Breakdown.Coercive.Internal.PieceAbsorb.gradAmp_neg` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:29`).

**Theorem: Frame frequency changes sign.** Negating the integer mode pair negates its frame frequency. Source: `Breakdown.Coercive.Internal.PieceAbsorb.frameFreq_neg` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:33`).

**Theorem: Reindex a symmetric finite mode set.** Negation leaves the sum unchanged when the finite index set is closed under negation. Source: `Breakdown.Coercive.Internal.PieceAbsorb.sum_neg_eq` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:38`).

**Theorem: An indicator cannot enlarge magnitude.** Multiplying a real number by a proposition indicator cannot increase its absolute value. Source: `Breakdown.Coercive.Internal.PieceAbsorb.abs_ind_mul_le` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:43`).

**Theorem: Bound symmetric piece membership.** The indicator of membership in a piece or its negative is at most the sum of the two individual membership indicators. Source: `Breakdown.Coercive.Internal.PieceAbsorb.ind_inPiece_le` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:48`).

**Theorem: Split a finite sum by a predicate.** A finite sum splits into the terms selected by a predicate and those selected by its negation. Source: `Breakdown.Coercive.Internal.PieceAbsorb.split_sum_ite` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:55`).

**Theorem: Compare selected finite sums.** A pointwise bound on the selected terms gives the same bound between their finite sums. Source: `Breakdown.Coercive.Internal.PieceAbsorb.sum_ite_le` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:61`).

**Theorem: Allocate shifted piece coefficients.** The sum of coefficients whose shifted modes enter a piece is bounded by the retained local coefficient allowance plus the outgoing boundary cost. Source: `Breakdown.Coercive.Internal.PieceAbsorb.coef_le` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:69`).

**Theorem: Absorb the squared harmonic sum.** The piece-restricted harmonic convolution square and its allocated square bound are summable, with the former bounded by the latter after summing modes. Source: `Breakdown.Coercive.Internal.PieceAbsorb.pressure_le` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:123`).

**Theorem: Absorb the velocity-piece density sum.** The velocity-piece density discrepancy and remainder series are summable, and their total discrepancy is bounded by the remainder sum plus the velocity block correction. Source: `Breakdown.Coercive.Internal.PieceAbsorb.mu_piece_le` (`Breakdown/Cert/CoercivePieceAbsorbMu.lean:225`).

### Breakdown.Cert.CoercivePieceDensityPassage

The piece-weight multiplier estimate passes from smooth approximations to weak fields by combining source, energy, seminorm, pairing, and signed-density limits.

**Paper context:** Appendix B, Proposition B.1: weak-limit passage for piece-weight multipliers.

**Theorem: Multipliers converge in period L².** The squared period L² distance from each approximating multiplier to the limiting multiplier tends to zero. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.multiplier_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:25`).

**Theorem: The limiting source has finite L² energy.** The limiting equation source is almost-everywhere strongly measurable and has finite squared energy over one time period. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.rightSideLimit_memL2` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:49`).

**Theorem: The smooth source has finite L² energy.** Each smooth approximation source with its actuator combination is almost-everywhere strongly measurable and has finite squared energy over one period. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.smoothRight_memL2` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:71`).

**Theorem: Equation sources converge in period L².** The squared period L² distance between the smooth source with actuators and the explicit limiting source tends to zero. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.smoothRight_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:93`).

**Theorem: Pair with the explicit limiting source.** The source pairing with the multiplier equals the pairing of the explicit limiting equation source with that multiplier. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.rightSide_pairing_eq` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:114`).

**Theorem: Weighted energies converge.** The weighted energies of the approximating gradients and Hessians converge to the weighted energy of the weak derivative fields. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.energy_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:136`).

**Theorem: Piece-seminorm energies converge.** The real squared piece-seminorm energies of the smooth approximations converge to that of the weak field. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.seminorm_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:162`).

**Theorem: Source-multiplier pairings converge.** The smooth source-multiplier pairings converge to the pairing of the limiting source and multiplier. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.right_pairing_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:186`).

**Theorem: Actuator pairings converge.** The pairing of each fixed actuator with the approximating multipliers converges to its pairing with the limiting multiplier. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.action_pairing_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:214`).

**Theorem: Multiplier gaps converge.** The multiplier gaps of the smooth approximations, their sources, and their multipliers converge to the weak-field multiplier gap. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.gap_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:238`).

**Theorem: The integrated negative split is finite.** The integrated negative density side, including its remainder, block, and stretching contributions, is finite. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.right_finite` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:266`).

**Theorem: The positive density split is measurable.** Almost every spatial positive-split integrand is measurable up to a null set, and its spatial integral is likewise measurable in time. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.left_measurable` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:281`).

**Theorem: A subsequence controls both sides.** One strictly increasing subsequence gives convergence of the integrated negative density side and the almost-everywhere lower-liminf bound for the positive side. Source: `Breakdown.Coercive.PieceDensityPassage.Internal.subsequence_limits` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:297`).

**Theorem: Pass piece density to weak fields.** The supplied hypotheses establish transfer of the split piece-density inequality along a smooth approximation to the weak perturbation. Source: `Breakdown.Coercive.pieceDensityPassageHolds_of` (`Breakdown/Cert/CoercivePieceDensityPassage.lean:322`).

### Breakdown.Cert.CoercivePieceDensityPassageDiffBound

Base, curl, velocity, and block estimates are combined into uniform amplitude and difference bounds for the full piece remainder and block correction.

**Paper context:** Appendix B, Proposition B.1: quantitative continuity of piece remainders.

**Theorem: Zero satisfies the remainder bounds.** The identically zero remainder satisfies the uniform amplitude and adjustable quadratic difference specification. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.isRestBound_zero` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:23`).

**Theorem: Equal remainders share their bounds.** The stated equality of remainders transfers the uniform amplitude and adjustable quadratic difference bounds to the second remainder. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.isRestBound_congr` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:27`).

**Theorem: Finite sums retain remainder bounds.** A finite sum of remainders satisfying the uniform amplitude and quadratic difference bounds satisfies those bounds as well. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.isRestBound_sum` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:37`).

**Definition: Put a scalar term at the zero mode.** Assign the scalar block term to the zero frequency and zero to all other modes. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.atOrigin` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:52`).

**Theorem: Only the zero mode contributes an error.** The sum of the absolute discrepancy between two zero-mode-supported families equals the absolute discrepancy of their zero-mode values. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.tsum_atOrigin_sub` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:58`).

**Theorem: Uniform bounds for the base coefficients.** One nonnegative constant bounds all five base-density coefficients, including the radially weighted velocity coefficient. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.base_coeff_bounds` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:76`).

**Theorem: Base density remainder bound.** The base density has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.base_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:121`).

**Theorem: Curl-piece remainder remainder bound.** The curl-piece remainder has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.epsRest_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:207`).

**Theorem: Velocity-piece remainder remainder bound.** The velocity-piece remainder has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.muRest_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:215`).

**Theorem: Curl-piece block term remainder bound.** The curl-piece block term has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.epsBlock_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:223`).

**Theorem: Bounds for the velocity-piece block.** The velocity-piece block term has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.muBlock_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:231`).

**Theorem: Bounds for full piece remainders.** The piece multiplier remainder has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.rest_diff_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:239`).

**Theorem: Piece multiplier block remainder bound.** The piece multiplier block has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBound.block_diff_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBound.lean:248`).

### Breakdown.Cert.CoercivePieceDensityPassageDiffBoundBlock

Reverse triangle inequalities for restricted square-sum norms control products of piece norms; block corrections are placed at the zero mode to fit the common remainder specification.

**Paper context:** Appendix B, Proposition B.1: continuity estimates for piece-block corrections.

**Theorem: Reverse triangle inequality in ℓ².** The difference of the square-sum norms of two square-summable real sequences has absolute value at most the square-sum norm of their difference. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.sqrt_tsum_sub_le` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:16`).

**Theorem: The piece norm is a square-sum norm.** The piece norm is the square root of the sum of squares of the amplitudes multiplied by their piece-membership indicators. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.pieceNorm_eq` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:40`).

**Theorem: Rescale a piece norm.** For the stated positive scalar c, the piece norm of g equals c times the piece norm of g divided by c. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.pieceNorm_scale` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:48`).

**Theorem: An indicator decreases a square.** The square of an indicator times a real value is at most the square of that value. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.ind_mul_sq_le` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:58`).

**Theorem: Finite positive series give summability.** Finiteness of the converted nonnegative series implies summability of the stated nonnegative real family. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.summable_of_ofReal` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:62`).

**Theorem: Sum a contribution supported at zero.** The nonnegative extended-real sum of a term supported only at the zero mode equals the converted absolute value of that term. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.tsum_origin` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:67`).

**Theorem: Only the zero mode contributes an error.** The sum of the absolute discrepancy between two zero-mode-supported families equals the absolute discrepancy of their zero-mode values. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.tsum_origin_sub` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:77`).

**Theorem: Control a restricted amplitude norm.** The piece-restricted amplitude squares are summable, their sum is bounded by the total combined mode energy, and the resulting piece norm is nonnegative. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.amp_norm_facts` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:88`).

**Theorem: Bounds for products of piece norms.** The stated coefficient times a product of two piece norms, placed at the zero mode, satisfies the uniform amplitude and adjustable quadratic difference bounds. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.block_prod_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:104`).

**Theorem: Negation preserves an absolute bound.** A bound on the absolute value of x also bounds the absolute value of −x. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.abs_neg_le` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:203`).

**Theorem: Bounds for the velocity-piece block.** The velocity-piece block term has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.muBlock_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:207`).

**Theorem: Curl-piece block term remainder bound.** The curl-piece block term has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundBlock.epsBlock_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundBlock.lean:257`).

### Breakdown.Cert.CoercivePieceDensityPassageDiffBoundEps

The curl-piece edge terms are normalized into bounded coefficients and amplitude products, yielding their common remainder difference estimate.

**Paper context:** Appendix B, Proposition B.1: difference control for curl-piece remainders.

**Theorem: Bound a coefficient times a sign.** The stated bounds on a coefficient and a factor of absolute value at most one bound the magnitude of their product. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundEps.coeff_le_of` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundEps.lean:16`).

**Theorem: Rescale boundary coefficients and data.** Multiplying every harmonic coefficient by a nonzero common scalar and dividing every amplitude by it leaves the edge sum unchanged. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundEps.edgeSum_scale` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundEps.lean:21`).

**Theorem: Boundary terms satisfy remainder bounds.** The stated coefficient, amplitude, and harmonic boundary sum satisfy the uniform amplitude and adjustable quadratic difference bounds. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundEps.edge_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundEps.lean:35`).

**Theorem: Curl-piece remainder remainder bound.** The curl-piece remainder has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundEps.epsRest_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundEps.lean:65`).

### Breakdown.Cert.CoercivePieceDensityPassageDiffBoundMu

The velocity-piece boundary sum is expanded into selected shifted products and bounded coefficientwise to establish its remainder difference estimate.

**Paper context:** Appendix B, Proposition B.1: difference control for velocity-piece remainders.

**Theorem: Proposition indicators are nonnegative.** The real-valued indicator of a proposition is nonnegative. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundMu.ind_nonneg` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundMu.lean:18`).

**Theorem: An indicator is at most one.** The real-valued indicator of a proposition is at most one. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundMu.ind_le_one` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundMu.lean:22`).

**Theorem: Boundary selectors lie in the unit range.** The nested conditional boundary selector takes values between zero and one. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundMu.ite_nonneg_le_one` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundMu.lean:26`).

**Theorem: Expand the scaled boundary sum.** A scalar multiple of the edge sum equals the explicit finite harmonic sum of the two directed boundary selectors and shifted amplitudes. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundMu.mul_edgeSum_eq` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundMu.lean:31`).

**Theorem: Equal remainders share their bounds.** The stated equality of remainders transfers the uniform amplitude and adjustable quadratic difference bounds to the second remainder. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundMu.isRestBound_congr` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundMu.lean:49`).

**Theorem: Bound a three-factor edge coefficient.** The stated absolute bounds on the first two factors and the unit bound on the selector give |a x e| ≤ A X. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundMu.coeff_le` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundMu.lean:61`).

**Theorem: Velocity-piece remainder remainder bound.** The velocity-piece remainder has the common uniform amplitude bound and adjustable quadratic difference bound. Source: `Breakdown.Coercive.Internal.PiecePassageDiffBoundMu.muRest_bound` (`Breakdown/Cert/CoercivePieceDensityPassageDiffBoundMu.lean:71`).

### Breakdown.Cert.CoercivePieceDensityPassageLimit

A general signed lower-bound theorem combines convergence of the negative density side with a lower-liminf bound on the positive side; period-pairing lemmas supply the scalar limit.

**Paper context:** Appendix B, Proposition B.1: the abstract limit step for the piece-density inequality.

**Definition: Positive terms in the split bound.** Add the positive mode, remainder, block, and stretching contributions as nonnegative extended reals. Source: `Breakdown.Coercive.splitLeft` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:12`).

**Definition: Negative terms in the split bound.** Add the negative parts of the mode remainder, block, and stretching terms as nonnegative extended reals. Source: `Breakdown.Coercive.splitRight` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:16`).

**Definition: The weak equation's limiting source.** Add weak transport, negative second-derivative trace, both convection terms, and the actuator combination. Source: `Breakdown.Coercive.rightSideLimit` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:19`).

**Theorem: Read the signed lower-bound conditions.** The split lower-bound specification is equivalent to finite negative remainder energy together with its positive-versus-negative integrated inequality. Source: `Breakdown.Coercive.Internal.PassageLimit.isSplitLowerBound_iff` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:26`).

**Theorem: Pass a signed lower bound to a limit.** Convergence of the negative side and source value, together with the positive-side lower-liminf bound, preserves the split lower-bound specification. Source: `Breakdown.Coercive.Internal.PassageLimit.isSplitLowerBound_of_liminf` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:34`).

**Theorem: Field pairing is integrable.** Under the stated hypotheses, the field pairing is integrable. Source: `Breakdown.Coercive.Internal.PassageLimit.period_integrable_inner` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:84`).

**Theorem: Pair over the period product measure.** The iterated period pairing equals the inner-product integral over the unit time-slab product measure. Source: `Breakdown.Coercive.Internal.PassageLimit.periodPairing_eq_integral` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:117`).

**Theorem: Subtract in the second pairing slot.** The difference of two period pairings with the same first field equals the pairing with the difference of their second fields. Source: `Breakdown.Coercive.Internal.PassageLimit.periodPairing_sub_right` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:125`).

**Theorem: L² convergence preserves a fixed pairing.** The period pairing with a fixed L² field converges when the second field converges in period L². Source: `Breakdown.Coercive.Internal.PassageLimit.periodPairing_tendsto_right` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:149`).

**Theorem: The period pairing is symmetric.** Interchanging the two real vector fields leaves the period pairing unchanged. Source: `Breakdown.Coercive.Internal.PassageLimit.periodPairing_comm` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:179`).

**Theorem: Expand a pairing about reference fields.** The period pairing equals the pairing of both discrepancies plus the two cross pairings with reference fields minus the reference pairing. Source: `Breakdown.Coercive.Internal.PassageLimit.periodPairing_expand` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:187`).

**Theorem: Pairings converge when both fields vary.** The period pairings converge to the limiting pairing under the stated period L² convergence of both fields. Source: `Breakdown.Coercive.Internal.PassageLimit.periodPairing_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:222`).

**Theorem: Period integration preserves order.** An almost-everywhere pointwise bound implies the same bound between the nonnegative period integrals. Source: `Breakdown.Coercive.Internal.PassageLimit.periodLIntegral_mono` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:263`).

**Theorem: Integrate a pointwise weighted bound.** The pointwise nonnegative bound f ≤ Cg yields the corresponding period-integral bound with the converted scalar C. Source: `Breakdown.Coercive.Internal.PassageLimit.periodLIntegral_le_mul` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:267`).

**Theorem: Integrate directly over the period slab.** The iterated nonnegative period integral equals the integral over the period product measure. Source: `Breakdown.Coercive.Internal.PassageLimit.periodLIntegral_eq_prod` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:277`).

**Theorem: Period integral preserves addition.** Under the stated hypotheses, the nonnegative period integral commutes with addition. Source: `Breakdown.Coercive.Internal.PassageLimit.periodLIntegral_add` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:288`).

**Theorem: Finite L² energy from a comparison.** The stated pointwise comparison with finite period square energy implies finite period square energy for the target field. Source: `Breakdown.Coercive.Internal.PassageLimit.periodL2_of_le` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:306`).

**Theorem: Sums retain finite period L² energy.** The sum of two fields with finite period squared energies has finite period squared energy. Source: `Breakdown.Coercive.Internal.PassageLimit.periodL2_add` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:311`).

**Theorem: Finite sums retain period L² control.** A finite sum of the stated fields is almost-everywhere strongly measurable and has finite squared energy over one period. Source: `Breakdown.Coercive.Internal.PassageLimit.periodL2_sum` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:334`).

**Theorem: Second-derivative trace is continuous.** Under the stated hypotheses, the second-derivative trace is continuous. Source: `Breakdown.Coercive.Internal.PassageLimit.continuous_secondDerivTrace` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:350`).

**Theorem: Spatial derivative is continuous.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.Internal.PassageLimit.continuous_fderiv_of_contDiff_two` (`Breakdown/Cert/CoercivePieceDensityPassageLimit.lean:354`).

### Breakdown.Cert.CoercivePieceDensityPassageMeasurable

The positive piece term, piece remainder, and block correction are made measurable, including the iterated integrals on the positive density side.

**Paper context:** Appendix B, Proposition B.1: measurable piece-density expressions.

**Theorem: The piece block is nonpositive.** The piece block correction is at most zero under the stated piece-weight and amplitude hypotheses. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMeasure.pieceBlock_nonpos` (`Breakdown/Cert/CoercivePieceDensityPassageMeasurable.lean:21`).

**Theorem: Piece density terms are measurable.** The positive piece contribution and piece remainder are measurable up to null sets for the stated weak field and derivative data. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMeasure.piece_parts_aemeasurable_of` (`Breakdown/Cert/CoercivePieceDensityPassageMeasurable.lean:29`).

**Theorem: Smooth piece terms are measurable.** For the stated smooth perturbation, the positive piece contribution and piece remainder are measurable up to null sets. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMeasure.piece_parts_aemeasurable` (`Breakdown/Cert/CoercivePieceDensityPassageMeasurable.lean:125`).

**Theorem: Piece multiplier block is measurable.** Under the stated hypotheses, the piece multiplier block is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMeasure.pieceBlock_aemeasurable_of` (`Breakdown/Cert/CoercivePieceDensityPassageMeasurable.lean:134`).

**Theorem: Measurability of the positive split.** The positive density split is measurable up to a null set on almost every spatial slice, and its spatial integral is measurable in time up to a null set. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMeasure.pieceSplitLeft_aemeasurable` (`Breakdown/Cert/CoercivePieceDensityPassageMeasurable.lean:190`).

### Breakdown.Cert.CoercivePieceDensityPassageMultiplier

Norm uniqueness and subtraction of variational multiplier representatives yield period L² convergence of the multipliers along a smooth approximation.

**Paper context:** Appendix B, Proposition B.1: convergence of piece multiplier fields.

**Theorem: Multiplier representatives have one norm.** Two fields satisfying the multiplier specification for the same data have equal period norms. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMultiplier.multiplier_norm_eq` (`Breakdown/Cert/CoercivePieceDensityPassageMultiplier.lean:20`).

**Theorem: Integral preserves subtraction.** Under the stated hypotheses, the integral commutes with subtraction. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMultiplier.iterated_sub` (`Breakdown/Cert/CoercivePieceDensityPassageMultiplier.lean:63`).

**Theorem: Field pairing preserves subtraction.** Under the stated hypotheses, the field pairing commutes with subtraction. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMultiplier.pairing_sub` (`Breakdown/Cert/CoercivePieceDensityPassageMultiplier.lean:72`).

**Theorem: Subtract multiplier fields.** Subtracting two multiplier fields gives a multiplier field for the corresponding velocity, gradient, and second-derivative differences. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMultiplier.multiplier_sub` (`Breakdown/Cert/CoercivePieceDensityPassageMultiplier.lean:83`).

**Theorem: Multipliers converge in period L².** The squared period L² distance from each approximating multiplier to the limiting multiplier tends to zero. Source: `Breakdown.Coercive.Internal.PieceDensityPassageMultiplier.multiplier_tendsto_of` (`Breakdown/Cert/CoercivePieceDensityPassageMultiplier.lean:153`).

### Breakdown.Cert.CoercivePieceDensityPassageRest

The absolute and negative integrals of the piece remainders and block correction are finite, ensuring that the negative density side can be passed to a limit.

**Paper context:** Appendix B, Proposition B.1: finite negative mass in the piece-density argument.

**Theorem: Absolute piece remainders are integrable.** The period integral of the sum of the absolute piece remainders is finite. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRest.rest_abs_finite` (`Breakdown/Cert/CoercivePieceDensityPassageRest.lean:19`).

**Theorem: The absolute piece block is integrable.** The absolute piece-block correction has finite integral over one time period. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRest.block_abs_finite` (`Breakdown/Cert/CoercivePieceDensityPassageRest.lean:42`).

**Theorem: Negative piece remainders are integrable.** The period integral of the sum of the negative parts of the piece remainders is finite. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRest.rest_negative_finite` (`Breakdown/Cert/CoercivePieceDensityPassageRest.lean:66`).

**Theorem: The negative piece block is integrable.** The negative part of the piece-block correction has finite integral over one time period. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRest.block_negative_finite` (`Breakdown/Cert/CoercivePieceDensityPassageRest.lean:83`).

**Theorem: The integrated negative split is finite.** The integrated negative density side, including its remainder, block, and stretching contributions, is finite. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRest.right_finite_of` (`Breakdown/Cert/CoercivePieceDensityPassageRest.lean:99`).

### Breakdown.Cert.CoercivePieceDensityPassageRestBase

Uniform bounds on the base-density coefficients control its absolute value by the combined Hessian, curl-gradient, gradient, curl, and weighted velocity amplitudes.

**Paper context:** Appendix B, Proposition B.1: the base part of the piece-remainder bound.

**Theorem: Bound a coefficient times a square.** An absolute bound |a| ≤ A gives |a x²| ≤ A x². Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestBase.abs_coef_sq_le` (`Breakdown/Cert/CoercivePieceDensityPassageRestBase.lean:14`).

**Theorem: Bound the base quadratic density.** The absolute base quadratic density is bounded by the stated sum of coefficient bounds times the combined Hessian, curl-gradient, gradient, curl, and weighted velocity squares. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestBase.base_abs_le` (`Breakdown/Cert/CoercivePieceDensityPassageRestBase.lean:18`).

**Theorem: A uniform base-density amplitude bound.** One nonnegative constant bounds every base-density term by the sum of the five stated squared amplitudes, including radial damping of velocity. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestBase.base_pointwise` (`Breakdown/Cert/CoercivePieceDensityPassageRestBase.lean:68`).

### Breakdown.Cert.CoercivePieceDensityPassageRestEps

The negative curl-piece remainder and block terms are bounded by sums of mode energies with explicit weight, harmonic, frame, and background factors.

**Paper context:** Appendix B, Proposition B.1: finite-energy control of negative curl-piece terms.

**Theorem: Control negative curl remainders.** The sum of the negative curl-piece remainder parts is bounded by the stated harmonic-count factor times the curl, curl-gradient, gradient, and weighted velocity mode energies. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestEps.epsRest_pointwise` (`Breakdown/Cert/CoercivePieceDensityPassageRestEps.lean:16`).

**Theorem: Control the negative curl block.** The negative curl block is bounded by the stated weight, frame, and background constant times the four corresponding mode-energy sums. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestEps.epsBlock_pointwise` (`Breakdown/Cert/CoercivePieceDensityPassageRestEps.lean:92`).

### Breakdown.Cert.CoercivePieceDensityPassageRestMu

Velocity-piece boundary and negative block contributions are bounded by gradient and radially damped velocity mode energies.

**Paper context:** Appendix B, Proposition B.1: finite-energy control of negative velocity-piece terms.

**Theorem: Control the velocity boundary sum.** The velocity boundary-interaction sum is bounded by the stated weight and background factor times the harmonic count and weighted velocity-plus-gradient energies. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestMu.muEdge_pointwise` (`Breakdown/Cert/CoercivePieceDensityPassageRestMu.lean:16`).

**Theorem: Control the negative velocity block.** The negative velocity block is bounded by the stated weight, frame, and background constant times the gradient and radially weighted velocity mode energies. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestMu.muBlock_pointwise` (`Breakdown/Cert/CoercivePieceDensityPassageRestMu.lean:59`).

### Breakdown.Cert.CoercivePieceDensityPassageRestSum

The separate amplitude families are bounded by one total mode energy, allowing all absolute piece remainders to be summed under a common finite constant.

**Paper context:** Appendix B, Proposition B.1: summing the piece-remainder energy bounds.

**Theorem: Square the complex-array norm root.** Squaring the nonnegative square root of the complex-array norm square returns that norm square. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestSum.sq_sqrt_cnormSq` (`Breakdown/Cert/CoercivePieceDensityPassageRestSum.lean:18`).

**Theorem: Identify the combined amplitude energy.** The sum of the Hessian, curl-gradient, gradient, curl, and radially weighted velocity amplitude squares equals the defined combined mode energy. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestSum.ampSq_eq` (`Breakdown/Cert/CoercivePieceDensityPassageRestSum.lean:21`).

**Theorem: Each amplitude energy is below the total.** Each of the curl, curl-gradient, gradient, and weighted velocity square sums is bounded by the total combined mode energy. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestSum.families_le` (`Breakdown/Cert/CoercivePieceDensityPassageRestSum.lean:27`).

**Theorem: Bound a signed finite remainder sum.** The absolute finite remainder sum is bounded in nonnegative extended reals by its base magnitude, negative curl contributions, and the stated velocity bounds. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestSum.ofReal_abs_split` (`Breakdown/Cert/CoercivePieceDensityPassageRestSum.lean:46`).

**Theorem: Uniform control of all piece remainders.** A finite nonnegative extended-real constant bounds the sum of absolute piece remainders by the total combined mode energy at every space-time point. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestSum.rest_tsum_le` (`Breakdown/Cert/CoercivePieceDensityPassageRestSum.lean:72`).

**Theorem: Absorb a product of piece norms.** The product of two piece norms is bounded by the allocated weighted sums of their squared amplitudes under the stated coefficient inequality. Source: `Breakdown.Coercive.Internal.PieceDensityPassageRestSum.block_le` (`Breakdown/Cert/CoercivePieceDensityPassageRestSum.lean:192`).

### Breakdown.Cert.CoercivePieceDensityPassageRight

The explicit limiting equation source is compared with the smooth source, using weighted velocity, Hessian-trace, and background derivative bounds to prove period L² convergence.

**Paper context:** Appendix B, Proposition B.1: convergence of the equation's right-hand side.

**Theorem: The limiting source has finite L² energy.** The limiting equation source is almost-everywhere strongly measurable and has finite squared energy over one time period. Source: `Breakdown.Coercive.Internal.PassageLimit.rightSideLimit_memL2` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:15`).

**Theorem: Finite weighted period velocity energy.** The period integral of ‖v‖² divided by (1 + ‖y‖)² is finite under the perturbation hypotheses. Source: `Breakdown.Coercive.Internal.PassageLimit.weightedVelocity_lt_top` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:96`).

**Theorem: Identify the smooth equation source.** The smooth equation source plus its actuator combination equals the limiting-source formula evaluated on the smooth field and its derivatives and transport term. Source: `Breakdown.Coercive.Internal.PassageLimit.smoothRight_add_eq` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:130`).

**Theorem: The smooth source has finite L² energy.** Each smooth approximation source with its actuator combination is almost-everywhere strongly measurable and has finite squared energy over one period. Source: `Breakdown.Coercive.Internal.PassageLimit.smoothRight_memL2` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:136`).

**Theorem: Decay bounds the background field.** The background decay assumption bounds the field norm by the absolute decay constant. Source: `Breakdown.Coercive.Internal.PassageLimit.norm_field_le_abs` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:149`).

**Theorem: A weighted derivative action bound.** The squared norm of the background derivative applied to x is at most the squared decay constant times ‖x‖² divided by (1 + ‖y‖)². Source: `Breakdown.Coercive.Internal.PassageLimit.norm_fderiv_field_apply_sq_le` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:161`).

**Theorem: Second-derivative square is continuous.** Under the stated hypotheses, the squared second-derivative norm is continuous. Source: `Breakdown.Coercive.Internal.PassageLimit.continuous_secondDerivSq` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:183`).

**Theorem: Second-derivative square is nonnegative.** The squared second-derivative norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.PassageLimit.secondDerivSq_nonneg` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:188`).

**Theorem: Squared matrix norm is nonnegative.** The squared matrix norm is nonnegative for the stated data. Source: `Breakdown.Coercive.Internal.PassageLimit.matSq_nonneg'` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:191`).

**Theorem: Bound the trace square by Hessian energy.** The squared norm of the second-derivative trace is at most three times the full second-derivative square. Source: `Breakdown.Coercive.Internal.PassageLimit.traceSq_le_three_secondDerivSq` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:194`).

**Theorem: Expand a limiting-source difference.** The limiting-source difference is the transport discrepancy minus the trace discrepancy plus the two background convection discrepancies, with the common actuators cancelling. Source: `Breakdown.Coercive.Internal.PassageLimit.rightSideLimit_sub` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:212`).

**Theorem: Bound the square of four summed vectors.** The squared norm of a sum of four vectors is at most four times the sum of their squared norms. Source: `Breakdown.Coercive.Internal.PassageLimit.norm_add_four_sq_le` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:221`).

**Theorem: Equation sources converge in period L².** The squared period L² distance between the smooth source with actuators and the explicit limiting source tends to zero. Source: `Breakdown.Coercive.Internal.PassageLimit.smoothRight_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassageRight.lean:232`).

### Breakdown.Cert.CoercivePieceDensityPassageSubsequence

Absolute remainder and block discrepancies vanish in integral, and a common subsequence combines convergence of the negative side with lower semicontinuity of the positive side.

**Paper context:** Appendix B, Proposition B.1: selecting a subsequence for the signed piece-density limit.

**Theorem: Total remainder discrepancy vanishes.** The integral of the sum of the absolute piece-remainder discrepancies tends to zero. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.rest_abs_sub_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:21`).

**Theorem: Block discrepancies vanish in period L¹.** The period integral of the absolute piece-block discrepancy tends to zero. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.block_abs_sub_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:45`).

**Theorem: Negative remainder integrals converge.** The integrated sum of the negative piece-remainder parts converges to the corresponding weak-field integral. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.rest_negative_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:78`).

**Theorem: Negative block integrals converge.** The integral of the negative piece-block part converges to the corresponding weak-field integral. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.block_negative_tendsto` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:112`).

**Theorem: Stretching form is measurable.** Under the stated hypotheses, the stretching form is measurable up to a null set. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.stretchForm_aemeasurable` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:143`).

**Theorem: Choose simultaneous piece convergence.** One strictly increasing subsequence makes every positive piece term, every piece remainder, and the stretching form converge almost everywhere to the weak-field values. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.pieces_converge_ae` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:159`).

**Theorem: Nonpositive blocks have no positive part.** When the block is nonpositive, the positive density split is unchanged by replacing that block with zero. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.splitLeft_block_eq` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:184`).

**Theorem: Separate the integrated negative split.** The integrated negative density side equals the sum of the negative stretching integral, negative remainder-series integral, and negative block integral. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.splitRight_split` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:189`).

**Theorem: Control both sides along a subsequence.** One strictly increasing subsequence gives convergence of the integrated negative side and an almost-everywhere lower-liminf bound for the positive side. Source: `Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.subsequence_limits_of` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequence.lean:204`).

### Breakdown.Cert.CoercivePieceDensityPassageSubsequenceModes

One subsequence makes all velocity, gradient, and Hessian modes converge almost everywhere, which yields the pointwise piece and stretching limits.

**Paper context:** Appendix B, Proposition B.1: simultaneous mode convergence for piece-density passage.

**Theorem: A fixed zero selector preserves limits.** Replacing a convergent sequence and its limit by zero under the same fixed condition preserves convergence. Source: `Breakdown.Coercive.Internal.PiecePassageModes.tendsto_ite_zero` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequenceModes.lean:16`).

**Theorem: Boundary sums preserve amplitude limits.** Pointwise convergence of the amplitude sequence implies convergence of each finite harmonic boundary sum. Source: `Breakdown.Coercive.Internal.PiecePassageModes.tendsto_edgeSum` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequenceModes.lean:25`).

**Theorem: Mode convergence gives piece convergence.** The stated pointwise field and mode convergence implies convergence of every positive piece contribution, every piece remainder, and the stretching form. Source: `Breakdown.Coercive.Internal.PiecePassageModes.piece_limits_of_modes` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequenceModes.lean:38`).

**Theorem: Choose convergence of all mode fields.** One strictly increasing subsequence makes all velocity, gradient, and Hessian modes and the physical velocity and gradient converge almost everywhere. Source: `Breakdown.Coercive.Internal.PiecePassageModes.ae_subseq_modes` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequenceModes.lean:100`).

**Theorem: Absorbable error integrals vanish.** The stated adjustable absorption bound implies that the nonnegative error's period integral tends to zero. Source: `Breakdown.Coercive.Internal.PiecePassageModes.tendsto_of_absorb_bound` (`Breakdown/Cert/CoercivePieceDensityPassageSubsequenceModes.lean:144`).

### Breakdown.Cert.CoercivePieceField

The piece-weight pairing is shown to be linear, summable, and bounded by the test-field period norm, giving the variational multiplier field and its quantitative estimate.

**Paper context:** Appendix B, Proposition B.1: existence and norm control of the piece multiplier field.

**Definition: Pair the negative second derivative.** Pair the negative second-derivative trace with a test field over space and one period. Source: `Breakdown.Coercive.PieceField.Internal.secondDerivPairing` (`Breakdown/Cert/CoercivePieceField.lean:21`).

**Definition: One mode of the piece multiplier.** Add the signed curl-piece and velocity-piece pairings at the selected mode and point. Source: `Breakdown.Coercive.PieceField.Internal.pieceIntegrand` (`Breakdown/Cert/CoercivePieceField.lean:24`).

**Definition: Sum the piece multiplier pairings.** Sum the space-time integrals of the piece-multiplier integrand over all modes. Source: `Breakdown.Coercive.PieceField.Internal.pieceModeSum` (`Breakdown/Cert/CoercivePieceField.lean:31`).

**Theorem: Combine two energy contributions.** The sum α√E + βS is bounded by the weighted dual coefficient norm times √(cE + cμS²) under the stated positivity assumptions. Source: `Breakdown.Coercive.PieceField.Internal.scalar_pair_bound` (`Breakdown/Cert/CoercivePieceField.lean:35`).

**Theorem: Combine the multiplier coefficients.** The trace, gradient, and velocity-piece contributions are bounded by the explicit coefficient factor times the combined weighted energy square root. Source: `Breakdown.Coercive.PieceField.Internal.coef_le` (`Breakdown/Cert/CoercivePieceField.lean:45`).

**Theorem: Period integration preserves order.** An almost-everywhere pointwise bound implies the same bound between the nonnegative period integrals. Source: `Breakdown.Coercive.PieceField.Internal.periodLIntegral_mono` (`Breakdown/Cert/CoercivePieceField.lean:65`).

**Theorem: Period integral preserves scaling.** Under the stated hypotheses, the nonnegative period integral commutes with multiplication by a constant. Source: `Breakdown.Coercive.PieceField.Internal.periodLIntegral_const_mul` (`Breakdown/Cert/CoercivePieceField.lean:69`).

**Theorem: Restrict volume to one time slab.** Restricting space-time volume to the unit time slab gives the product of restricted time volume and spatial volume. Source: `Breakdown.Coercive.PieceField.Internal.restrict_eq_prod` (`Breakdown/Cert/CoercivePieceField.lean:78`).

**Theorem: Integrate directly over the period slab.** The iterated nonnegative period integral equals the integral over the period product measure. Source: `Breakdown.Coercive.PieceField.Internal.periodLIntegral_eq_prod` (`Breakdown/Cert/CoercivePieceField.lean:82`).

**Theorem: Subadditivity of the period integral.** The nonnegative period integral of a pointwise sum is at most the sum of the two period integrals. Source: `Breakdown.Coercive.PieceField.Internal.periodLIntegral_add_le` (`Breakdown/Cert/CoercivePieceField.lean:88`).

**Theorem: The squared trace norm is continuous.** The squared norm of the second-derivative trace depends continuously on its tensor argument. Source: `Breakdown.Coercive.PieceField.Internal.continuous_secondDerivTrace_sq` (`Breakdown/Cert/CoercivePieceField.lean:97`).

**Theorem: Second-derivative trace is continuous.** Under the stated hypotheses, the second-derivative trace is continuous. Source: `Breakdown.Coercive.PieceField.Internal.continuous_secondDerivTrace` (`Breakdown/Cert/CoercivePieceField.lean:102`).

**Theorem: Squared matrix norm is continuous.** Under the stated hypotheses, the squared matrix norm is continuous. Source: `Breakdown.Coercive.PieceField.Internal.continuous_matSq` (`Breakdown/Cert/CoercivePieceField.lean:107`).

**Theorem: Squared matrix norm is nonnegative.** The squared matrix norm is nonnegative for the stated data. Source: `Breakdown.Coercive.PieceField.Internal.matSq_nonneg` (`Breakdown/Cert/CoercivePieceField.lean:111`).

**Theorem: Test fields are strongly measurable.** The joint periodic test field is strongly measurable up to a null set. Source: `Breakdown.Coercive.PieceField.Internal.testField_aesm` (`Breakdown/Cert/CoercivePieceField.lean:114`).

**Theorem: Test fields have finite period L² energy.** The squared norm of the stated periodic test field has finite integral over one period. Source: `Breakdown.Coercive.PieceField.Internal.testField_sq_lt_top` (`Breakdown/Cert/CoercivePieceField.lean:118`).

**Theorem: Field pairing is integrable.** Under the stated hypotheses, the field pairing is integrable. Source: `Breakdown.Coercive.PieceField.Internal.integrable_inner_prod` (`Breakdown/Cert/CoercivePieceField.lean:147`).

**Theorem: Fourier mode average preserves scaling.** Under the stated hypotheses, the Fourier mode average commutes with multiplication by a constant. Source: `Breakdown.Coercive.PieceField.Internal.modeAverage_const_mul` (`Breakdown/Cert/CoercivePieceField.lean:173`).

**Theorem: Velocity mode preserves scaling.** Under the stated hypotheses, the velocity mode commutes with scalar multiplication. Source: `Breakdown.Coercive.PieceField.Internal.modeVel_smul` (`Breakdown/Cert/CoercivePieceField.lean:180`).

**Theorem: Gradient field preserves scaling.** Under the stated hypotheses, the gradient field commutes with scalar multiplication. Source: `Breakdown.Coercive.PieceField.Internal.gradField_smul` (`Breakdown/Cert/CoercivePieceField.lean:187`).

**Theorem: Gradient mode preserves scaling.** Under the stated hypotheses, the gradient mode commutes with scalar multiplication. Source: `Breakdown.Coercive.PieceField.Internal.modeGrad_smul` (`Breakdown/Cert/CoercivePieceField.lean:192`).

**Theorem: Curl respects scalar multiplication.** Multiplying every gradient coordinate by a real scalar multiplies its complex curl contraction by that scalar. Source: `Breakdown.Coercive.PieceField.Internal.curlOfGrad_smul` (`Breakdown/Cert/CoercivePieceField.lean:201`).

**Theorem: Scale the second complex pairing slot.** Multiplying the second complex-vector argument by a real scalar multiplies the complex pairing by that scalar. Source: `Breakdown.Coercive.PieceField.Internal.cdot_smul` (`Breakdown/Cert/CoercivePieceField.lean:207`).

**Theorem: Move a real scalar outside the real part.** A real scalar factor can be moved outside the real part of the weighted imaginary complex product. Source: `Breakdown.Coercive.PieceField.Internal.re_smul_aux` (`Breakdown/Cert/CoercivePieceField.lean:212`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.PieceField.Internal.axialRot_continuous` (`Breakdown/Cert/CoercivePieceField.lean:215`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.PieceField.Internal.axialRot_comp_continuous` (`Breakdown/Cert/CoercivePieceField.lean:219`).

**Theorem: Coordinate projections are continuous.** Each Euclidean coordinate projection is continuous. Source: `Breakdown.Coercive.PieceField.Internal.space_apply_continuous` (`Breakdown/Cert/CoercivePieceField.lean:224`).

**Theorem: A test field has differentiable slices.** Each spatial slice of the stated periodic test field is differentiable at the selected point. Source: `Breakdown.Coercive.PieceField.Internal.slice_differentiableAt` (`Breakdown/Cert/CoercivePieceField.lean:227`).

**Theorem: The spatial part of the joint derivative.** The gradient field equals the joint space-time derivative restricted to pure spatial directions. Source: `Breakdown.Coercive.PieceField.Internal.gradField_eq` (`Breakdown/Cert/CoercivePieceField.lean:231`).

**Theorem: Gradient field is continuous.** Under the stated hypotheses, the gradient field is continuous. Source: `Breakdown.Coercive.PieceField.Internal.gradField_continuous` (`Breakdown/Cert/CoercivePieceField.lean:238`).

**Theorem: Gradient field preserves addition.** Under the stated hypotheses, the gradient field commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.gradField_add` (`Breakdown/Cert/CoercivePieceField.lean:245`).

**Theorem: Integral preserves addition.** Under the stated hypotheses, the integral commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.iter_integral_add` (`Breakdown/Cert/CoercivePieceField.lean:251`).

**Theorem: The Fourier phase is continuous.** The complex exponential Fourier phase is continuous in the time-angle parameters. Source: `Breakdown.Coercive.PieceField.Internal.phase_continuous` (`Breakdown/Cert/CoercivePieceField.lean:264`).

**Theorem: Fourier mode average preserves addition.** Under the stated hypotheses, the Fourier mode average commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.modeAverage_add` (`Breakdown/Cert/CoercivePieceField.lean:269`).

**Theorem: Velocity-mode orbit integrand continuity.** Under the stated hypotheses, the velocity-mode orbit integrand is continuous. Source: `Breakdown.Coercive.PieceField.Internal.vel_integrand_continuous` (`Breakdown/Cert/CoercivePieceField.lean:286`).

**Theorem: Gradient-mode orbit integrand continuity.** Under the stated hypotheses, the gradient-mode orbit integrand is continuous. Source: `Breakdown.Coercive.PieceField.Internal.grad_integrand_continuous` (`Breakdown/Cert/CoercivePieceField.lean:297`).

**Theorem: Velocity mode preserves addition.** Under the stated hypotheses, the velocity mode commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.modeVel_add` (`Breakdown/Cert/CoercivePieceField.lean:315`).

**Theorem: Gradient mode preserves addition.** Under the stated hypotheses, the gradient mode commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.modeGrad_add` (`Breakdown/Cert/CoercivePieceField.lean:323`).

**Theorem: Curl mode preserves addition.** Under the stated hypotheses, the curl extracted from a gradient commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.curlOfGrad_add` (`Breakdown/Cert/CoercivePieceField.lean:333`).

**Theorem: Field pairing preserves addition.** Under the stated hypotheses, the field pairing commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.cdot_add` (`Breakdown/Cert/CoercivePieceField.lean:338`).

**Theorem: Split the real weighted complex product.** The real part of a weighted imaginary product distributes over addition of its complex argument. Source: `Breakdown.Coercive.PieceField.Internal.re_add_aux` (`Breakdown/Cert/CoercivePieceField.lean:341`).

**Theorem: Add tests in the piece integrand.** Under the stated hypotheses, the piece-multiplier integrand commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.pieceIntegrand_add` (`Breakdown/Cert/CoercivePieceField.lean:344`).

**Theorem: Represent a bounded variational pairing.** The stated bounded linear pairing is represented by a periodic solenoidal L² field with the required norm bound. Source: `Breakdown.Coercive.PieceField.Internal.exists_field_of_bounded` (`Breakdown/Cert/CoercivePieceField.lean:354`).

**Theorem: Weighted control of both derivatives.** The weighted energy controls the trace energy and the gradient energy multiplied by the positive lower weight bound. Source: `Breakdown.Coercive.PieceField.Internal.energy_bounds` (`Breakdown/Cert/CoercivePieceField.lean:366`).

**Theorem: Bound the negative-Laplacian pairing.** The absolute negative-Laplacian pairing is at most the product of the two period L² norms. Source: `Breakdown.Coercive.PieceField.Internal.secondDerivPairing_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:406`).

**Theorem: Add tests in the Laplacian pairing.** The negative-Laplacian period pairing distributes over addition of its test-field argument. Source: `Breakdown.Coercive.PieceField.Internal.secondDerivPairing_add` (`Breakdown/Cert/CoercivePieceField.lean:424`).

**Theorem: Scale a test in the Laplacian pairing.** Multiplying the test field by a real scalar multiplies the negative-Laplacian period pairing by the same scalar. Source: `Breakdown.Coercive.PieceField.Internal.secondDerivPairing_smul` (`Breakdown/Cert/CoercivePieceField.lean:450`).

**Theorem: Weighted frequency energy is finite.** The total period mode energy weighted by the spatial weight and the absolute integer frequencies is finite. Source: `Breakdown.Coercive.PieceField.Internal.weightedFrequency_lt_top` (`Breakdown/Cert/CoercivePieceField.lean:456`).

**Theorem: Bound frame frequency by mode size.** The absolute frame frequency is at most (2π/P + |a|) times the sum of the absolute integer mode coordinates. Source: `Breakdown.Coercive.PieceField.Internal.frameFreq_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:465`).

**Theorem: A piece sign has magnitude at most one.** The absolute piece sign is at most one. Source: `Breakdown.Coercive.PieceField.Internal.sgn_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:477`).

**Theorem: Squared complex norm is nonnegative.** The squared complex norm is nonnegative for the stated data. Source: `Breakdown.Coercive.PieceField.Internal.cnormSq_nonneg` (`Breakdown/Cert/CoercivePieceField.lean:481`).

**Theorem: Complex-vector Cauchy-Schwarz.** The norm of the complex pairing is at most the product of the square-sum norms of its two vector arguments. Source: `Breakdown.Coercive.PieceField.Internal.cdot_norm_le` (`Breakdown/Cert/CoercivePieceField.lean:484`).

**Theorem: Bound a weighted imaginary real part.** The absolute real part of i c X is at most |c| times the complex norm of X for real c. Source: `Breakdown.Coercive.PieceField.Internal.re_I_mul_le` (`Breakdown/Cert/CoercivePieceField.lean:493`).

**Theorem: Bound the velocity-piece pairing.** The finite velocity-piece pairing sum is bounded by the square root of its frequency-weighted coefficient sum times the two complex-vector norms and the stated ratio factor. Source: `Breakdown.Coercive.PieceField.Internal.mu_part_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:497`).

**Theorem: Combine the curl-piece coefficients.** The sum of weighted imaginary real parts equals the same expression with the real coefficients summed first. Source: `Breakdown.Coercive.PieceField.Internal.eps_part_eq` (`Breakdown/Cert/CoercivePieceField.lean:523`).

**Theorem: Bound the combined curl coefficient.** The absolute sum of the signed curl-piece weights is bounded by the supplied uniform curl-weight bound. Source: `Breakdown.Coercive.PieceField.Internal.epsCoef_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:527`).

**Theorem: Bound the curl-coefficient derivative.** The derivative norm of the sum of signed curl-piece weights is bounded by the supplied uniform derivative bound. Source: `Breakdown.Coercive.PieceField.Internal.epsCoef_fderiv_le` (`Breakdown/Cert/CoercivePieceField.lean:536`).

**Definition: Volume over one time period.** Use the product of volume on the closed unit time interval and spatial volume. Source: `Breakdown.Coercive.PieceField.Internal.slabMeasure` (`Breakdown/Cert/CoercivePieceField.lean:602`).

**Definition: One weighted curl-mode pairing.** Take the real part of i times the coefficient and the complex pairing of the two curl modes. Source: `Breakdown.Coercive.PieceField.Internal.curlTerm` (`Breakdown/Cert/CoercivePieceField.lean:604`).

**Definition: One weighted velocity-mode pairing.** Take the real part of i times the coefficient and the complex pairing of the two velocity modes. Source: `Breakdown.Coercive.PieceField.Internal.velTerm` (`Breakdown/Cert/CoercivePieceField.lean:608`).

**Theorem: Curl-piece pairing term is measurable.** Under the stated hypotheses, the curl-piece pairing term is strongly measurable up to a null set. Source: `Breakdown.Coercive.PieceField.Internal.curlTerm_aesm` (`Breakdown/Cert/CoercivePieceField.lean:612`).

**Theorem: Measurable velocity-piece pairings.** Under the stated hypotheses, the velocity-piece pairing term is strongly measurable up to a null set. Source: `Breakdown.Coercive.PieceField.Internal.velTerm_aesm` (`Breakdown/Cert/CoercivePieceField.lean:628`).

**Theorem: Test gradients have finite period energy.** The period integral of the squared coordinate-column norm of the test-field gradient is finite. Source: `Breakdown.Coercive.PieceField.Internal.gradField_matSq_lt_top` (`Breakdown/Cert/CoercivePieceField.lean:644`).

**Theorem: Curl-piece pairing term is integrable.** Under the stated hypotheses, the curl-piece pairing term is integrable. Source: `Breakdown.Coercive.PieceField.Internal.curlTerm_integrable` (`Breakdown/Cert/CoercivePieceField.lean:653`).

**Theorem: Curl-piece pairing term is summable.** Under the stated hypotheses, the curl-piece pairing term is summable over its index set. Source: `Breakdown.Coercive.PieceField.Internal.curlTerm_summable` (`Breakdown/Cert/CoercivePieceField.lean:672`).

**Theorem: Truncation preserves velocity testing.** Replacing the velocity by its stated ball truncation leaves the velocity-mode pairing term unchanged under the test-support hypotheses. Source: `Breakdown.Coercive.PieceField.Internal.velTerm_ballPart` (`Breakdown/Cert/CoercivePieceField.lean:699`).

**Theorem: Integrable velocity-piece pairings.** Under the stated hypotheses, the velocity-piece pairing term is integrable. Source: `Breakdown.Coercive.PieceField.Internal.velTerm_integrable` (`Breakdown/Cert/CoercivePieceField.lean:708`).

**Theorem: Velocity-piece pairing term is summable.** Under the stated hypotheses, the velocity-piece pairing term is summable over its index set. Source: `Breakdown.Coercive.PieceField.Internal.velTerm_summable` (`Breakdown/Cert/CoercivePieceField.lean:732`).

**Definition: Signed coefficient of a curl piece.** Multiply the curl piece's signed mode membership by its spatial weight. Source: `Breakdown.Coercive.PieceField.Internal.epsCoefOf` (`Breakdown/Cert/CoercivePieceField.lean:757`).

**Definition: Signed coefficient of a velocity piece.** Multiply the velocity piece's signed mode membership by its spatial weight. Source: `Breakdown.Coercive.PieceField.Internal.muCoefOf` (`Breakdown/Cert/CoercivePieceField.lean:760`).

**Theorem: Split the piece multiplier integrand.** The piece multiplier integrand equals the finite sum of its curl terms plus the finite sum of its velocity terms. Source: `Breakdown.Coercive.PieceField.Internal.pieceIntegrand_eq` (`Breakdown/Cert/CoercivePieceField.lean:763`).

**Theorem: Continuous curl-piece coefficients.** Under the stated hypotheses, the signed coefficient of a curl piece is continuous. Source: `Breakdown.Coercive.PieceField.Internal.epsCoefOf_continuous` (`Breakdown/Cert/CoercivePieceField.lean:768`).

**Theorem: Continuous velocity-piece coefficients.** Under the stated hypotheses, the signed coefficient of a velocity piece is continuous. Source: `Breakdown.Coercive.PieceField.Internal.muCoefOf_continuous` (`Breakdown/Cert/CoercivePieceField.lean:775`).

**Theorem: Bound one curl-piece coefficient.** Each signed curl-piece coefficient has absolute value at most the supplied uniform curl-weight bound. Source: `Breakdown.Coercive.PieceField.Internal.epsCoefOf_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:782`).

**Theorem: Bound one velocity-piece coefficient.** Each signed velocity-piece coefficient has absolute value at most the supplied weight bound. Source: `Breakdown.Coercive.PieceField.Internal.muCoefOf_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:793`).

**Theorem: All piece terms are slab-integrable.** Every curl-piece and velocity-piece pairing integrand is integrable over the unit time slab. Source: `Breakdown.Coercive.PieceField.Internal.pieceIntegrand_integrable_slab` (`Breakdown/Cert/CoercivePieceField.lean:802`).

**Theorem: Piece-multiplier integrand is integrable.** Under the stated hypotheses, the piece-multiplier integrand is integrable. Source: `Breakdown.Coercive.PieceField.Internal.pieceIntegrand_integrable` (`Breakdown/Cert/CoercivePieceField.lean:816`).

**Theorem: Summable integrated piece terms.** Under the stated hypotheses, the family of integrated piece-multiplier terms is summable over its index set. Source: `Breakdown.Coercive.PieceField.Internal.pieceIntegral_summable` (`Breakdown/Cert/CoercivePieceField.lean:830`).

**Definition: Sum of the curl-piece pairings.** Sum all curl-piece pairings over the pieces, modes, space, and one time period. Source: `Breakdown.Coercive.PieceField.Internal.epsModeSum` (`Breakdown/Cert/CoercivePieceField.lean:855`).

**Definition: Sum of the velocity-piece pairings.** Sum all velocity-piece pairings over the pieces, modes, space, and one time period. Source: `Breakdown.Coercive.PieceField.Internal.muModeSum` (`Breakdown/Cert/CoercivePieceField.lean:859`).

**Theorem: Separate the two piece pairing sums.** The full piece-mode pairing sum equals its curl-piece sum plus its velocity-piece sum. Source: `Breakdown.Coercive.PieceField.Internal.pieceModeSum_split` (`Breakdown/Cert/CoercivePieceField.lean:863`).

**Theorem: Bound an integrated curl mode.** The absolute integrated curl-mode pairing is bounded by the integral of the trace-mode and curl-mode amplitudes weighted by the coefficient bounds and multiplied by the test-mode amplitude. Source: `Breakdown.Coercive.PieceField.Internal.epsMode_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:897`).

**Theorem: Control the total curl-mode energy.** The sum of the integrated curl-mode squares is at most the physical gradient energy over one period. Source: `Breakdown.Coercive.PieceField.Internal.curlMode_squareSum_le` (`Breakdown/Cert/CoercivePieceField.lean:919`).

**Theorem: Young's inequality for two real factors.** For positive t, the product xy is bounded by half of tx² plus y²/t. Source: `Breakdown.Coercive.PieceField.Internal.mul_le_half_sq` (`Breakdown/Cert/CoercivePieceField.lean:965`).

**Theorem: Optimise the adjustable square bound.** The family of adjustable two-term bounds in the hypotheses implies s ≤ √X√Y. Source: `Breakdown.Coercive.PieceField.Internal.le_sqrt_mul_of_forall` (`Breakdown/Cert/CoercivePieceField.lean:972`).

**Theorem: Cauchy-Schwarz for summed mode integrals.** The sum of the integrated mode products is finite and bounded by the product of the square roots of the two summed square energies. Source: `Breakdown.Coercive.PieceField.Internal.tsum_lintegral_mul_le` (`Breakdown/Cert/CoercivePieceField.lean:1001`).

**Theorem: Bound the summed curl contribution.** The absolute sum of the curl-weight pairings is controlled by the stated trace and gradient energy factors times the test-field period norm. Source: `Breakdown.Coercive.PieceField.Internal.epsModeSum_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:1049`).

**Theorem: Bound the summed velocity contribution.** The absolute sum of velocity-weight pairings is controlled by the frequency or piece seminorm factor and the test-field period norm. Source: `Breakdown.Coercive.PieceField.Internal.muModeSum_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:1172`).

**Theorem: The piece pairing is norm-bounded.** The absolute piece-mode pairing sum is bounded by the trace, gradient, and weighted piece-seminorm factors times the period norm of the test field. Source: `Breakdown.Coercive.PieceField.Internal.pieceModeSum_abs_le` (`Breakdown/Cert/CoercivePieceField.lean:1301`).

**Theorem: Piece pairing sum preserves addition.** Under the stated hypotheses, the sum of piece pairings commutes with addition. Source: `Breakdown.Coercive.PieceField.Internal.pieceModeSum_add` (`Breakdown/Cert/CoercivePieceField.lean:1319`).

**Theorem: Piece pairing sum preserves scaling.** Under the stated hypotheses, the sum of piece pairings commutes with scalar multiplication. Source: `Breakdown.Coercive.PieceField.Internal.pieceModeSum_smul` (`Breakdown/Cert/CoercivePieceField.lean:1353`).

### Breakdown.Cert.CoercivePieceFieldCurlWeight

Weak integration by parts against Lipschitz weights bounds each weighted curl pairing by trace-mode and curl-mode amplitudes, first on slices and then over the period slab.

**Paper context:** Appendix B, Proposition B.1: weighted curl estimates for piece multiplier existence.

**Theorem: Lipschitz derivatives are weak partials.** For the stated Lipschitz function, its directional line derivative in a coordinate direction is a weak partial derivative. Source: `Breakdown.Coercive.CurlWeight.Internal.weakPartial_lineDeriv` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:23`).

**Theorem: Line derivatives vanish off the support.** The directional line derivative vanishes outside the support specified in the hypotheses. Source: `Breakdown.Coercive.CurlWeight.Internal.lineDeriv_eq_zero_of_not_mem` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:38`).

**Theorem: Convolution thickens support by two.** The convolution support is contained in the closed radius-two thickening of the original support. Source: `Breakdown.Coercive.CurlWeight.Internal.support_convolve_subset` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:50`).

**Theorem: Mollification preserves a uniform bound.** The mollified scalar function has absolute value at most the same supplied uniform bound M. Source: `Breakdown.Coercive.CurlWeight.Internal.abs_convolve_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:68`).

**Theorem: Zero beyond the thickened support.** The convolution is zero outside the closed radius-two thickening of the original support. Source: `Breakdown.Coercive.CurlWeight.Internal.convolve_eq_zero_of_notMem` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:84`).

**Theorem: Mollified test pairings converge.** The integrals pairing the mollified function with the stated weight converge to the corresponding unmollified pairing. Source: `Breakdown.Coercive.CurlWeight.Internal.tendsto_integral_convolve_mul` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:89`).

**Theorem: Use a Lipschitz weak-derivative test.** The pairing of a weak partial with the stated Lipschitz test equals minus the pairing of the original function with the test's coordinate line derivative. Source: `Breakdown.Coercive.CurlWeight.Internal.weakPartial_increment_test` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:108`).

**Theorem: A weighted test function is Lipschitz.** The product of the stated weight and test function has some finite Lipschitz constant. Source: `Breakdown.Coercive.CurlWeight.Internal.increment_mul_bounded` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:150`).

**Theorem: Weak integration by parts with a weight.** Integration by parts against the weighted test splits into the derivative of the weight and the derivative of the test function. Source: `Breakdown.Coercive.CurlWeight.Internal.weakPartial_increment_weight` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:173`).

**Theorem: Real parts retain local integrability.** The real part of the stated locally integrable complex function is locally integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.locallyIntegrable_re` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:200`).

**Theorem: Imaginary parts preserve local L¹.** The imaginary part of the stated locally integrable complex function is locally integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.locallyIntegrable_im` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:206`).

**Theorem: Constant multiples preserve local L¹.** Multiplying the stated locally integrable function by a real constant preserves local integrability. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.locallyIntegrable_const_mul` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:212`).

**Theorem: Integrability with bounded test weights.** The stated bounded weight times the locally integrable function is integrable under the support hypotheses. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.integrable_bounded_mul` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:218`).

**Theorem: Use the supplied test derivative.** The weak integration-by-parts identity holds for the weighted test with its supplied derivative field. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.weakPartial_differentiable_weight` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:231`).

**Theorem: Weak partials respect finite sums.** The same finite real linear combination of weak partial derivatives is a weak partial of the corresponding combination of functions. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.weakPartial_sum` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:262`).

**Theorem: Move a weighted test derivative.** The weighted derivative pairing equals the negative field-derivative pairing minus the weight-derivative correction under the stated weak derivative relations. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.weight_term_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:289`).

**Theorem: Integrate the complex curl by parts.** The real and imaginary weighted curl terms transform into the corresponding field-derivative terms and weight-derivative corrections. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.term_pair_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:301`).

**Theorem: Integrate a triple finite sum.** Under the stated integrability hypotheses, the integral of the triple coordinate sum equals the triple sum of the integrals. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.integral_sum_three` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:326`).

**Theorem: Expand the real part of complex curl.** The real part of each complex curl coordinate is the alternating-symbol contraction of the real gradient coordinates. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.re_curl_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:335`).

**Theorem: The imaginary part of complex curl.** The imaginary part of each complex curl coordinate is the alternating-symbol contraction of the imaginary gradient coordinates. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.im_curl_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:339`).

**Theorem: Read a real curl-gradient contraction.** The real part of the second-derivative curl contraction is the alternating-symbol sum of its real coordinates. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.re_curlSecondDeriv_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:343`).

**Theorem: The imaginary curl-gradient contraction.** The imaginary part of the second-derivative curl contraction is the alternating-symbol sum of its imaginary coordinates. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.im_curlSecondDeriv_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:348`).

**Theorem: Expand the weighted curl pairing.** The real weighted imaginary curl pairing equals the explicit alternating-symbol sum of real and imaginary gradient and curl coordinates. Source: `Breakdown.Coercive.CurlWeight.Internal.SliceAssembly.integrand_expand` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:353`).

**Theorem: An abstract weighted curl-slice bound.** The absolute weighted curl pairing on a spatial slice is bounded by the integral of the trace-amplitude and curl-amplitude terms times the test amplitude. Source: `Breakdown.Coercive.CurlWeight.Internal.slice_bound_abstract` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:365`).

**Theorem: A weighted curl bound on a.e. slices.** On almost every time slice, the weighted curl-mode pairing is controlled by the trace-mode and curl-mode amplitudes times the test-mode amplitude. Source: `Breakdown.Coercive.CurlWeight.Internal.curlWeightSlice_abs_le_proof` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:568`).

**Theorem: A weighted curl bound on a.e. slices.** On almost every time slice, the weighted curl-mode pairing is controlled by the trace-mode and curl-mode amplitudes times the test-mode amplitude. Source: `Breakdown.Coercive.CurlWeight.Internal.curlWeightSlice_abs_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:596`).

**Theorem: The weighted curl bound over time.** The absolute weighted curl pairing over the time slab is bounded by the corresponding integrated trace-mode and curl-mode amplitude expression. Source: `Breakdown.Coercive.CurlWeight.Internal.curlWeightPairing_abs_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeight.lean:611`).

### Breakdown.Cert.CoercivePieceFieldCurlWeightIncrement

Increment bounds imply Lipschitz control of finite weight combinations and an almost-everywhere bound on the squares of their coordinate derivatives.

**Paper context:** Appendix B, Proposition B.1: weak derivative bounds for the piece weights.

**Theorem: Finite weight combinations are Lipschitz.** The stated finite real combination of weight functions has a finite Lipschitz constant. Source: `Breakdown.Coercive.CurlWeight.Internal.increment_weightSum` (`Breakdown/Cert/CoercivePieceFieldCurlWeightIncrement.lean:13`).

**Theorem: Coordinate squares of a functional.** The sum of squared coordinate evaluations of a real linear functional is at most its squared operator norm. Source: `Breakdown.Coercive.CurlWeight.Internal.sum_sq_apply_unitVector_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeightIncrement.lean:26`).

**Theorem: Bound the weight gradient a.e..** Almost everywhere, the sum of the squared coordinate line derivatives of the weight combination is at most the squared nonnegative derivative bound. Source: `Breakdown.Coercive.CurlWeight.Internal.ae_lineDeriv_sq_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeightIncrement.lean:53`).

### Breakdown.Cert.CoercivePieceFieldCurlWeightPointwise

Finite-dimensional real and complex Cauchy-Schwarz identities bound the expanded curl contraction by trace, curl, and test amplitudes.

**Paper context:** Appendix B, Proposition B.1: the pointwise algebra in the piece curl-weight estimate.

**Theorem: Real and imaginary square sums.** The complex-vector norm square is the sum of the real-coordinate squares and imaginary-coordinate squares. Source: `Breakdown.Coercive.CurlWeight.Internal.cnormSq_eq_re_im` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:11`).

**Theorem: Cauchy-Schwarz for a difference pairing.** The square of the summed coordinate difference pairing is bounded by the product of the two combined square sums. Source: `Breakdown.Coercive.CurlWeight.Internal.sum_sub_sq_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:18`).

**Theorem: Cauchy-Schwarz for a sum pairing.** The square of the summed coordinate pairing is bounded by the product of the two combined square sums. Source: `Breakdown.Coercive.CurlWeight.Internal.sum_add_sq_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:30`).

**Theorem: Bound the cross-product norm.** The squared norm of the alternating-symbol cross product is at most the product of the two vector squared norms. Source: `Breakdown.Coercive.CurlWeight.Internal.cross_sq_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:38`).

**Theorem: Take square roots of a quadratic bound.** The assumed squared bound and nonnegativity imply |S| ≤ √X√Y. Source: `Breakdown.Coercive.CurlWeight.Internal.abs_le_sqrt_mul_sqrt` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:45`).

**Theorem: Regroup the curl contraction.** The triple alternating-symbol sum regroups into the test coordinates paired with the trace contraction and the two cross-product corrections. Source: `Breakdown.Coercive.CurlWeight.Internal.sum_rewrite` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:50`).

**Theorem: Combine trace and curl amplitude bounds.** The stated contraction bounds imply |S| ≤ (A√NΔ + A′√Nω)√Nθ. Source: `Breakdown.Coercive.CurlWeight.Internal.final_bound` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:62`).

**Theorem: A pointwise weighted curl bound.** The weighted curl contraction is bounded by the coefficient bound times trace amplitude plus the derivative bound times curl amplitude, all multiplied by test amplitude. Source: `Breakdown.Coercive.CurlWeight.Internal.slice_pointwise_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeightPointwise.lean:95`).

### Breakdown.Cert.CoercivePieceFieldCurlWeightSlice

The real and imaginary gradient-mode coordinates retain their weak partial derivatives on almost every time slice, supplying the weak integration-by-parts relations for curl testing.

**Paper context:** Appendix B, Proposition B.1: weak spatial slice relations for complex modes.

**Theorem: Read a real vector coordinate.** A coordinate of the reconstructed real vector is the real part of the matching complex coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.reVec_apply` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:18`).

**Theorem: Read an imaginary vector coordinate.** A coordinate of the reconstructed imaginary vector is the imaginary part of the matching complex coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.imVec_apply` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:21`).

**Theorem: Read a real matrix coordinate.** Applying the reconstructed real matrix to a coordinate basis vector returns the corresponding real matrix entry. Source: `Breakdown.Coercive.CurlWeight.Internal.reMat_apply_apply` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:24`).

**Theorem: Read an imaginary matrix coordinate.** Applying the reconstructed imaginary matrix to a coordinate basis vector returns the corresponding imaginary matrix entry. Source: `Breakdown.Coercive.CurlWeight.Internal.imMat_apply_apply` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:29`).

**Theorem: Coordinates retain local integrability.** Each coordinate of the stated locally integrable vector field is locally integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.locallyIntegrable_coord` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:34`).

**Theorem: Fixed evaluation preserves local L¹.** Applying a locally integrable linear-map field to a fixed vector gives a locally integrable vector field. Source: `Breakdown.Coercive.CurlWeight.Internal.locallyIntegrable_apply` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:40`).

**Theorem: Function F is integrable.** Under the stated hypotheses, the function F is locally integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.locallyIntegrable_of_re_im` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:46`).

**Theorem: Extract a coordinate weak partial.** Each coordinate of the vector weak-gradient relation gives the corresponding scalar weak partial derivative. Source: `Breakdown.Coercive.CurlWeight.Internal.weakPartial_coord` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:54`).

**Theorem: Modes retain weak derivatives on slices.** On almost every time slice, all gradient and Hessian mode coordinates are locally integrable and their real and imaginary parts satisfy the stated weak partial relations. Source: `Breakdown.Coercive.CurlWeight.Internal.ae_modeSlice_weak` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSlice.lean:70`).

### Breakdown.Cert.CoercivePieceFieldCurlWeightSumSecondPartials

Weak mixed-derivative symmetry and zero divergence identify the double alternating-symbol Hessian contraction with the corresponding trace-field mode almost everywhere.

**Paper context:** Appendix B, Proposition B.1: the trace identity inside the weak curl-weight estimate.

**Theorem: Read a real vector coordinate.** A coordinate of the reconstructed real vector is the real part of the matching complex coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.reVec_coord` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:17`).

**Theorem: Read an imaginary vector coordinate.** A coordinate of the reconstructed imaginary vector is the imaginary part of the matching complex coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.imVec_coord` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:20`).

**Theorem: Read a real matrix coordinate.** Applying the reconstructed real matrix to a coordinate basis vector returns the corresponding real matrix entry. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.reMat_coord` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:23`).

**Theorem: Read an imaginary matrix coordinate.** Applying the reconstructed imaginary matrix to a coordinate basis vector returns the corresponding imaginary matrix entry. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.imMat_coord` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:26`).

**Theorem: Coordinates retain local integrability.** Each coordinate of the stated locally integrable vector field is locally integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.locInt_coord` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:29`).

**Theorem: Local L¹ of operator coordinates.** A coordinate of the locally integrable linear-map field evaluated on a fixed vector is locally integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.locInt_apply` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:34`).

**Theorem: Test one weak gradient coordinate.** The tested coordinate of the weak gradient equals minus the corresponding test-derivative pairing with the original field coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.coord_weak` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:40`).

**Theorem: Test partials remain test functions.** A coordinate derivative of a smooth compactly supported test function is again a test function. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.test_fderiv` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:57`).

**Theorem: Test-function mixed derivatives commute.** The coordinate second derivatives of the stated test function agree after their differentiation directions are interchanged. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.fderiv_fderiv_symm` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:62`).

**Theorem: Weak mixed derivatives agree a.e..** The stated weak second-derivative coordinates are symmetric in their two differentiation indices almost everywhere. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.ae_symm` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:75`).

**Theorem: The differentiated divergence vanishes.** The stated weak second derivatives have zero differentiated trace almost everywhere. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.ae_trace` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:100`).

**Theorem: Trace commutes with frame rotation.** The sum of the rotated diagonal second derivatives equals the rotated second-derivative trace. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.sum_rot_diag` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:128`).

**Theorem: Axial rotation is continuous.** Under the stated hypotheses, the axial rotation is continuous. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.continuous_rot_comp` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:153`).

**Theorem: Integrable diagonal Hessian orbits.** Under the stated hypotheses, the rotated diagonal Hessian orbit coordinate is integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.integrable_secondDerivDiag` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:168`).

**Theorem: Trace commutes with taking a mode.** The diagonal sum of a second-derivative mode equals the velocity mode of the second-derivative trace. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.modeSecondDeriv_trace_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:192`).

**Theorem: Weak symmetry and vanishing trace.** The real weak derivative fields have symmetric mixed derivatives and zero differentiated divergence almost everywhere. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.real_parts` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:213`).

**Theorem: The double contraction gives the trace.** Under the stated symmetry and zero-divergence identities, the double alternating-symbol contraction equals the supplied trace vector coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.SumSecondPartialsModes.contraction_eq` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:239`).

**Theorem: The contraction equals the trace mode.** For almost every time and spatial point, the double alternating-symbol contraction of the Hessian mode equals the corresponding trace-field mode. Source: `Breakdown.Coercive.CurlWeight.Internal.ae_modeSlice_sumSecondPartials` (`Breakdown/Cert/CoercivePieceFieldCurlWeightSumSecondPartials.lean:255`).

### Breakdown.Cert.CoercivePieceFieldCurlWeightTest

The test-mode average is differentiated under its time-angle integral, producing a uniformly bounded spatial derivative whose coordinates are the gradient modes.

**Paper context:** Appendix B, Proposition B.1: differentiability of compact test modes.

**Definition: Integrand of a test-field mode.** Multiply the shifted and rotated test-field coordinate by its complex Fourier phase. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.modeTestIntegrand` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:18`).

**Definition: Derivative of the mode integrand.** Apply the Fourier phase to the rotated derivative of the test-field coordinate. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.modeTestIntegrandDeriv` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:22`).

**Theorem: Volume on the averaging rectangle.** The time-angle averaging measure equals planar volume restricted to one time period and one angular turn. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.boxMeasure_eq_restrict` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:27`).

**Theorem: Continuous rectangle data are integrable.** Under the stated hypotheses, the continuous function on the time-angle rectangle is integrable. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.integrable_box_of_continuous` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:31`).

**Theorem: Parameters lie in the averaging box.** Almost every averaging parameter belongs to the time-angle rectangle defining its measure. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.ae_box_mem` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:37`).

**Theorem: Test fields have smooth spatial slices.** Every spatial slice of the stated test field is smooth. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.contDiff_testSlice` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:41`).

**Theorem: Spatial derivative is continuous.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.continuous_testSlice_fderiv` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:45`).

**Theorem: Bound test derivatives over a period.** One nonnegative constant bounds the spatial derivative of the test field at every point and every time in the selected unit interval. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.testSlice_fderiv_bound` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:51`).

**Theorem: Differentiate the test-mode integrand.** The test-mode integrand has the explicitly constructed continuous linear derivative at every selected point. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.hasFDerivAt_modeTestIntegrand` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:66`).

**Theorem: Continuous mode-integrand derivatives.** Under the stated hypotheses, the test-mode integrand derivative is continuous. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.continuous_modeTestIntegrandDeriv` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:98`).

**Theorem: Test-mode integrand is continuous.** Under the stated hypotheses, the test-mode integrand is continuous. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.continuous_modeTestIntegrand` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:118`).

**Theorem: Bound the mode-integrand derivative.** The mode-integrand derivative norm is at most the test-field spatial derivative norm at the shifted and rotated point. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.norm_modeTestIntegrandDeriv_le` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:130`).

**Theorem: A rectangle integral for a test mode.** A velocity-mode coordinate is the time-angle rectangle integral of the test-mode integrand divided by 2π. Source: `Breakdown.Coercive.CurlWeight.Internal.TestModes.modeVel_eq_box` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:147`).

**Theorem: Test modes have bounded derivatives.** There is a uniformly bounded derivative field for each test-mode coordinate whose coordinate evaluations equal the corresponding gradient-mode entries. Source: `Breakdown.Coercive.CurlWeight.Internal.hasFDerivAt_modeVel_testField` (`Breakdown/Cert/CoercivePieceFieldCurlWeightTest.lean:162`).

### Breakdown.Cert.CoerciveRotation

Explicit sine and cosine formulas establish axial rotation's coordinate action, linearity, composition, inverse, and isometry properties.

**Paper context:** Appendix B, Proposition B.1: the rotation structure used by the time-angle mode decomposition.

**Theorem: The first rotated coordinate.** The first coordinate after axial rotation is cos(φ)y₀ − sin(φ)y₁. Source: `Breakdown.Coercive.RotationInternal.axialRot_apply_zero` (`Breakdown/Cert/CoerciveRotation.lean:14`).

**Theorem: The second rotated coordinate.** The second coordinate after axial rotation is sin(φ)y₀ + cos(φ)y₁. Source: `Breakdown.Coercive.RotationInternal.axialRot_apply_one` (`Breakdown/Cert/CoerciveRotation.lean:18`).

**Theorem: Rotation fixes the axial coordinate.** Axial rotation leaves the third coordinate unchanged. Source: `Breakdown.Coercive.RotationInternal.axialRot_apply_two` (`Breakdown/Cert/CoerciveRotation.lean:22`).

**Theorem: Coordinates determine a vector.** Two three-dimensional vectors are equal when their three coordinates agree. Source: `Breakdown.Coercive.RotationInternal.space_ext` (`Breakdown/Cert/CoerciveRotation.lean:25`).

**Theorem: Adding angles composes rotations.** Axial rotation by φ + ψ equals rotation by φ after rotation by ψ. Source: `Breakdown.Coercive.RotationInternal.axialRot_add` (`Breakdown/Cert/CoerciveRotation.lean:32`).

**Theorem: A zero-angle rotation is the identity.** Axial rotation through angle zero fixes every vector. Source: `Breakdown.Coercive.RotationInternal.axialRot_zero` (`Breakdown/Cert/CoerciveRotation.lean:41`).

**Theorem: Axial rotation preserves addition.** Under the stated hypotheses, the axial rotation commutes with addition. Source: `Breakdown.Coercive.RotationInternal.axialRot_map_add` (`Breakdown/Cert/CoerciveRotation.lean:47`).

**Theorem: Axial rotation preserves scaling.** Under the stated hypotheses, the axial rotation commutes with scalar multiplication. Source: `Breakdown.Coercive.RotationInternal.axialRot_map_smul` (`Breakdown/Cert/CoerciveRotation.lean:56`).

**Theorem: Undo a rotation with its negative angle.** Rotation by −φ after rotation by φ returns the original vector. Source: `Breakdown.Coercive.RotationInternal.axialRot_neg_self` (`Breakdown/Cert/CoerciveRotation.lean:65`).

**Theorem: Cancel an inverse rotation.** Rotation by φ after rotation by −φ returns the original vector. Source: `Breakdown.Coercive.RotationInternal.axialRot_self_neg` (`Breakdown/Cert/CoerciveRotation.lean:68`).

**Theorem: Axial rotation preserves length.** Axial rotation preserves the Euclidean norm. Source: `Breakdown.Coercive.RotationInternal.axialRot_norm` (`Breakdown/Cert/CoerciveRotation.lean:71`).

**Definition: Axial rotation as a linear map.** Equip axial rotation with its real linear-map structure. Source: `Breakdown.Coercive.RotationInternal.axialRotLinear` (`Breakdown/Cert/CoerciveRotation.lean:78`).

**Definition: Axial rotation as a linear isometry.** Equip axial rotation with its inverse rotation and norm-preserving linear-equivalence structure. Source: `Breakdown.Coercive.RotationInternal.axialRotEquiv` (`Breakdown/Cert/CoerciveRotation.lean:83`).

**Theorem: The axial rotation identities.** The supplied hypotheses establish linear isometry, composition, periodicity, and cylindrical-coordinate identities for axial rotation. Source: `Breakdown.Coercive.axialRotationHolds_proof` (`Breakdown/Cert/CoerciveRotation.lean:94`).

### Breakdown.Cert.CoerciveSmoothApproxClass

Space-time mollification is shown to preserve the smooth perturbation class, including divergence, weighted velocity, sixth-power slices, and derivative and transport energies.

**Paper context:** Appendix B, Proposition B.1: membership of mollified fields in the smooth approximation class.

**Theorem: The spatial kernel has radius two.** Every point in the kernel support has spatial component of norm at most two. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_support_subset` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:20`).

**Theorem: Compare radially shifted weights.** A spatial shift of norm at most two changes the inverse-square radial weight by at most a factor of nine in the stated direction. Source: `Breakdown.Coercive.Internal.SmoothApprox.weight_shift` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:36`).

**Theorem: Finite weighted period velocity energy.** The period integral of ‖v‖² times the inverse-square radial weight is finite under the perturbation hypotheses. Source: `Breakdown.Coercive.Internal.SmoothApprox.velocity_weight_lt_top` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:44`).

**Theorem: The radial weight is measurable.** Under the stated hypotheses, the inverse-square radial weight is measurable. Source: `Breakdown.Coercive.Internal.SmoothApprox.weight_measurable` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:54`).

**Theorem: Mollification preserves zero divergence.** The mollified perturbation is divergence-free at every time and spatial point. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_divergence_free` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:57`).

**Theorem: Each mollified slice lies in L⁶.** At every time, the mollified velocity has finite spatial sixth-power norm integral. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_sixth_power` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:81`).

**Theorem: Finite weighted mollification energy.** The squared norm of the mollified velocity divided by (1 + ‖y‖)² has finite period integral. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_weighted_finite` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:87`).

**Theorem: Mollified spatial derivatives lie in L².** Every positive-order spatial derivative of the mollified field has finite squared energy over a period. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_derivatives_finite` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:105`).

**Theorem: Finite weighted time-derivative energy.** The mollified field's time derivative has finite period squared energy with inverse-square radial weight. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_time_weighted_finite` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:140`).

**Theorem: Mixed mollified derivatives lie in L².** Every positive-order spatial derivative of the mollified time derivative has finite squared energy over one period. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_time_derivatives_finite` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:164`).

**Theorem: Mollified transport derivatives in L².** Every spatial derivative order, including zero, of the mollified transport field has finite squared energy over a period. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_transport_finite` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:207`).

**Theorem: Mollification is a smooth perturbation.** Each mollification of the stated weak perturbation satisfies the smooth-perturbation specification. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_isSmoothPerturbation` (`Breakdown/Cert/CoerciveSmoothApproxClass.lean:214`).

### Breakdown.Cert.CoerciveSmoothApproxClassSixth

A weighted sixth-power integral estimate and the spatial energy-space embedding give finite L⁶ energy for every mollified time slice.

**Paper context:** Appendix B, Proposition B.1: the sixth-power condition in smooth approximation.

**Theorem: A weighted sixth-power Hölder bound.** The sixth power of the weighted integral is bounded by the fifth power of the first weight integral times the stated reciprocal-weighted sixth-power integral. Source: `Breakdown.Coercive.Internal.SmoothApprox.lintegral_mul_sixth_le` (`Breakdown/Cert/CoerciveSmoothApproxClassSixth.lean:14`).

**Theorem: Sobolev control of sixth-power energy.** The spatial sixth-power velocity integral is bounded by the sixth power of the energy-space embedding norm times the cube of the gradient energy. Source: `Breakdown.Coercive.Internal.SmoothApprox.slice_sixth_le` (`Breakdown/Cert/CoerciveSmoothApproxClassSixth.lean:60`).

**Theorem: Bound an integral over several periods.** The nonnegative integral of the periodic function over any k-period interval is at most k times its integral over the unit period. Source: `Breakdown.Coercive.Internal.SmoothApprox.lintegral_Ioc_window` (`Breakdown/Cert/CoerciveSmoothApproxClassSixth.lean:91`).

**Theorem: The time bump is supported within two.** A point in the stated time-bump support has absolute value at most two. Source: `Breakdown.Coercive.Internal.SmoothApprox.timeBump_abs_le` (`Breakdown/Cert/CoerciveSmoothApproxClassSixth.lean:108`).

**Theorem: The kernel's time support is bounded.** A point in the kernel support has time coordinate of absolute value at most two. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_fst_abs_le` (`Breakdown/Cert/CoerciveSmoothApproxClassSixth.lean:117`).

**Theorem: Each mollified slice lies in L⁶.** At every time, the mollified velocity has finite spatial sixth-power norm integral. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_sixth_power_bound` (`Breakdown/Cert/CoerciveSmoothApproxClassSixth.lean:122`).

### Breakdown.Cert.CoerciveSmoothApproxClassTransport

Differentiating the mollifier and integrating coordinate kernels against weak derivatives gives the transport commutator formula and finite transport-derivative energies.

**Paper context:** Appendix B, Proposition B.1: transport estimates for space-time mollification.

**Theorem: Differentiate mollification in time.** The time derivative of the mollified field equals convolution with the kernel's pure time derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_time_deriv` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:18`).

**Theorem: Finite gradient operator-norm energy.** The period integral of the squared operator norm of the weak gradient is finite. Source: `Breakdown.Coercive.Internal.SmoothApprox.gradient_sq_lt_top` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:32`).

**Theorem: The convolution integrand is integrable.** The product of the stated compact smooth kernel with the translated locally integrable field is integrable. Source: `Breakdown.Coercive.Internal.SmoothApprox.scalar_convolution_integrable` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:46`).

**Theorem: Continuous kernel derivative evaluation.** Under the stated hypotheses, the kernel derivative evaluated on the direction field is continuous. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_fderiv_continuous` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:54`).

**Theorem: Kernel derivatives have compact support.** Under the stated hypotheses, the kernel derivative evaluated on the direction field has compact support. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_fderiv_hasCompactSupport` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:58`).

**Theorem: Coordinate-weighted kernels are smooth.** Under the stated hypotheses, the spatial coordinate times the kernel is smooth. Source: `Breakdown.Coercive.Internal.SmoothApprox.coordinate_kernel_contDiff` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:64`).

**Theorem: Compact support of weighted kernels.** Under the stated hypotheses, the spatial coordinate times the kernel has compact support. Source: `Breakdown.Coercive.Internal.SmoothApprox.coordinate_kernel_hasCompactSupport` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:74`).

**Theorem: Differentiate a coordinate-kernel term.** The coordinate spatial derivative of tₖ times the kernel equals the kernel plus tₖ times that kernel derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.coordinate_kernel_fderiv` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:78`).

**Theorem: Expand a pure spatial direction.** A linear functional applied to a pure spatial vector equals the sum of its coordinate components times the corresponding coordinate evaluations. Source: `Breakdown.Coercive.Internal.SmoothApprox.fderiv_apply_snd_eq_sum` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:94`).

**Theorem: Sum the coordinate-kernel derivatives.** The sum of the three coordinate derivatives of coordinate times kernel equals three times the kernel plus its radial spatial derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.coordinate_kernel_sum` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:103`).

**Theorem: Integrate coordinate kernels by parts.** The sum of coordinate-kernel convolutions with the weak gradient equals three times the mollified field plus convolution with the radial kernel derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.coordinate_convolution_sum` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:110`).

**Theorem: Compute the transport commutator.** The transport of the mollified field equals mollification of the weak transport term plus half the sum of coordinate-kernel convolutions with the weak gradient. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_transportPart_eq` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:143`).

**Theorem: Norm is integrable.** Under the stated hypotheses, the norm is locally integrable. Source: `Breakdown.Coercive.Internal.SmoothApprox.locallyIntegrable_norm` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:267`).

**Theorem: Mollified transport derivatives in L².** Every spatial derivative order, including zero, of the mollified transport field has finite squared energy over a period. Source: `Breakdown.Coercive.Internal.SmoothApprox.transport_finite_bound` (`Breakdown/Cert/CoerciveSmoothApproxClassTransport.lean:271`).

### Breakdown.Cert.CoerciveSmoothApproxDerivative

Kernel differentiation and weak integration by parts show that the spatial derivatives of mollification equal mollification of the weak derivatives.

**Paper context:** Appendix B, Proposition B.1: derivative compatibility of smooth approximation.

**Theorem: Differentiate a kernel convolution.** The directional derivative of the convolution equals convolution with the kernel's directional derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.convolution_fderiv_apply` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:14`).

**Theorem: Differentiate mollification in space.** The spatial directional derivative of the mollified field equals convolution with the corresponding pure spatial derivative of the kernel. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_fderiv_eq` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:27`).

**Theorem: Local L¹ of weak-gradient evaluation.** Under the stated hypotheses, the weak-gradient field evaluated on a fixed vector is locally integrable. Source: `Breakdown.Coercive.Internal.SmoothApprox.joint_apply_locallyIntegrable` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:41`).

**Theorem: A shifted kernel is a test function.** For fixed time and spatial parameters, the translated kernel slice is a smooth compactly supported test function. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_shift_testFunction` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:49`).

**Theorem: Differentiate the translated kernel.** Differentiating the translated spatial kernel gives minus the corresponding pure spatial derivative of the kernel at the translated argument. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_shift_fderiv` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:62`).

**Theorem: Move a weak partial onto the kernel.** Convolution with a coordinate kernel derivative equals mollification of the corresponding weak partial derivative field. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_partial_eq` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:77`).

**Theorem: Mollify weak coordinate derivatives.** Each coordinate derivative of the mollified field equals the mollification of its corresponding weak gradient column. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_partial` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:108`).

**Theorem: Integrable kernel-field products.** Under the stated hypotheses, the translated kernel times the joint field is integrable. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_smul_integrable` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:116`).

**Theorem: Move the convolution shift to the kernel.** The mollified field equals the integral of the translated kernel times the unshifted joint field. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_eq_integral` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:124`).

**Theorem: Read a coordinate of the mollified field.** A coordinate of the mollified vector field equals the integral of the translated kernel times that coordinate of the original field. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_component` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:131`).

**Theorem: Integrable kernel-coordinate products.** Under the stated hypotheses, the translated kernel times one joint-field coordinate is integrable. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_component_integrable` (`Breakdown/Cert/CoerciveSmoothApproxDerivative.lean:138`).

### Breakdown.Cert.CoerciveSmoothApproxGeneral

The convolution derivative and weak-partial transfer formulas are proved for a general smooth compact kernel, including equality of the full convolved weak-gradient field.

**Paper context:** Appendix B, Proposition B.1: general convolution calculus used by smooth approximation.

**Theorem: Differentiate a general convolution.** For the stated smooth compact kernel, the directional derivative of the convolution equals convolution with the kernel derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.convolution_fderiv_apply_of` (`Breakdown/Cert/CoerciveSmoothApproxGeneral.lean:14`).

**Theorem: Compact support of shifted kernel slices.** The stated translated spatial slice of the compact kernel has compact support. Source: `Breakdown.Coercive.Internal.SmoothApprox.shift_hasCompactSupport` (`Breakdown/Cert/CoerciveSmoothApproxGeneral.lean:27`).

**Theorem: Differentiate a translated kernel.** The derivative of the spatially translated kernel is the negative pure spatial derivative of the original kernel at the translated point. Source: `Breakdown.Coercive.Internal.SmoothApprox.shift_fderiv_of` (`Breakdown/Cert/CoerciveSmoothApproxGeneral.lean:36`).

**Theorem: Move a general kernel derivative weakly.** Convolving a coordinate derivative of the stated smooth kernel with the field equals convolving the kernel with its weak partial field. Source: `Breakdown.Coercive.Internal.SmoothApprox.partial_eq_of` (`Breakdown/Cert/CoerciveSmoothApproxGeneral.lean:49`).

**Theorem: Convolve the full weak gradient.** The spatial derivative field of the convolution equals the convolution of the kernel with the full weak gradient field. Source: `Breakdown.Coercive.Internal.SmoothApprox.slice_fderiv_clm_of` (`Breakdown/Cert/CoerciveSmoothApproxGeneral.lean:78`).

### Breakdown.Cert.CoerciveSmoothApproxIterated

Controls iterated derivatives of the smoothing convolution and identifies the spatial derivative of the mollified field.

**Paper context:** Appendix B, Proposition B.1: approximation that extends the smooth coercive calculation to the perturbation domain.

**Theorem: Differentiate a smoothing convolution.** Each iterated derivative of the convolution is bounded by the integral of the corresponding kernel-derivative norm times the translated field norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.norm_iteratedFDeriv_convolution_le` (`Breakdown/Cert/CoerciveSmoothApproxIterated.lean:15`).

**Theorem: A slice derivative is no larger.** The norm of an iterated spatial derivative on a fixed time slice is at most that of the full spacetime derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.norm_iteratedFDeriv_slice_le` (`Breakdown/Cert/CoerciveSmoothApproxIterated.lean:44`).

**Theorem: Mollification preserves weak gradients.** The spatial derivative of the mollified field equals convolution of the kernel with the supplied weak gradient. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_fderiv_clm` (`Breakdown/Cert/CoerciveSmoothApproxIterated.lean:66`).

### Breakdown.Cert.CoerciveSmoothApproxKernel

Builds the compactly supported spacetime smoothing kernel and proves smoothness, periodicity and local integrability of its convolution.

**Paper context:** Appendix B, Proposition B.1: approximation that extends the smooth coercive calculation to the perturbation domain.

**Definition: Shrinking time bump.** The time bump equals one inside radius $1/(n+1)$ and is supported inside radius $2/(n+1)$. Source: `Breakdown.Coercive.Internal.SmoothApprox.timeBump` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:14`).

**Definition: Shrinking spatial bump.** The spatial bump uses inner radius $1/(n+1)$ and outer radius $2/(n+1)$. Source: `Breakdown.Coercive.Internal.SmoothApprox.spaceBump` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:18`).

**Definition: Product smoothing kernel.** The smoothing kernel is the product of the normalised time and spatial bumps. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:22`).

**Definition: A field as a spacetime function.** The joint version evaluates a time-dependent field at the time and space coordinates of one pair. Source: `Breakdown.Coercive.Internal.SmoothApprox.joint` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:25`).

**Definition: Smooth a field by convolution.** The mollified field is the spacetime convolution of the field with the product smoothing kernel. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:27`).

**Theorem: Smoothness of smoothing kernel.** Under the stated hypotheses, the smoothing kernel is smooth. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_contDiff` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:30`).

**Theorem: Compact support of smoothing kernel.** Under the stated hypotheses, the smoothing kernel has compact support. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_hasCompactSupport` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:34`).

**Theorem: Nonnegativity of smoothing kernel.** The smoothing kernel is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_nonneg` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:44`).

**Theorem: Spacetime volume is Haar measure.** Lebesgue measure on time times space is an additive Haar measure. Source: `Breakdown.Coercive.Internal.SmoothApprox.volume_prod_invariantClass` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:47`).

**Theorem: Smoothness of mollified field.** Under the stated hypotheses, the mollified field is smooth. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_smooth` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:50`).

**Theorem: Time periodicity of mollified field.** Under the stated hypotheses, the mollified field has period one in time. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_periodic` (`Breakdown/Cert/CoerciveSmoothApproxKernel.lean:55`).

### Breakdown.Cert.CoerciveSmoothApproxLimits

Proves convergence of mollified fields, gradients, second derivatives and inverse-radius weighted fields in the norms needed to pass the smooth estimate to weak perturbations.

**Paper context:** Appendix B, Proposition B.1: approximation that extends the smooth coercive calculation to the perturbation domain.

**Theorem: Periodic convolution converges in L2.** The squared period $L^2$ error between the smoothed periodic field and the original field tends to zero. Source: `Breakdown.Coercive.Internal.SmoothApprox.convolution_sq_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:16`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.matSq_le_three_sq` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:24`).

**Theorem: Mollified gradients converge in L2.** The spatial gradients of the mollified perturbations converge to the supplied weak gradient in the period $L^2$ square seminorm. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_gradient_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:33`).

**Theorem: Evaluate a locally integrable operator.** Applying a locally integrable operator-valued field to one fixed vector gives a locally integrable field. Source: `Breakdown.Coercive.Internal.SmoothApprox.joint_apply_locallyIntegrable_of` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:61`).

**Theorem: Evaluation commutes with convolution.** Applying the convolved operator-valued field to a fixed vector is the same as convolving its value on that vector. Source: `Breakdown.Coercive.Internal.SmoothApprox.convolution_apply_eq` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:69`).

**Theorem: Mollification preserves second gradients.** The second spatial derivative of the mollified perturbation is the convolution of its supplied weak second derivative. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_secondDerivField_eq` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:80`).

**Theorem: Square of a three-term sum.** The square of a sum of three real numbers is at most three times the sum of their squares. Source: `Breakdown.Coercive.Internal.SmoothApprox.sq_add_three_le` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:127`).

**Theorem: Squared Hessian norm bound.** The sum of squared second derivative entries is at most nine times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.secondDerivSq_le_sq` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:130`).

**Theorem: Operator norm from Hessian entries.** The squared bilinear operator norm is at most nine times the sum of squared second derivative entries. Source: `Breakdown.Coercive.Internal.SmoothApprox.sq_le_secondDerivSq` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:140`).

**Theorem: Finite second-derivative energy.** The supplied second-derivative field has finite squared operator-norm integral over one spacetime period. Source: `Breakdown.Coercive.Internal.SmoothApprox.secondDeriv_sq_lt_top` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:160`).

**Theorem: Mollified Hessians converge in L2.** The second derivatives of the mollified perturbations converge to the supplied weak second derivative in the period square seminorm. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_secondDeriv_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:174`).

**Theorem: Spatial support of the smoothing kernel.** A point in the kernel's support has spatial norm at most $2/(n+1)$. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_snd_le` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:197`).

**Theorem: An inverse radial weight under shifts.** The change in the reciprocal weight under a spatial shift is bounded by the shift norm times the shifted reciprocal weight. Source: `Breakdown.Coercive.Internal.SmoothApprox.weight_diff_le` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:205`).

**Definition: Velocity with inverse radial weight.** The weighted field is the velocity divided by one plus the distance from the origin. Source: `Breakdown.Coercive.Internal.SmoothApprox.weightedField` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:218`).

**Theorem: Local integrability after radial scaling.** Dividing the perturbation by one plus the spatial norm preserves the stated local integrability. Source: `Breakdown.Coercive.Internal.SmoothApprox.weightedField_locallyIntegrable` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:220`).

**Theorem: Separate the weighted smoothing error.** The weighted squared smoothing error is bounded by twice the weighted-field convolution error plus the explicit kernel-radius commutator term. Source: `Breakdown.Coercive.Internal.SmoothApprox.weighted_pointwise` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:234`).

**Theorem: Finite weighted velocity energy.** The inverse-radius weighted velocity has finite squared-norm integral over one spacetime period. Source: `Breakdown.Coercive.Internal.SmoothApprox.weightedField_sq_lt_top` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:307`).

**Theorem: Weighted velocities converge in L2.** The mollified velocities converge to the original perturbation in the period square norm weighted by $(1+|y|)^{-2}$. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_weighted_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:318`).

**Theorem: Mollified transport converges in L2.** The similarity-transport fields of the mollified perturbations converge to the supplied weak transport field in the period $L^2$ square norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.mollify_transport_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimits.lean:399`).

### Breakdown.Cert.CoerciveSmoothApproxLimitsTransport

Controls the extra first-moment convolution generated when similarity transport is mollified, so the transport approximation converges in the required norm.

**Paper context:** Appendix B, Proposition B.1: approximation that extends the smooth coercive calculation to the perturbation domain.

**Theorem: Additivity over one time period.** The iterated integral of the displayed sum splits into the two iterated integrals under the stated measurability or integrability assumptions. Source: `Breakdown.Coercive.Internal.SmoothApprox.period_add_of_measurable` (`Breakdown/Cert/CoerciveSmoothApproxLimitsTransport.lean:15`).

**Theorem: A smooth first-moment kernel.** Multiplying the smoothing kernel by a spatial coordinate gives a smooth spacetime function. Source: `Breakdown.Coercive.Internal.SmoothApprox.moment_kernel_contDiff` (`Breakdown/Cert/CoerciveSmoothApproxLimitsTransport.lean:25`).

**Theorem: The moment kernel has compact support.** The product of the smoothing kernel and a spatial coordinate has compact support. Source: `Breakdown.Coercive.Internal.SmoothApprox.moment_kernel_hasCompactSupport` (`Breakdown/Cert/CoerciveSmoothApproxLimitsTransport.lean:30`).

**Theorem: First moment of the smoothing kernel.** The nonnegative integral of one spatial coordinate times the kernel in absolute value is at most $2/(n+1)$. Source: `Breakdown.Coercive.Internal.SmoothApprox.moment_kernel_lintegral_le` (`Breakdown/Cert/CoerciveSmoothApproxLimitsTransport.lean:34`).

**Theorem: A four-vector square bound.** The squared norm of the displayed transport-error decomposition is bounded by the three component squares plus four times the remaining error square. Source: `Breakdown.Coercive.Internal.SmoothApprox.transport_pointwise` (`Breakdown/Cert/CoerciveSmoothApproxLimitsTransport.lean:50`).

**Theorem: Mollified transport converges in L2.** The similarity-transport fields of the mollified perturbations converge to the supplied weak transport field in the period $L^2$ square norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.transport_tendsto_of_eq` (`Breakdown/Cert/CoerciveSmoothApproxLimitsTransport.lean:69`).

### Breakdown.Cert.CoerciveSmoothApproxLimitsWhole

Establishes approximate-identity convergence on full spacetime and transfers it to a one-period integral using a finite time-slab truncation.

**Paper context:** Appendix B, Proposition B.1: approximation that extends the smooth coercive calculation to the perturbation domain.

**Theorem: The smoothing kernel has mass one.** The displayed integral of the nonnegative normalised smoothing kernel is one. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_integral_eq_one` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:14`).

**Theorem: The smoothing kernel has mass one.** The displayed integral of the nonnegative normalised smoothing kernel is one. Source: `Breakdown.Coercive.Internal.SmoothApprox.lintegral_kernel_eq_one` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:19`).

**Theorem: The smoothing kernel's support shrinks.** The kernel support lies in the spacetime ball of radius $2/(n+1)$. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_support_subset_ball` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:29`).

**Theorem: All smoothing radii are at most two.** The radius $2/(n+1)$ is at most two for every natural-number index. Source: `Breakdown.Coercive.Internal.SmoothApprox.radius_le_two` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:42`).

**Theorem: Kernel supports tend to the origin.** The supports of the smoothing kernels eventually lie in every neighbourhood of the spacetime origin. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_support_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:45`).

**Theorem: A convolution bound on all spacetime.** The squared $L^2$ integral of a convolution is bounded by the squared $L^1$ kernel norm times the squared $L^2$ field integral. Source: `Breakdown.Coercive.Internal.SmoothApprox.whole_convolution_sq_le` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:56`).

**Theorem: The L2 norm as a square integral.** The squared extended $L^2$ norm equals the nonnegative integral of the squared extended norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.eLpNorm_two_sq_eq_lintegral` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:90`).

**Theorem: From squared integrals to L2 convergence.** Convergence of the nonnegative squared norm integrals to zero implies convergence of the corresponding $L^2$ norms to zero. Source: `Breakdown.Coercive.Internal.SmoothApprox.eLpNorm_tendsto_of_sq` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:96`).

**Theorem: Smoothing is an L2 contraction.** The $L^2$ distance between two smoothed fields is at most their original $L^2$ distance. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_convolution_sub_eLpNorm_le` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:105`).

**Theorem: Smooth approximation of continuous data.** For the stated continuous data, convolution by the shrinking unit-mass kernels converges in the squared $L^2$ integral. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_convolution_sq_tendsto_of_continuous` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:132`).

**Theorem: Smooth approximation of L2 data.** Convolution by the shrinking smoothing kernels converges to the original $L^2$ field in $L^2$ norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.kernel_convolution_eLpNorm_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:192`).

**Theorem: A time restriction as a product set.** The iterated nonnegative integral over a time set and all space equals the integral over their Cartesian product. Source: `Breakdown.Coercive.Internal.SmoothApprox.setLIntegral_prod_eq` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:236`).

**Theorem: A finite time window suffices locally.** On the indicated central time slab, cutting the periodic field to the interval $[-2,3]$ does not change its convolution with the smoothing kernel. Source: `Breakdown.Coercive.Internal.SmoothApprox.convolution_indicator_eq` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:245`).

**Theorem: Bound an integral over five periods.** The nonnegative integral over $[-2,3]$ is at most five times the integral over one period. Source: `Breakdown.Coercive.Internal.SmoothApprox.lintegral_five_periods` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:265`).

**Theorem: Period energy with extended norms.** The period integral of the real squared norm equals the iterated nonnegative integral of the squared extended norm. Source: `Breakdown.Coercive.Internal.SmoothApprox.periodLIntegral_sq_eq` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:295`).

**Theorem: Truncation to a finite time slab is L2.** The joint field restricted by the indicator of the time interval $[-2,3]$ belongs to spacetime $L^2$. Source: `Breakdown.Coercive.Internal.SmoothApprox.period_indicator_memLp` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:300`).

**Theorem: Periodic convolution converges in L2.** The squared period $L^2$ error between the smoothed periodic field and the original field tends to zero. Source: `Breakdown.Coercive.Internal.SmoothApprox.period_convolution_sq_tendsto` (`Breakdown/Cert/CoerciveSmoothApproxLimitsWhole.lean:320`).

### Breakdown.Cert.CoerciveSmoothApproxPeriodBound

Bounds ordinary and radially weighted period energies of a convolution by the corresponding energies of the original periodic field.

**Paper context:** Appendix B, Proposition B.1: approximation that extends the smooth coercive calculation to the perturbation domain.

**Theorem: Weighted integral Cauchy–Schwarz.** The squared integral of $AB$ is bounded by the integral of $A$ times the integral of $AB^2$. Source: `Breakdown.Coercive.Internal.SmoothApprox.sq_lintegral_mul_le_prod` (`Breakdown/Cert/CoerciveSmoothApproxPeriodBound.lean:15`).

**Theorem: Convolution on a periodic time slab.** The squared period integral of a convolution is at most the squared $L^1$ kernel norm times the field's period square integral. Source: `Breakdown.Coercive.Internal.SmoothApprox.period_convolution_sq_le` (`Breakdown/Cert/CoerciveSmoothApproxPeriodBound.lean:39`).

**Theorem: Convolution with a spatial weight.** The weighted period square integral obeys the convolution bound multiplied by the assumed weight-comparison constant. Source: `Breakdown.Coercive.Internal.SmoothApprox.period_convolution_weighted_sq_le` (`Breakdown/Cert/CoerciveSmoothApproxPeriodBound.lean:103`).

### Breakdown.Cert.CoerciveSmoothBase

Converts smooth physical-space derivative and curl energies into weighted mode densities through Parseval and the weighted div-curl identity.

**Paper context:** Appendix B, (B.16) and Proposition B.1: the conversion weights that replace curl energies by derivative energies.

**Theorem: Continuity of the perturbation jet.** A smooth perturbation and its first two spatial derivative fields are jointly continuous in time and space. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_fields_continuous` (`Breakdown/Cert/CoerciveSmoothBase.lean:16`).

**Theorem: Continuity of mode coefficients.** The velocity, gradient and second derivative mode coefficients of a smooth perturbation are jointly continuous. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modes_continuous` (`Breakdown/Cert/CoerciveSmoothBase.lean:29`).

**Theorem: Measurable mode-energy densities.** The velocity, gradient, vorticity, Hessian and vorticity-gradient mode squares are measurable. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_squares_measurable` (`Breakdown/Cert/CoerciveSmoothBase.lean:66`).

**Theorem: The expanded base density is measurable.** Under the stated hypotheses, the expanded base-density expression is measurable. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_measurable_expanded` (`Breakdown/Cert/CoerciveSmoothBase.lean:78`).

**Theorem: Measurability of positive main density.** Under the stated hypotheses, the positive main density is measurable. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_measurable_mainPos` (`Breakdown/Cert/CoerciveSmoothBase.lean:95`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.SmoothBaseInternal.norm_unit` (`Breakdown/Cert/CoerciveSmoothBase.lean:103`).

**Theorem: Apply an operator to a unit vector.** Applying a continuous linear map to a coordinate unit vector has norm at most its operator norm. Source: `Breakdown.Coercive.SmoothBaseInternal.apply_unit_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:106`).

**Theorem: A bilinear map on unit vectors.** Applying a continuous bilinear map to two coordinate unit vectors has norm at most its operator norm. Source: `Breakdown.Coercive.SmoothBaseInternal.apply_unit₂_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:110`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.SmoothBaseInternal.matNorm_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:114`).

**Theorem: Squared Hessian norm bound.** The sum of squared second derivative entries is at most nine times the squared operator norm. Source: `Breakdown.Coercive.SmoothBaseInternal.secondDerivSq_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:120`).

**Theorem: Squared trace bound.** The squared norm of the second derivative trace is at most nine times the squared operator norm. Source: `Breakdown.Coercive.SmoothBaseInternal.trace_sq_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:128`).

**Definition: Curl as a continuous linear map.** This bundles the matrix-to-curl operation as a continuous linear map. Source: `Breakdown.Coercive.SmoothBaseInternal.curlMap` (`Breakdown/Cert/CoerciveSmoothBase.lean:137`).

**Theorem: Curl square from its operator norm.** The squared curl norm is bounded by the squared curl-map norm times the squared input operator norm. Source: `Breakdown.Coercive.SmoothBaseInternal.curl_sq_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:139`).

**Theorem: Domination gives a finite integral.** The supplied pointwise domination by a finite nonnegative period integral makes the displayed period integral finite. Source: `Breakdown.Coercive.SmoothBaseInternal.period_finite_of_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:144`).

**Theorem: The first iterated derivative.** The first iterated derivative and the ordinary Fréchet derivative have equal norms. Source: `Breakdown.Coercive.SmoothBaseInternal.norm_iter_one` (`Breakdown/Cert/CoerciveSmoothBase.lean:156`).

**Theorem: The second iterated derivative.** The second iterated derivative and the derivative of the derivative have equal norms. Source: `Breakdown.Coercive.SmoothBaseInternal.norm_iter_two` (`Breakdown/Cert/CoerciveSmoothBase.lean:160`).

**Theorem: Differentiate the curl field.** The directional derivative of the vorticity is the curl contraction of the second derivative in that direction. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_fderiv_curl_apply` (`Breakdown/Cert/CoerciveSmoothBase.lean:164`).

**Theorem: Continuous physical energy densities.** The vorticity-gradient, vorticity, Laplacian and gradient energy densities are jointly continuous for a smooth perturbation. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_energy_continuous` (`Breakdown/Cert/CoerciveSmoothBase.lean:175`).

**Theorem: Recover a real period integral.** For the stated nonnegative integrable density, the ordinary iterated integral equals the real value of its extended-nonnegative period integral. Source: `Breakdown.Coercive.SmoothBaseInternal.integral_eq_period` (`Breakdown/Cert/CoerciveSmoothBase.lean:195`).

**Theorem: The smooth energy integrals are finite.** The stated smooth-perturbation and bounded-weight assumptions make the vorticity-gradient, vorticity, Laplacian and weighted-gradient square integrals finite. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_fields_finite` (`Breakdown/Cert/CoerciveSmoothBase.lean:205`).

**Theorem: Split the vorticity energy.** The vorticity energy is the vorticity-gradient square integral plus one quarter of the vorticity square integral. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_vorticityEnergy_eq` (`Breakdown/Cert/CoerciveSmoothBase.lean:240`).

**Theorem: Split the weighted energy.** The weighted energy is the Laplacian square integral plus the weighted gradient square integral. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_weightedEnergy_eq` (`Breakdown/Cert/CoerciveSmoothBase.lean:273`).

**Theorem: Parseval for the vorticity gradient.** The sum of the vorticity-gradient mode energies equals the physical vorticity-gradient square integral. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSum_eq_vortGrad` (`Breakdown/Cert/CoerciveSmoothBase.lean:286`).

**Theorem: Parseval for vorticity.** The sum of the vorticity mode energies equals the physical vorticity square integral. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSum_eq_vort` (`Breakdown/Cert/CoerciveSmoothBase.lean:341`).

**Theorem: Domination gives a finite slice integral.** The supplied pointwise bound by a finite nonnegative spatial integral makes the displayed slice integral finite. Source: `Breakdown.Coercive.SmoothBaseInternal.slice_finite_of_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:385`).

**Theorem: A finite norm integral gives L1.** The stated measurability and finite norm integral imply integrability of the displayed function. Source: `Breakdown.Coercive.SmoothBaseInternal.integrable_of_lintegral` (`Breakdown/Cert/CoerciveSmoothBase.lean:394`).

**Theorem: Radial damping decreases a positive term.** Dividing the stated nonnegative number by $(1+|y|)^2$ cannot increase it. Source: `Breakdown.Coercive.SmoothBaseInternal.weight_div_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:398`).

**Theorem: Smooth slices and symmetric Hessians.** Every time slice is smooth and its second derivative is symmetric in the two spatial directions. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_slice_smooth` (`Breakdown/Cert/CoerciveSmoothBase.lean:401`).

**Theorem: Differentiate a gradient column.** Differentiating a fixed gradient column gives the second derivative with that column direction held fixed. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_column_fderiv` (`Breakdown/Cert/CoerciveSmoothBase.lean:409`).

**Theorem: Differentiate zero divergence.** Differentiating the divergence-free identity gives zero trace for the corresponding directional second derivative. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_divergence_deriv_zero` (`Breakdown/Cert/CoerciveSmoothBase.lean:416`).

**Theorem: Finite derivative energy on most slices.** For almost every time in one period, the first and second spatial derivative square integrals are finite. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_slice_good` (`Breakdown/Cert/CoerciveSmoothBase.lean:435`).

**Theorem: Derivative bounds for the unit weight.** The constant weight one satisfies the displayed weighted derivative bounds through order two. Source: `Breakdown.Coercive.SmoothBaseInternal.const_one_bound` (`Breakdown/Cert/CoerciveSmoothBase.lean:450`).

**Theorem: Hessian energy equals Laplacian energy.** For almost every time slice, the integral of the squared Hessian equals the integral of the squared Laplacian under the stated smoothness and finiteness assumptions. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_slice_secondDerivSq_eq` (`Breakdown/Cert/CoerciveSmoothBase.lean:458`).

**Theorem: Hessian modes recover Laplacian energy.** The sum of the Hessian mode energies equals the physical Laplacian square integral. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSum_eq_secondDeriv` (`Breakdown/Cert/CoerciveSmoothBase.lean:586`).

**Theorem: Parseval with the gradient weight.** The weighted sum of gradient-mode squares equals the weighted physical gradient square integral. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSum_eq_weighted_grad` (`Breakdown/Cert/CoerciveSmoothBase.lean:605`).

**Theorem: Parseval with radial velocity damping.** The inverse-radius weighted sum of velocity-mode squares equals the corresponding weighted physical velocity integral. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSum_eq_weighted_vel` (`Breakdown/Cert/CoerciveSmoothBase.lean:642`).

**Theorem: Finite mode energy on most slices.** A finite nonnegative mode-energy sum gives a finite spatial integral for the selected mode at almost every time. Source: `Breakdown.Coercive.SmoothBaseInternal.ae_slice_of_modeSum` (`Breakdown/Cert/CoerciveSmoothBase.lean:680`).

**Theorem: All required mode slices are finite.** For almost every time, the weighted velocity, gradient, vorticity, Hessian and vorticity-gradient energies of the selected mode are finite. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_mode_slices` (`Breakdown/Cert/CoerciveSmoothBase.lean:685`).

**Theorem: Weighted derivative bounds at infinity.** The weight's derivative bounds can be expressed using powers of one plus the spatial norm through order two. Source: `Breakdown.Coercive.SmoothBaseInternal.weight_bound_one_add` (`Breakdown/Cert/CoerciveSmoothBase.lean:713`).

**Theorem: Bounds for the weight and its Hessian.** The weight and its Hessian satisfy the displayed uniform and inverse-square radial bounds. Source: `Breakdown.Coercive.SmoothBaseInternal.weight_value_bounds` (`Breakdown/Cert/CoerciveSmoothBase.lean:751`).

**Theorem: Euclidean norm in coordinates.** The squared Euclidean norm is the sum of the squared real coordinates. Source: `Breakdown.Coercive.SmoothBaseInternal.space_norm_sq` (`Breakdown/Cert/CoerciveSmoothBase.lean:765`).

**Theorem: Real vector coordinates.** The indicated coordinate of the real vector is the real part of the complex coordinate. Source: `Breakdown.Coercive.SmoothBaseInternal.reVec_apply` (`Breakdown/Cert/CoerciveSmoothBase.lean:769`).

**Theorem: Imaginary vector coordinates.** The indicated coordinate of the imaginary vector is the imaginary part of the complex coordinate. Source: `Breakdown.Coercive.SmoothBaseInternal.imVec_apply` (`Breakdown/Cert/CoerciveSmoothBase.lean:772`).

**Theorem: Real matrix entries.** Applying the real matrix to a coordinate unit vector returns the corresponding real parts of its entries. Source: `Breakdown.Coercive.SmoothBaseInternal.reMat_apply` (`Breakdown/Cert/CoerciveSmoothBase.lean:775`).

**Theorem: Imaginary matrix entries.** Applying the imaginary matrix to a coordinate unit vector returns the corresponding imaginary parts of its entries. Source: `Breakdown.Coercive.SmoothBaseInternal.imMat_apply` (`Breakdown/Cert/CoerciveSmoothBase.lean:778`).

**Theorem: Split the complex matrix norm.** The squared norms of the real and imaginary matrices add to the squared complex matrix norm. Source: `Breakdown.Coercive.SmoothBaseInternal.matNorm_re_im` (`Breakdown/Cert/CoerciveSmoothBase.lean:781`).

**Theorem: Split the squared curl norm.** The squared curls of the real and imaginary matrices add to the squared complex curl norm. Source: `Breakdown.Coercive.SmoothBaseInternal.curl_re_im` (`Breakdown/Cert/CoerciveSmoothBase.lean:786`).

**Theorem: Split a complex Hessian quadratic form.** The Hessian quadratic form on a complex vector is the sum of its real-vector and imaginary-vector quadratic forms. Source: `Breakdown.Coercive.SmoothBaseInternal.secondDerivQuad_re_im` (`Breakdown/Cert/CoerciveSmoothBase.lean:793`).

**Theorem: Split the complex vector norm.** The squared norms of the real and imaginary vectors add to the squared complex vector norm. Source: `Breakdown.Coercive.SmoothBaseInternal.vec_re_im` (`Breakdown/Cert/CoerciveSmoothBase.lean:803`).

**Theorem: Curl square bounded by matrix square.** The squared curl norm is at most twice the sum of squared gradient-column norms. Source: `Breakdown.Coercive.SmoothBaseInternal.curl_le_matNorm` (`Breakdown/Cert/CoerciveSmoothBase.lean:808`).

**Theorem: A squared coordinate is bounded.** Each squared coordinate is at most the squared Euclidean norm. Source: `Breakdown.Coercive.SmoothBaseInternal.coord_sq_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:815`).

**Theorem: Bound a Hessian quadratic form.** The absolute coordinate quadratic form is at most nine times the bilinear operator norm times the squared vector norm. Source: `Breakdown.Coercive.SmoothBaseInternal.quad_abs_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:819`).

**Theorem: The weight-Hessian norm.** The weight's second derivative norm is the operator norm of its second Fréchet derivative. Source: `Breakdown.Coercive.SmoothBaseInternal.secondDerivNorm_eq` (`Breakdown/Cert/CoerciveSmoothBase.lean:837`).

**Theorem: Weighted real div-curl identity.** For the stated divergence-free field, the weighted gradient-curl energy difference equals the Hessian-weight quadratic form, with all terms integrable. Source: `Breakdown.Coercive.SmoothBaseInternal.real_field_identity` (`Breakdown/Cert/CoerciveSmoothBase.lean:841`).

**Theorem: Weighted complex div-curl identity.** The weighted difference between complex gradient and curl squares equals the weight-Hessian quadratic integral, with both terms integrable. Source: `Breakdown.Coercive.SmoothBaseInternal.complex_field_identity` (`Breakdown/Cert/CoerciveSmoothBase.lean:905`).

**Theorem: Rotation preserves the trace.** Conjugating a linear map by axial rotation preserves the sum of its diagonal entries. Source: `Breakdown.Coercive.SmoothBaseInternal.rot_trace` (`Breakdown/Cert/CoerciveSmoothBase.lean:956`).

**Theorem: Symmetry of second derivative modes.** The second derivative mode is unchanged when its two derivative indices are exchanged. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSecondDeriv_symm` (`Breakdown/Cert/CoerciveSmoothBase.lean:964`).

**Theorem: The mode gradients have zero trace.** The gradient mode has zero trace and each spatial derivative of that trace also vanishes. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_mode_trace` (`Breakdown/Cert/CoerciveSmoothBase.lean:973`).

**Theorem: Differentiate an integral in a parameter.** Under the stated regularity and domination assumptions, parameter differentiation passes through the displayed integral. Source: `Breakdown.Coercive.SmoothBaseInternal.param_hasFDerivAt` (`Breakdown/Cert/CoerciveSmoothBase.lean:1028`).

**Definition: Integrate over time and angle.** The double integral runs over one unit of time and one full angular turn. Source: `Breakdown.Coercive.SmoothBaseInternal.doubleIntegral` (`Breakdown/Cert/CoerciveSmoothBase.lean:1042`).

**Theorem: Continuous time-angle integrals.** Under the stated hypotheses, the time-angular double integral is continuous. Source: `Breakdown.Coercive.SmoothBaseInternal.doubleIntegral_continuous` (`Breakdown/Cert/CoerciveSmoothBase.lean:1045`).

**Theorem: Differentiate an integral in a parameter.** Under the stated regularity and domination assumptions, parameter differentiation passes through the displayed integral. Source: `Breakdown.Coercive.SmoothBaseInternal.doubleIntegral_hasFDerivAt` (`Breakdown/Cert/CoerciveSmoothBase.lean:1054`).

**Theorem: Regularity survives bounded integration.** Integrating over the fixed bounded parameter intervals preserves the displayed order of continuous differentiability. Source: `Breakdown.Coercive.SmoothBaseInternal.doubleIntegral_contDiff` (`Breakdown/Cert/CoerciveSmoothBase.lean:1075`).

**Definition: Projection to the rotating plane.** The plane map retains the first two coordinates and sets the axial coordinate to zero. Source: `Breakdown.Coercive.SmoothBaseInternal.rotPlane` (`Breakdown/Cert/CoerciveSmoothBase.lean:1103`).

**Definition: The axial rotation generator.** The rotation generator sends the first two coordinates to their quarter turn and sets the axial coordinate to zero. Source: `Breakdown.Coercive.SmoothBaseInternal.rotTurn` (`Breakdown/Cert/CoerciveSmoothBase.lean:1107`).

**Definition: Projection to the axis.** The axis map retains the third coordinate and sets the first two coordinates to zero. Source: `Breakdown.Coercive.SmoothBaseInternal.rotAxis` (`Breakdown/Cert/CoerciveSmoothBase.lean:1111`).

**Definition: Axial rotation as a linear map.** The linear rotation combines cosine times the plane projection, sine times the plane generator, and the axial projection. Source: `Breakdown.Coercive.SmoothBaseInternal.rotMap` (`Breakdown/Cert/CoerciveSmoothBase.lean:1113`).

**Theorem: Evaluate the linear rotation map.** The continuous linear rotation map agrees with the axial rotation of the vector. Source: `Breakdown.Coercive.SmoothBaseInternal.rotMap_apply` (`Breakdown/Cert/CoerciveSmoothBase.lean:1115`).

**Theorem: Smoothness of linear axial rotation.** Under the stated hypotheses, the linear axial rotation is smooth. Source: `Breakdown.Coercive.SmoothBaseInternal.rotMap_contDiff` (`Breakdown/Cert/CoerciveSmoothBase.lean:1119`).

**Theorem: Evaluate an integrated operator.** Applying the operator-valued double integral to a fixed vector equals integrating the evaluated operator. Source: `Breakdown.Coercive.SmoothBaseInternal.doubleIntegral_apply` (`Breakdown/Cert/CoerciveSmoothBase.lean:1123`).

**Theorem: Differentiate a rotated field average.** The real and imaginary parts of the rotated mode average have the stated spatial derivatives obtained by averaging the corresponding derivatives. Source: `Breakdown.Coercive.SmoothBaseInternal.mode_field` (`Breakdown/Cert/CoerciveSmoothBase.lean:1135`).

**Theorem: Derivatives of real and imaginary modes.** The real and imaginary velocity modes are twice continuously differentiable, and their first and second derivatives are the corresponding real and imaginary derivative modes. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_mode_derivatives` (`Breakdown/Cert/CoerciveSmoothBase.lean:1259`).

**Theorem: Mode differentiation and zero divergence.** The smooth mode calculus supplies the real and imaginary spatial derivatives together with the trace identities required for the div-curl estimate. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_mode_calculus` (`Breakdown/Cert/CoerciveSmoothBase.lean:1308`).

**Theorem: One column uses part of the norm.** The squared complex norm of a selected column or slice is at most the squared norm of the full array. Source: `Breakdown.Coercive.SmoothBaseInternal.column_cnormSq_le` (`Breakdown/Cert/CoerciveSmoothBase.lean:1326`).

**Theorem: One column uses part of the norm.** The squared complex norm of a selected column or slice is at most the squared norm of the full array. Source: `Breakdown.Coercive.SmoothBaseInternal.column_cnormSq_le'` (`Breakdown/Cert/CoerciveSmoothBase.lean:1332`).

**Theorem: Weighted div-curl identity for a mode.** For almost every time, the two weighted derivative-versus-curl differences equal the corresponding weight-Hessian quadratic integrals. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_mode_weight_identity` (`Breakdown/Cert/CoerciveSmoothBase.lean:1338`).

**Theorem: The two weighted curl defects.** On a slice with the stated mode calculus and integrability, the integrated Hessian and gradient curl defects are nonpositive. Source: `Breakdown.Coercive.SmoothBaseInternal.slice_curl_weight` (`Breakdown/Cert/CoerciveSmoothBase.lean:1391`).

**Theorem: The base-density inequality on a mode.** For almost every time, the positive part of the expanded base density and the negative main term are bounded by the positive main term and the negative expanded density. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_per_mode` (`Breakdown/Cert/CoerciveSmoothBase.lean:1426`).

**Theorem: Sum the positive base-density terms.** The positive main mode sum equals the vorticity energy contributions plus the negative-part coefficient times the weighted energy contributions. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSum_mainPos` (`Breakdown/Cert/CoerciveSmoothBase.lean:1539`).

**Theorem: Sum the negative base-density terms.** The negative main mode sum is the positive part of the coercivity coefficient times the weighted Laplacian-and-gradient energy. Source: `Breakdown.Coercive.SmoothBaseInternal.smooth_modeSum_mainNeg` (`Breakdown/Cert/CoerciveSmoothBase.lean:1570`).

### Breakdown.Cert.CoerciveSmoothCurlWeight

Proves the decaying weighted div-curl identity by cutting off the weight, integrating by parts and passing the cutoff to infinity.

**Paper context:** Appendix B, (B.16) and Proposition B.1: the conversion weights that replace curl energies by derivative energies.

**Theorem: Compact support of function g.** Under the stated hypotheses, the function $g$ has compact support. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.compactSupport_of_vanish` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:16`).

**Theorem: Weighted div-curl with compact support.** For a compactly supported weight and divergence-free field, the weighted curl square integral equals the weighted gradient square integral minus the Hessian-weight quadratic integral. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.identity_of_compactSupport` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:22`).

**Definition: A bump between radii one and two.** The fixed smooth bump uses inner radius one and outer radius two. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.bump` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:162`).

**Definition: Rescale the spatial argument.** The linear scaling map multiplies its argument by the displayed inverse radius. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.scaleMap` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:164`).

**Definition: An expanding spatial cutoff.** The cutoff evaluates the fixed bump on the spatial argument divided by the chosen radius. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.cutoff` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:166`).

**Definition: The cut-off weight.** The truncated weight is the original weight multiplied by the expanding spatial cutoff. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.weighted` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:168`).

**Theorem: Evaluate the inverse-radius scaling.** The scaling map multiplies the spatial vector by the displayed reciprocal radius. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.scaleMap_apply` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:170`).

**Theorem: Norm after inverse-radius scaling.** The rescaled vector norm is the original norm multiplied by the nonnegative reciprocal radius. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.norm_scaleMap_apply` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:172`).

**Theorem: Operator norm of the scaling map.** The scaling operator norm is bounded by the stated reciprocal radius. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.norm_scaleMap_le` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:176`).

**Theorem: C2 regularity of cutoff.** Under the stated hypotheses, the spatial cutoff has continuous derivatives through order $2$. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.cutoff_contDiff` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:180`).

**Theorem: Compact support of cutoff.** Under the stated hypotheses, the spatial cutoff has compact support. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.cutoff_hasCompactSupport` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:183`).

**Theorem: The cutoff is one in its inner ball.** The spatial cutoff equals one at every point satisfying the stated inner-radius condition. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.cutoff_eq_one` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:194`).

**Theorem: The cutoff has magnitude at most one.** The absolute value of the spatial cutoff is at most one. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.abs_cutoff_le` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:202`).

**Theorem: Uniform weighted cutoff derivatives.** The stated weighted norms of the cutoff derivatives admit a bound independent of the cutoff index. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.cutoff_deriv_bound` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:207`).

**Theorem: The second derivative norm.** The iterated second derivative and the displayed second Fréchet derivative have the same norm. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.norm_secondDeriv_eq` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:243`).

**Theorem: Uniform Hessian bounds after cutoff.** The Hessians of the cut-off weights obey a common inverse-square radial bound. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.weighted_secondDeriv_bound` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:248`).

**Theorem: The cutoff eventually preserves a germ.** Near any fixed spatial point, the cut-off weight eventually agrees with the original weight. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.weighted_eventuallyEq` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:282`).

**Theorem: Curl square bounded by matrix square.** The squared curl norm is at most twice the sum of squared gradient-column norms. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.curl_sq_le` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:294`).

**Theorem: Nonnegative squared matrix norm.** The sum of squared column norms is nonnegative. Source: `Breakdown.Coercive.SmoothCurlWeight.Internal.matSq_nonneg` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:303`).

**Theorem: Weighted div-curl identity with decay.** The cutoff limit supplies the weighted div-curl identity for the stated decaying fields. Source: `Breakdown.Coercive.curlWeightIdentityDecayHolds_proof` (`Breakdown/Cert/CoerciveSmoothCurlWeight.lean:310`).

### Breakdown.Cert.CoerciveSmoothDensity

Combines the base, curl and velocity contributions into the smooth signed-density estimate, including the actuator pairings.

**Paper context:** Appendix B, Proposition B.1 and (B.20): assembly of the signed coercive density and multiplier pairing.

**Theorem: A sum under a nonnegative integral.** The displayed sum of nonnegative iterated integrals is at most the iterated integral of the sum. Source: `Breakdown.Coercive.Internal.SmoothDensity.iter_add_le` (`Breakdown/Cert/CoerciveSmoothDensity.lean:22`).

**Theorem: Monotonicity over one period.** The stated pointwise or almost-everywhere ordering passes to the iterated nonnegative integral over one time period. Source: `Breakdown.Coercive.Internal.SmoothDensity.iter_mono` (`Breakdown/Cert/CoerciveSmoothDensity.lean:27`).

**Theorem: Additivity over one time period.** The iterated integral of the displayed sum splits into the two iterated integrals under the stated measurability or integrability assumptions. Source: `Breakdown.Coercive.Internal.SmoothDensity.iter_add_left` (`Breakdown/Cert/CoerciveSmoothDensity.lean:31`).

**Theorem: Balance the positive and negative parts.** The extended-nonnegative terms on the two sides obey the stated inequality after a finite real difference is split into positive and negative parts. Source: `Breakdown.Coercive.Internal.SmoothDensity.pos_neg_le` (`Breakdown/Cert/CoerciveSmoothDensity.lean:43`).

**Theorem: Recover a real number from its parts.** The positive part of a real number equals the number plus its negative part. Source: `Breakdown.Coercive.Internal.SmoothDensity.max_split` (`Breakdown/Cert/CoerciveSmoothDensity.lean:58`).

**Theorem: Balance four real contributions.** The sum of the four positive parts plus the negative part of their total equals the positive part of the total plus the four negative parts. Source: `Breakdown.Coercive.Internal.SmoothDensity.ofReal_four` (`Breakdown/Cert/CoerciveSmoothDensity.lean:65`).

**Theorem: Rearrange the modewise sign split.** The stated positive-part inequality allocates the base, curl and velocity contributions into the combined positive density and negative remainder. Source: `Breakdown.Coercive.Internal.SmoothDensity.ofReal_mode` (`Breakdown/Cert/CoerciveSmoothDensity.lean:80`).

**Theorem: Bound a negative part of a sum.** The negative part of a three-term real sum is at most the sum of the three negative parts. Source: `Breakdown.Coercive.Internal.SmoothDensity.ofReal_neg_three` (`Breakdown/Cert/CoerciveSmoothDensity.lean:97`).

**Theorem: Integrate the base sign split.** The assumed signed base estimate yields the displayed extended-nonnegative bound between the integrated positive and negative densities. Source: `Breakdown.Coercive.Internal.SmoothDensity.hbase` (`Breakdown/Cert/CoerciveSmoothDensity.lean:102`).

**Theorem: Combine the base and mode estimates.** The base, stretching, curl and velocity estimates combine into the displayed split lower bound. Source: `Breakdown.Coercive.Internal.SmoothDensity.combine` (`Breakdown/Cert/CoerciveSmoothDensity.lean:174`).

**Theorem: Linearity of the period pairing.** Pairing a field plus a finite actuator combination with a multiplier gives the field pairing plus the same finite linear combination of actuator pairings. Source: `Breakdown.Coercive.Internal.SmoothDensity.pairing_sum` (`Breakdown/Cert/CoerciveSmoothDensity.lean:262`).

**Theorem: Additivity over one time period.** The iterated integral of the displayed sum splits into the two iterated integrals under the stated measurability or integrability assumptions. Source: `Breakdown.Coercive.Internal.SmoothDensity.iterInt_add` (`Breakdown/Cert/CoerciveSmoothDensity.lean:298`).

**Theorem: A nonnegative mode sum is measurable.** The sum over modes of the nonnegative embeddings is almost everywhere measurable for the period measure. Source: `Breakdown.Coercive.Internal.SmoothDensity.aem_tsum` (`Breakdown/Cert/CoerciveSmoothDensity.lean:310`).

**Theorem: Assemble the smooth mode density.** The base density, curl estimate, velocity estimate and pairing identity combine into the smooth mode-density bound. Source: `Breakdown.Coercive.modeDensitySmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothDensity.lean:317`).

### Breakdown.Cert.CoerciveSmoothDensityBase

Controls the negative base-density contributions by finite derivative and weighted-velocity energies.

**Paper context:** Appendix B, (B.16) and Proposition B.1: the conversion weights that replace curl energies by derivative energies.

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.unit_norm` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:21`).

**Theorem: Restricting to one time period.** The product measure on one time period is absolutely continuous with respect to full spacetime volume. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.period_ac` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:25`).

**Theorem: Domination gives a finite integral.** The supplied pointwise domination by a finite nonnegative period integral makes the displayed period integral finite. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.lt_top_of_le` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:29`).

**Definition: Velocity with inverse radial weight.** The weighted field is the velocity divided by one plus the distance from the origin. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.scaled` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:41`).

**Theorem: Rotate a scalar multiple.** A coordinate of the rotation of a scalar multiple equals the scalar times the rotated coordinate. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.axialRot_smul_apply` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:43`).

**Theorem: Radial scaling of velocity-mode energy.** The squared norm of the radially scaled velocity mode is the original squared mode norm divided by $(1+|y|)^2$. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.cnormSq_modeVel_scaled` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:47`).

**Theorem: C2 regularity of function v.** Under the stated hypotheses, the function $v$ has continuous derivatives through order $2$. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.smooth_two` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:78`).

**Theorem: Second derivative field norm.** The norm of the spatial second derivative field equals the norm of the second iterated spatial derivative. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.norm_secondDerivField` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:81`).

**Theorem: Squared Hessian norm bound.** The sum of squared second derivative entries is at most nine times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.secondDerivSq_le` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:86`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.matSq_le` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:100`).

**Theorem: Square-integrable periodic Hessians.** The smooth perturbation's second derivative is measurable, one-periodic and square-integrable on the time slab. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.secondDeriv_facts` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:111`).

**Theorem: Square-integrable periodic gradients.** The smooth perturbation's spatial gradient is measurable, one-periodic and square-integrable on the time slab. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.grad_facts` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:121`).

**Theorem: Square-integrable weighted velocity.** The inverse-radius weighted velocity is measurable, one-periodic and square-integrable on the time slab. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.scaled_facts` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:132`).

**Theorem: Dominate the negative base density.** The negative expanded base expression is bounded by the displayed nonnegative combination of derivative squares and radially weighted velocity squares. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.real_bound` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:152`).

**Theorem: Bound the conversion-weight Hessian.** The Hessian norms of all displayed conversion weights admit one common finite bound. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.secondDerivD_bound` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:178`).

**Theorem: Dominate the negative base density.** The negative base density is bounded pointwise by a common finite combination of Hessian, vorticity-gradient, vorticity, gradient and weighted-velocity mode squares. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.pointwise` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:208`).

**Theorem: Integrate three weighted densities.** The nonnegative integral of three constant-weighted densities is the corresponding weighted sum of their integrals. Source: `Breakdown.Coercive.Internal.SmoothDensity.BaseBound.lint3` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:285`).

**Theorem: Finite negative base-density mass.** The period integral of the mode sum of the nonnegative negative-base-density contributions is finite. Source: `Breakdown.Coercive.Internal.SmoothDensity.base_neg_finite` (`Breakdown/Cert/CoerciveSmoothDensityBase.lean:299`).

### Breakdown.Cert.CoerciveSmoothDensityIntegrable

Proves integrability of the vorticity energy and stretching terms used in the smooth density assembly.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: Integrable smooth derivative squares.** The first and second spatial derivative squares and the inverse-radius weighted velocity square are integrable on one time slab. Source: `Breakdown.Coercive.Internal.SmoothDensity.slice_square_integrable` (`Breakdown/Cert/CoerciveSmoothDensityIntegrable.lean:23`).

**Theorem: Integrable vorticity energy.** The sum of the vorticity-gradient square and one quarter of the vorticity square is integrable on the period slab. Source: `Breakdown.Coercive.Internal.SmoothDensity.vorticity_integrable` (`Breakdown/Cert/CoerciveSmoothDensityIntegrable.lean:51`).

**Theorem: Integrability of stretching-form density.** Under the stated hypotheses, the stretching-form density is integrable. Source: `Breakdown.Coercive.Internal.SmoothDensity.stretch_integrable` (`Breakdown/Cert/CoerciveSmoothDensityIntegrable.lean:94`).

### Breakdown.Cert.CoerciveSmoothDensityMeasure

Establishes measurability of the base and modewise positive and negative densities before their infinite sums are integrated.

**Paper context:** Appendix B, Proposition B.1 and (B.20): assembly of the signed coercive density and multiplier pairing.

**Theorem: Restricting to one time period.** The product measure on one time period is absolutely continuous with respect to full spacetime volume. Source: `Breakdown.Coercive.Internal.SmoothDensity.measure_ac` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:23`).

**Theorem: Lift spatial measurability to spacetime.** The spatial function, viewed as independent of time, is almost everywhere measurable for spacetime volume. Source: `Breakdown.Coercive.Internal.SmoothDensity.lift_snd` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:28`).

**Theorem: Continuity of curl vector.** Under the stated hypotheses, the curl vector is continuous. Source: `Breakdown.Coercive.Internal.SmoothDensity.continuous_curlVec` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:31`).

**Theorem: Measurability of the perturbation jet.** The perturbation and its first two spatial derivative fields are almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.aem_fields` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:35`).

**Theorem: Measurability of the model jet.** The model field and its first two spatial derivative fields are almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.aem_fieldsW` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:44`).

**Theorem: Measurability of curl weight.** Under the stated hypotheses, the curl weight is measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.measurable_eps` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:52`).

**Theorem: Measurability of velocity weight.** Under the stated hypotheses, the velocity weight is measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.measurable_mu` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:57`).

**Theorem: Measurable absolute frame frequency.** The absolute rotating-frame frequency is a measurable spatial function. Source: `Breakdown.Coercive.Internal.SmoothDensity.measurable_dop` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:62`).

**Theorem: Relative-velocity norm is measurable.** Under the stated hypotheses, the norm of the mean velocity relative to the moving frame is measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.measurable_rel` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:67`).

**Theorem: Strong measurability of curl density.** Under the stated hypotheses, the positive curl-mode density is almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.aesm_epsPos` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:75`).

**Theorem: Strong measurability of curl remainder.** Under the stated hypotheses, the curl-mode remainder is almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.aesm_epsRest` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:85`).

**Theorem: Strong measurability of velocity density.** Under the stated hypotheses, the positive velocity-mode density is almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.aesm_muPos` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:128`).

**Theorem: Measurable velocity remainder.** Under the stated hypotheses, the velocity-mode remainder is almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SmoothDensity.aesm_muRest` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:138`).

**Theorem: The modewise base density is measurable.** The base density evaluated on the mode values is almost everywhere strongly measurable for the period measure. Source: `Breakdown.Coercive.Internal.SmoothDensity.aesm_base` (`Breakdown/Cert/CoerciveSmoothDensityMeasure.lean:168`).

### Breakdown.Cert.CoerciveSmoothDensitySquare

Shows that the smooth linearised right-hand side is measurable, periodic and square-integrable on one period.

**Paper context:** Appendix B, Proposition B.1 and (B.20): assembly of the signed coercive density and multiplier pairing.

**Theorem: The linearised field lies in period L2.** The linearised right-hand side is measurable, periodic and square-integrable over one time period and space. Source: `Breakdown.Coercive.Internal.SmoothDensity.smoothRight_square` (`Breakdown/Cert/CoerciveSmoothDensitySquare.lean:22`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentity

Assembles the smooth period identity pairing the linearised equation with the negative Laplacian into vorticity energy and stretching.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: The smooth energy identity on a slice.** The stated slice identity splits the linearised-field pairing with the negative Laplacian into the scaled time pairing, vorticity energy and stretching terms. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.slice_identity` (`Breakdown/Cert/CoerciveSmoothEnergyIdentity.lean:22`).

**Theorem: The smooth energy identity on a slice.** The stated slice identity splits the linearised-field pairing with the negative Laplacian into the scaled time pairing, vorticity energy and stretching terms. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.slice_identity_ae` (`Breakdown/Cert/CoerciveSmoothEnergyIdentity.lean:36`).

**Theorem: The smooth multiplier energy identity.** The time, diffusion and stretching identities supply the energy identity for smooth perturbations. Source: `Breakdown.Coercive.energyIdentitySmoothHolds_proof` (`Breakdown/Cert/CoerciveSmoothEnergyIdentity.lean:50`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentityBounds

Bounds the transport and linearised equation terms by weighted velocity and derivative quantities that have finite period energy.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: Integrability on almost every slice.** Joint integrability on the time slab gives spatial integrability at almost every time. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Bounds.slice_of_joint` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityBounds.lean:18`).

**Theorem: Smoothness of derivative.** Under the stated hypotheses, the spatial derivative is smooth. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Bounds.joint_fderiv` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityBounds.lean:32`).

**Theorem: Smoothness of time derivative.** Under the stated hypotheses, the time derivative is smooth. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Bounds.joint_time` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityBounds.lean:37`).

**Theorem: Smoothness of similarity transport field.** Under the stated hypotheses, the similarity transport field is smooth. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Bounds.joint_transport` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityBounds.lean:47`).

**Theorem: Smooth slice bounds hold a.e..** The smooth perturbation satisfies the six required spatial slice-integrability bounds for almost every time in one period. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.slice_bounds_ae` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityBounds.lean:68`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentityCutoff

Supplies expanding spatial cutoffs and the decaying integration-by-parts rules used in the global energy identity.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Definition: A bump between radii one and two.** The fixed smooth bump uses inner radius one and outer radius two. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.baseBump` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:16`).

**Definition: Rescale the spatial argument.** The linear scaling map multiplies its argument by the displayed inverse radius. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.scaleMap` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:18`).

**Definition: An expanding spatial cutoff.** The cutoff evaluates the fixed bump on the spatial argument divided by the chosen radius. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:20`).

**Definition: Radii tending to infinity.** The cutoff radius at index $n$ is $n+1$. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.radiusSeq` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:22`).

**Theorem: Evaluate the inverse-radius scaling.** The scaling map multiplies the spatial vector by the displayed reciprocal radius. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.scaleMap_apply` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:24`).

**Theorem: Every cutoff radius is at least one.** Every radius in the sequence $n+1$ is at least one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.radiusSeq_one_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:26`).

**Theorem: Every cutoff radius is positive.** Every radius in the sequence $n+1$ is positive. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.radiusSeq_pos` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:31`).

**Theorem: Smoothness of cutoff.** Under the stated hypotheses, the spatial cutoff is smooth. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_contDiff` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:34`).

**Theorem: Nonnegativity of cutoff.** The spatial cutoff is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_nonneg` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:37`).

**Theorem: The cutoff is bounded above by one.** The spatial cutoff takes values at most one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_le_one` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:39`).

**Theorem: Norm after inverse-radius scaling.** The rescaled vector norm is the original norm multiplied by the nonnegative reciprocal radius. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.norm_scaleMap` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:41`).

**Theorem: The cutoff is one in its inner ball.** The spatial cutoff equals one at every point satisfying the stated inner-radius condition. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_eq_one` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:44`).

**Theorem: Compact support of cutoff.** Under the stated hypotheses, the spatial cutoff has compact support. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_support` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:51`).

**Theorem: Differentiate the rescaled cutoff.** The derivative of the cutoff is the derivative of the fixed bump applied to the inversely rescaled direction. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_fderiv` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:61`).

**Theorem: A weighted bound for the bump derivative.** The derivative norm of the fixed bump times one plus the radius has a finite uniform bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.bump_deriv_bound` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:69`).

**Theorem: Decay of a cutoff derivative.** The directional derivative of the cutoff is bounded by the stated constant times the direction norm divided by one plus the radius. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_fderiv_bound` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:83`).

**Theorem: The cutoff eventually equals one.** At a fixed spatial point, the expanding cutoff eventually has value one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_eventually_one` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:111`).

**Theorem: Cutoff derivatives eventually vanish.** At a fixed spatial point, the derivative of the expanding cutoff is eventually zero. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cutoff_fderiv_eventually_zero` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:119`).

**Theorem: Expand a linear functional.** A linear functional applied to a vector is the sum of the coordinate coefficients times its values on the unit vectors. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.clm_apply_expand` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:133`).

**Theorem: Divergence of a scalar times a field.** The divergence of a scalar-weighted field is the scalar times the divergence plus the scalar's directional derivative along the field. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.div_smul` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:138`).

**Theorem: The divergence is continuous.** The stated differentiability of the vector field makes its divergence continuous. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.div_continuous` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:148`).

**Theorem: Spatial divergence integration by parts.** The integral of a directional derivative along the stated field equals minus the integral of the field's divergence times the test scalar. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.compact_div_ibp` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:155`).

**Theorem: Spatial divergence integration by parts.** The integral of a directional derivative along the stated field equals minus the integral of the field's divergence times the test scalar. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.weighted_ibp` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityCutoff.lean:185`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

Defines the time-gradient pairing and the coordinate identities needed to express the smooth energy calculation.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Definition: Time derivative of gradient energy.** The time-pairing density sums the inner products of the spatial gradient with the spatial gradient of the time derivative. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.timePair` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:17`).

**Definition: The two linearised advection terms.** The advection part adds the derivative of the perturbation along the model field to the derivative of the model field along the perturbation. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.advectionPart` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:21`).

**Definition: Integrability on a time slice.** The slice conditions require integrable squares of inverse-radius velocity, first and second spatial derivatives, similarity transport, and spatial derivatives of transport and of the time derivative. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceBounds` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:24`).

**Theorem: Split the linearised Laplacian pairing.** The linearised-field pairing with the negative Laplacian is the sum of its transport, diffusion and advection pairings. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.smoothRight_split` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:32`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.unitVector_norm` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:44`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of each real coordinate is at most the vector norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.coord_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:47`).

**Theorem: A column is bounded by the norm.** The squared norm of each matrix column is at most the squared operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.clm_unit_sq_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:51`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.matSq_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:56`).

**Theorem: Nonnegative squared matrix norm.** The sum of squared column norms is nonnegative. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.matSq_nonneg` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:60`).

**Theorem: Curl square and the cross contraction.** The squared curl norm equals the squared matrix-column norm minus the indicated matrix self-contraction. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.curl_sq_cross` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:64`).

**Theorem: The divergence cross term integrates out.** The displayed second-order cross term is integrable and has zero spatial integral under the divergence-free assumptions. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.cross_term_zero` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:73`).

**Theorem: Integrated curl and gradient energies.** Under the stated divergence-free and integrability assumptions, the integrated squared curl norm equals the integrated squared gradient-column norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.curl_energy` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityDefs.lean:146`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentityRest

Bounds and integrates the vorticity-gradient, vorticity and stretching remainder in the period energy identity.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: The second iterated derivative.** The second iterated derivative and the derivative of the derivative have equal norms. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.norm_iter_two` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:18`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of each real coordinate is at most the vector norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.coord_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:24`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.unit_norm` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:28`).

**Theorem: A matrix entry is bounded.** The absolute value of a matrix entry is at most the operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.apply_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:31`).

**Theorem: A Hessian entry is bounded.** The absolute value of a second derivative entry is at most the bilinear operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.apply2_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:36`).

**Theorem: Alternating symbol bound.** The alternating symbol has absolute value at most one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.eps_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:42`).

**Theorem: Three-term sum bound.** A sum of three terms, each bounded in absolute value by the stated nonnegative constant, has absolute value at most three times that constant. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.sum3_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:45`).

**Theorem: Product of two bounded factors.** The absolute value of a product is bounded by the product of the supplied absolute-value bounds. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.mul2_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:50`).

**Theorem: A vorticity-gradient coordinate bound.** Each displayed vorticity-gradient coordinate is bounded in magnitude by nine times the second derivative operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.vortGrad_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:54`).

**Theorem: Curl controlled by its linear-map norm.** The displayed curl norm or coordinate is bounded by the curl-map operator norm times the gradient operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.curl_coord_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:59`).

**Theorem: Curl controlled by its linear-map norm.** The displayed curl norm or coordinate is bounded by the curl-map operator norm times the gradient operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.curl_norm_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:65`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.matNorm_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:69`).

**Theorem: Nonnegative squared matrix norm.** The sum of squared column norms is nonnegative. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.matNorm_nonneg` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:78`).

**Theorem: Bound the three stretching contractions.** The absolute stretching expression is bounded by the displayed products of velocity, model-derivative and perturbation-gradient norms. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.stretch_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:82`).

**Theorem: Integrability of function f.** Under the stated hypotheses, the function $f$ is integrable. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.joint_integrable` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:123`).

**Theorem: A common quadratic energy bound.** The absolute energy-and-stretching expression is bounded by the listed quadratic combination of derivative and weighted-velocity quantities. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Rest.point_bound` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:136`).

**Theorem: The integrated energy remainder exists.** The spatial integral of the vorticity-gradient square, quarter-vorticity square and stretching density is integrable over the unit time interval. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.rest_integrable` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityRest.lean:165`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentitySliceIntegrable

Establishes the spatial integrability of the products that occur when the smooth energy identity is proved on a time slice.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: Two square-integrable factors.** The product of the two real square-integrable factors is integrable. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.int_mul` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:19`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.unit_norm` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:29`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of each real coordinate is at most the vector norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.comp_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:32`).

**Theorem: A matrix entry is bounded.** The absolute value of a matrix entry is at most the operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.entry_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:36`).

**Theorem: A Hessian entry is bounded.** The absolute value of a second derivative entry is at most the bilinear operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.entry2_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:41`).

**Theorem: Alternating symbol bound.** The alternating symbol has absolute value at most one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.eps_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:47`).

**Theorem: Three-term sum bound.** A sum of three terms, each bounded in absolute value by the stated nonnegative constant, has absolute value at most three times that constant. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.sum3` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:50`).

**Theorem: Product of two bounded factors.** The absolute value of a product is bounded by the product of the supplied absolute-value bounds. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.prod2` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:54`).

**Theorem: Product of three bounded factors.** The absolute value of a three-factor product is bounded by the product of the three supplied bounds. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.prod3` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:58`).

**Theorem: Product of four bounded factors.** The absolute value of a four-factor product is bounded by the product of the four supplied bounds. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.prod4` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:62`).

**Theorem: A vorticity-gradient coordinate bound.** Each displayed vorticity-gradient coordinate is bounded in magnitude by nine times the second derivative operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.vort_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:66`).

**Theorem: Trace bounded by operator norm.** The norm of the second derivative trace is at most three times the operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.trace_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:72`).

**Theorem: The curl norm from its operator norm.** The curl norm is bounded by the curl-map norm times the gradient operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.curl_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:81`).

**Theorem: The first iterated derivative.** The first iterated derivative and the ordinary Fréchet derivative have equal norms. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.norm_iter_one` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:85`).

**Theorem: The second iterated derivative.** The second iterated derivative and the derivative of the derivative have equal norms. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.norm_iter_two` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:91`).

**Theorem: Uniform bounds for the model slice.** The model-field decay assumptions give a common bound for the stated value, first derivative and second derivative quantities on a fixed time slice. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.weight_facts` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:97`).

**Theorem: Continuity of all fields in the identity.** The smooth slice and the displayed spatial and mixed time derivatives are continuous. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.SliceIntegrable.slice_cont` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:131`).

**Theorem: The slice identity terms integrate.** The transport, diffusion, advection, time, vorticity and stretching terms in the slice energy identity are integrable. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.slice_integrable` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySliceIntegrable.lean:156`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentityStretch

Expands the two linearised advection terms and integrates by parts to recover the stretching density.

**Paper context:** Appendix B, (B.18) and Proposition B.1: the stretching term in the base energy identity.

**Theorem: Alternating symbol bound.** The alternating symbol has absolute value at most one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.eps_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:18`).

**Theorem: A matrix entry is bounded.** The absolute value of a matrix entry is at most the operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.entry_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:21`).

**Theorem: A Hessian entry is bounded.** The absolute value of a second derivative entry is at most the bilinear operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.entry2_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:26`).

**Theorem: Nine-term sum bound.** A double sum over three coordinates has absolute value at most nine times a common bound for its entries. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.sum9_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:32`).

**Theorem: Multiply by the alternating symbol.** Multiplication by an alternating-symbol coefficient preserves the stated absolute-value bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.eps_mul_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:44`).

**Theorem: A curl-coordinate operator bound.** Each curl coordinate is bounded in absolute value by nine times the gradient operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.curl_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:52`).

**Theorem: A derivative-of-curl coordinate bound.** Each coordinate derivative of the curl is bounded by nine times the second derivative operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.curl_deriv_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:56`).

**Theorem: A vorticity-gradient coordinate bound.** Each displayed vorticity-gradient coordinate is bounded in magnitude by nine times the second derivative operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.vortGrad_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:62`).

**Theorem: Integrability from domination.** The displayed measurable function is integrable under the supplied integrable domination. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.int_dom` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:67`).

**Theorem: A scaled square stays integrable.** Multiplying the scalar function by a constant preserves integrability of its square. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.sq_const_mul` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:77`).

**Theorem: Weighted coordinate integration by parts.** The displayed integral of a scalar times a coordinate derivative equals minus the integral with that derivative moved to the scalar factor. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.wibp` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:84`).

**Theorem: Weighted coordinate integration by parts.** The displayed integral of a scalar times a coordinate derivative equals minus the integral with that derivative moved to the scalar factor. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.wibp_sum` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:107`).

**Theorem: Product of two bounded factors.** The absolute value of a product is bounded by the product of the supplied absolute-value bounds. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.prod_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:122`).

**Theorem: Negated alternating symbol bound.** The negative of the alternating symbol has absolute value at most one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.neps_abs_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:126`).

**Theorem: Bound a sum inside a product.** The stated absolute-value bounds control the product containing a two-term sum by the sum of its two coefficient bounds. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.sum_term_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:130`).

**Theorem: Bound a two-product expression.** The absolute two-product expression is at most the sum of the two supplied product bounds. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.two_term_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:136`).

**Theorem: Integrability from the common bound.** The displayed measurable function is integrable under the supplied integrable domination. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.int_N` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:150`).

**Theorem: Weighted coordinate integration by parts.** The displayed integral of a scalar times a coordinate derivative equals minus the integral with that derivative moved to the scalar factor. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.wibp_N` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:158`).

**Definition: Decay data for integration by parts.** These conditions collect smoothness, model-field decay and the three integrable perturbation quantities used in the stretching identity. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.DecayData` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:179`).

**Definition: A common perturbation bound.** The common bound adds inverse-radius weighted velocity, the first derivative norm and the second derivative norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.atom` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:190`).

**Theorem: Nonnegative common derivative bound.** The common weighted derivative bound is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.atom_nonneg` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:193`).

**Theorem: The common derivative bound is L2.** The square of the common velocity-and-derivative bound is spatially integrable. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.atom_sq` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:197`).

**Theorem: The common bound controls velocity.** The inverse-radius weighted velocity norm is at most the common bound formed from velocity and its first two derivatives. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.le0` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:219`).

**Theorem: The common bound controls the gradient.** The first derivative norm is at most the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.le1` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:223`).

**Theorem: The common bound controls the Hessian.** The second derivative norm is at most the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.le2` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:228`).

**Theorem: Control every first derivative entry.** Every first derivative entry is bounded in magnitude by the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.du_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:233`).

**Theorem: Control every second derivative entry.** Every second derivative entry is bounded in magnitude by the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.ddu_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:237`).

**Theorem: Curl controlled by the common bound.** Each curl coordinate is bounded in magnitude by nine times the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.curl_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:241`).

**Theorem: Control derivatives of the curl.** Every displayed curl derivative coordinate is bounded by nine times the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.dcurl_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:245`).

**Theorem: One plus a norm is at least one.** One plus the Euclidean norm is at least one. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.one_le_add_norm` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:249`).

**Theorem: Decay absorbs the field growth.** The coefficient-decay and perturbation-growth bounds give the displayed product bound by the common perturbation quantity. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.decay_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:251`).

**Theorem: A uniform model-gradient bound.** The decaying bound for the model gradient implies the stated uniform bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.W1_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:261`).

**Theorem: Decay of model vorticity.** The model vorticity coordinate is bounded by nine times the model constant divided by one plus the radius. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.curlW_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:265`).

**Theorem: A uniform model-vorticity bound.** The model vorticity coordinate has magnitude at most nine times the model constant. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.curlW_le'` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:269`).

**Theorem: Decay of model vorticity derivatives.** Each displayed model-vorticity derivative coordinate is bounded by nine times the model constant divided by one plus the radius. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.dcurlW_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:273`).

**Theorem: Three-term sum bound.** A sum of three terms, each bounded in absolute value by the stated nonnegative constant, has absolute value at most three times that constant. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.sum3_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:282`).

**Theorem: Enlarge a quadratic coefficient.** Increasing the nonnegative coefficient preserves the displayed quadratic upper bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.kmono` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:289`).

**Theorem: Rewrite the mixed vorticity contraction.** Integration by parts rewrites the mixed vorticity-gradient contraction as the displayed half-weighted alternating-symbol term. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.x_term_decay` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:292`).

**Theorem: Divergence-free transport cancels.** The integrated model-transport term paired with the vorticity square derivative is zero under the stated decay and divergence assumptions. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.transport_decay` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:440`).

**Theorem: Control the advection coordinates.** Each coordinate of the two linearised advection terms is bounded by twice the model constant times the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.A_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:513`).

**Theorem: Control the advection derivatives.** Each coordinate derivative of the linearised advection terms is bounded by twelve times the model constant times the common perturbation bound. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Stretch.dA_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:525`).

**Theorem: Convert advection into stretching.** The integrated advection pairing with the negative Laplacian equals the displayed strain and mixed-vorticity stretching expression. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.stretch_decay` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:557`).

**Theorem: Advection yields the stretching form.** On the stated time slice, the advection pairing with the negative Laplacian equals the integral of the stretching form. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.stretch_slice` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityStretch.lean:718`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentitySumSecondPartials

Identifies the squared Laplacian integral with the squared gradient-of-curl integral for the smooth divergence-free perturbation.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: The divergence of a curl vanishes.** The curl of a sufficiently smooth field has zero divergence. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.curl_field_div` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySumSecondPartials.lean:17`).

**Theorem: Laplacian energy is curl-gradient energy.** On the stated divergence-free slice, the squared negative-Laplacian integral equals the squared vorticity-gradient integral. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.sumSecondPartials_slice` (`Breakdown/Cert/CoerciveSmoothEnergyIdentitySumSecondPartials.lean:36`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentityTime

Shows that the time-derivative contribution to the gradient energy integrates to zero over one period.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: A periodic derivative pairs to zero.** The integral of a periodic scalar function times its derivative over one period is zero. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.period_ftc` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:18`).

**Theorem: Integrability of function f square.** Under the stated hypotheses, the squared norm of the function $f$ is integrable. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.sq_integrable` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:33`).

**Theorem: The time-direction derivative is smooth.** The joint derivative of the smooth perturbation applied to the pure time direction is smooth as a spacetime field. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.time_field_smooth` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:44`).

**Theorem: Read the time derivative jointly.** The time-derivative field is the joint spacetime derivative applied to the unit time direction. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.time_field_eq` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:48`).

**Theorem: A continuous time-derivative gradient.** The spatial derivative of the perturbation's time derivative is jointly continuous in time and space. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.time_grad_continuous` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:54`).

**Theorem: Continuity of derivative.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.space_grad_continuous` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:65`).

**Theorem: Bound the gradient time pairing.** The sum of three column inner products is bounded by three times the sum of the two squared operator norms. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.pair_bound` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:69`).

**Theorem: Time pairing of gradients is integrable.** Under the stated hypotheses, the time pairing of spatial gradients is integrable. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.joint_integrable` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:87`).

**Theorem: The time term cancels at a spatial point.** At each fixed spatial point, the integral of the gradient time-pairing density over one period is zero. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Time.slice_time_zero` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:112`).

**Theorem: The full time term cancels.** The spatially integrated gradient time-pairing term has zero integral over one period. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.time_term_zero` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:171`).

**Theorem: Integrate the time-gradient pairing.** The spatial integral of the gradient and time-gradient pairing is integrable over the unit time interval. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.time_integrable` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTime.lean:176`).

### Breakdown.Cert.CoerciveSmoothEnergyIdentityTransport

Computes the similarity-transport pairing with the negative Laplacian and obtains the quarter-gradient-energy contribution.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: Smoothness of function v.** Under the stated hypotheses, the function $v$ is smooth. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.slice_contDiff` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:18`).

**Theorem: Smoothness of time derivative.** Under the stated hypotheses, the time derivative is smooth. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.time_contDiff` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:23`).

**Theorem: Smoothness of similarity transport field.** Under the stated hypotheses, the similarity transport field is smooth. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.transport_contDiff` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:34`).

**Theorem: Differentiate similarity transport.** The spatial derivative of similarity transport splits into the scaled mixed time derivative, the spatial gradient and half the radial Hessian contraction. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.transport_fderiv` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:45`).

**Theorem: Differentiate the gradient energy.** The directional derivative of the squared gradient-column norm is twice the sum of each gradient column paired with its directional derivative. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.energy_fderiv` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:65`).

**Theorem: Transport paired with the gradient.** The pointwise transport-gradient pairing is the scaled time pairing plus gradient energy and one quarter of its radial derivative. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.pointwise_pair` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:81`).

**Theorem: Two square-integrable factors.** The product of the two real square-integrable factors is integrable. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.int_mul_of_sq` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:95`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of each real coordinate is at most the vector norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.abs_apply_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:108`).

**Theorem: A matrix entry is bounded.** The absolute value of a matrix entry is at most the operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.clm_entry_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:112`).

**Theorem: A Hessian entry is bounded.** The absolute value of a second derivative entry is at most the bilinear operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.clm2_entry_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:117`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.matNorm_le` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:123`).

**Theorem: Pair two square-integrable fields.** The inner product of the two square-integrable fields is integrable on the displayed measure space. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.int_inner_of_sq` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:135`).

**Theorem: Divergence of the radius vector.** The divergence of the identity vector field in three-dimensional space is three. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.div_id` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:149`).

**Theorem: Move the Laplacian onto a gradient.** The integral pairing a field with the negative Laplacian equals the sum of the corresponding gradient-column pairings. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.Transport.step_one` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:154`).

**Theorem: Transport gives quarter gradient energy.** The transport pairing with the negative Laplacian equals the scaled time-pairing integral plus one quarter of the vorticity energy integral. Source: `Breakdown.Coercive.SmoothEnergyIdentityInternal.transport_slice` (`Breakdown/Cert/CoerciveSmoothEnergyIdentityTransport.lean:212`).

### Breakdown.Cert.CoerciveSmoothEps

Provides the smooth curl-weight inequality by combining the pointwise mode estimate, diffusion control and summable remainder bounds.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: Turn a real bound into a sign split.** The stated real inequality gives the corresponding extended-nonnegative inequality after positive and negative parts are separated. Source: `Breakdown.Coercive.SmoothEpsInternal.ofReal_bound_of_le` (`Breakdown/Cert/CoerciveSmoothEps.lean:19`).

**Theorem: Read the period integral on the slab.** The iterated nonnegative period integral equals integration against the unit-time product measure. Source: `Breakdown.Coercive.SmoothEpsInternal.lintegral_slab_eq` (`Breakdown/Cert/CoerciveSmoothEps.lean:27`).

**Theorem: Read the real integral on the slab.** The displayed iterated real integral equals the integral against the unit-time product measure. Source: `Breakdown.Coercive.SmoothEpsInternal.integral_slab_eq` (`Breakdown/Cert/CoerciveSmoothEps.lean:31`).

**Theorem: The curl estimate for one mode.** The positive curl-mode density is controlled by its signed pairing term and the integrated negative remainder, in the split nonnegative form. Source: `Breakdown.Coercive.SmoothEpsInternal.epsMode_bound` (`Breakdown/Cert/CoerciveSmoothEps.lean:35`).

**Theorem: The smooth curl-mode estimate.** The per-mode lower bound, summability and remainder estimates supply the smooth curl-weight estimate. Source: `Breakdown.Coercive.modeEpsEstimateSmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothEps.lean:105`).

### Breakdown.Cert.CoerciveSmoothEpsAssembly

Integrates and sums the signed curl-mode bounds to produce the curl contribution to the smooth coercive estimate.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Definition: Spacetime measure on one period.** The measure is Lebesgue measure restricted to the unit time interval, multiplied by spatial Lebesgue measure. Source: `Breakdown.Coercive.SmoothEpsInternal.slabMeasure` (`Breakdown/Cert/CoerciveSmoothEpsAssembly.lean:14`).

**Theorem: Exchange the mode sum and integral.** Under the stated measurability assumptions, the nonnegative sum over modes can be interchanged with integration over one time period and space. Source: `Breakdown.Coercive.SmoothEpsInternal.lintegral_tsum_slab` (`Breakdown/Cert/CoerciveSmoothEpsAssembly.lean:16`).

**Theorem: A real value as its positive part.** Embedding a real number into extended nonnegative reals gives the same value as embedding its maximum with zero. Source: `Breakdown.Coercive.SmoothEpsInternal.ofReal_eq_ofReal_max` (`Breakdown/Cert/CoerciveSmoothEpsAssembly.lean:22`).

**Theorem: Sum the signed mode estimates.** The summable mode inequalities yield the displayed bound for the real total after its positive and negative parts are separated. Source: `Breakdown.Coercive.SmoothEpsInternal.real_of_tsum_bound` (`Breakdown/Cert/CoerciveSmoothEpsAssembly.lean:27`).

**Theorem: Assemble modewise lower bounds.** The stated summability and per-mode bounds combine into the split lower-bound predicate for the full mode sum. Source: `Breakdown.Coercive.SmoothEpsInternal.isSplitLowerBound_of_modes` (`Breakdown/Cert/CoerciveSmoothEpsAssembly.lean:64`).

### Breakdown.Cert.CoerciveSmoothEpsIntegrable

Proves integrability of the frequency, curl-pairing and weight-gradient terms used in the curl-weight estimate.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: Control the curl weight-gradient charge.** The curl-weight derivative charge is bounded by its uniform coefficient times the squared Hessian and gradient mode norms. Source: `Breakdown.Coercive.SmoothEpsInternal.epsGradTerm_le` (`Breakdown/Cert/CoerciveSmoothEpsIntegrable.lean:16`).

**Theorem: All curl-mode pairing terms integrate.** The linearised-field pairing, negative-Laplacian pairing and weight-gradient error are integrable over one time slab. Source: `Breakdown.Coercive.SmoothEpsInternal.integrable_epsTerms` (`Breakdown/Cert/CoerciveSmoothEpsIntegrable.lean:42`).

### Breakdown.Cert.CoerciveSmoothEpsMeasurable

Establishes the measurability of the positive curl-mode density and its negative remainder on the period slab.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: Measurable curl-weight data.** The curl weight, its gradient bound, the frame frequency and the frame rate are almost everywhere measurable as spacetime functions. Source: `Breakdown.Coercive.SmoothEpsInternal.aemeasurable_weights` (`Breakdown/Cert/CoerciveSmoothEpsMeasurable.lean:17`).

**Theorem: C2 regularity of function v.** Under the stated hypotheses, the function $v$ has continuous derivatives through order $2$. Source: `Breakdown.Coercive.SmoothEpsInternal.contDiff_two_of_smooth` (`Breakdown/Cert/CoerciveSmoothEpsMeasurable.lean:32`).

**Theorem: Curl density is ae measurable.** Under the stated hypotheses, the positive curl-mode density is almost everywhere measurable. Source: `Breakdown.Coercive.SmoothEpsInternal.aemeasurable_modeEpsPos` (`Breakdown/Cert/CoerciveSmoothEpsMeasurable.lean:36`).

**Theorem: Curl remainder is ae measurable.** Under the stated hypotheses, the curl-mode remainder is almost everywhere measurable. Source: `Breakdown.Coercive.SmoothEpsInternal.aemeasurable_modeEpsRest` (`Breakdown/Cert/CoerciveSmoothEpsMeasurable.lean:48`).

### Breakdown.Cert.CoerciveSmoothEpsModeBounds

Dominates the integrated curl pairing by square-mode energies and gives the measurability needed to sum it.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: One gradient mode costs no more.** The square integral of one gradient mode is at most the physical gradient square integral over the period. Source: `Breakdown.Coercive.SmoothEpsInternal.lintegral_modeGrad_le` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:17`).

**Theorem: Gradient-mode energy is measurable a.e..** Under the stated hypotheses, the squared complex norm of the gradient mode is almost everywhere strongly measurable. Source: `Breakdown.Coercive.SmoothEpsInternal.aesm_cnormSq_modeGrad` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:25`).

**Theorem: Integrability of gradient mode square.** Under the stated hypotheses, the squared complex norm of the gradient mode is integrable. Source: `Breakdown.Coercive.SmoothEpsInternal.integrable_cnormSq_modeGrad` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:30`).

**Theorem: Integrable second-derivative mode energy.** Under the stated hypotheses, the squared complex norm of the second derivative mode is integrable. Source: `Breakdown.Coercive.SmoothEpsInternal.integrable_cnormSq_modeSecondDeriv` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:38`).

**Theorem: Absorb a pairing into square energies.** The supplied pairing bound and sign assumptions imply the displayed coefficient times the sum of the two nonnegative energies. Source: `Breakdown.Coercive.SmoothEpsInternal.abs_bound_aux` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:50`).

**Theorem: Bound a curl-mode pairing density.** The absolute curl-pairing density is bounded by the uniform curl weight times the two squared gradient-mode norms. Source: `Breakdown.Coercive.SmoothEpsInternal.abs_epsIntegrand_le` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:58`).

**Theorem: Strong measurability of curl pairing.** Under the stated hypotheses, the curl-weight pairing density is almost everywhere strongly measurable. Source: `Breakdown.Coercive.SmoothEpsInternal.aesm_epsIntegrand` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:67`).

**Theorem: Continuity of signed curl weight.** Under the stated hypotheses, the signed curl weight is continuous. Source: `Breakdown.Coercive.SmoothEpsInternal.epsW_continuous` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:86`).

**Theorem: Integrability of curl pairing.** Under the stated hypotheses, the curl-weight pairing density is integrable. Source: `Breakdown.Coercive.SmoothEpsInternal.integrable_epsIntegrand` (`Breakdown/Cert/CoerciveSmoothEpsModeBounds.lean:92`).

### Breakdown.Cert.CoerciveSmoothEpsPointwise

Derives the single-mode curl estimate by separating frame frequency, model interactions and the weighted diffusion pairing.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: A lower bound for the curl remainder.** The sum of the curl-mode remainder and weight-gradient charge is at most the signed pairing with the full frame remainder. Source: `Breakdown.Coercive.SmoothEpsInternal.frameRest_lower` (`Breakdown/Cert/CoerciveSmoothEpsPointwise.lean:16`).

**Theorem: Separate the resonant imaginary pairing.** The displayed real imaginary pairing splits into its Laplacian term, frequency times squared mode norm and remainder pairing. Source: `Breakdown.Coercive.SmoothEpsInternal.re_split` (`Breakdown/Cert/CoerciveSmoothEpsPointwise.lean:85`).

**Theorem: The pointwise curl-mode lower bound.** The curl frequency density, remainder, gradient charge and negative-Laplacian pairing together are at most the linearised-field pairing density. Source: `Breakdown.Coercive.SmoothEpsInternal.epsIntegrand_lower` (`Breakdown/Cert/CoerciveSmoothEpsPointwise.lean:98`).

### Breakdown.Cert.CoerciveSmoothEpsPointwiseModes

Bounds each transport, stretching and model-vorticity contribution in the rotating-frame curl-mode equation.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: Rotation respects the moving frame.** Pulling back the radial and rotational frame vectors by axial rotation gives their unrotated coordinate form. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.rot_frame` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:19`).

**Theorem: Bound vorticity transport by modes.** The vorticity-transport amplitude is bounded by the relative mean speed times the vorticity-gradient amplitude plus the model-wave convolution. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.transport_le` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:35`).

**Theorem: Mean and wave stretching bounds.** The stretching mode equals the mean-gradient action on vorticity plus a remainder bounded by the model-gradient wave convolution. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.stretch_split` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:72`).

**Theorem: Bound transport of model vorticity.** The model-vorticity transport mode is bounded by the mean vorticity-gradient norm times velocity amplitude plus the corresponding wave convolution. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.vortTransport_le` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:102`).

**Theorem: Bound stretching by model vorticity.** The model-vorticity stretching mode is bounded by the mean vorticity norm times gradient amplitude plus the corresponding wave convolution. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.vortStretch_le` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:132`).

**Theorem: Split the five frame-remainder terms.** The frame remainder splits into transport, negative stretching, model-vorticity transport, negative model-vorticity stretching and rotation terms. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.frame_split` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:155`).

**Theorem: Bound the alternating cross term.** The stated alternating real-imaginary cross expression is bounded by the absolute coefficient and the indicated squared-vector energy. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.cross_bound` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:195`).

**Theorem: Control the skew part of mean stretching.** The imaginary mean-gradient pairing is bounded by half the curl norm times the absolute weight and squared complex-vector norm. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.mean_stretch_re_le` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:228`).

**Theorem: Bound a weighted imaginary pairing.** The absolute real part of the imaginary weighted pairing is at most the absolute weight times the two vector norms. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.re_cdot_abs_le` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseModes.lean:258`).

### Breakdown.Cert.CoerciveSmoothEpsPointwiseProduct

Reconstructs the finite model harmonics and computes their convolution with perturbation modes in matrix-vector products.

**Paper context:** Appendix B, (B.16) and Proposition B.1: finite harmonic interactions in the curl-weighted estimate.

**Theorem: Opposite velocity modes are conjugate.** For a real field, negating both frequency indices conjugates the velocity-mode coefficient. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.modeVel_neg` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:17`).

**Theorem: A uniform derivative bound from decay.** The stated derivative-decay assumption gives a finite uniform bound for the displayed model derivative. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.grad_bound_of_decay` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:21`).

**Theorem: Reconstruct the model field from modes.** The rotated model field equals its mean plus the displayed finite wave sum. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.velW_expansion` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:34`).

**Theorem: Reconstruct the model gradient.** The rotated model gradient equals its mean gradient plus the displayed finite gradient-mode wave sum. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.gradW_expansion` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:47`).

**Theorem: Reconstruct model vorticity from modes.** The rotated model vorticity equals mean vorticity plus the finite sum of curl-mode waves. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.vortW_expansion` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:61`).

**Theorem: Modes of a matrix-vector product.** The mode of the displayed matrix-vector product is the mean contribution plus the convolution of the finite coefficient modes with shifted input modes. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.mode_product_vec` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:82`).

**Theorem: Real vectors inside complex space.** Viewing a real vector as a complex vector preserves its Euclidean norm. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.cnorm3_ofReal` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:146`).

**Theorem: Bound the mode convolution norm.** The norm of the matrix-vector mode convolution is at most the mean product bound plus the sum of the shifted mode-amplitude products. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.cnorm3_product_le` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:153`).

**Theorem: Gradient modes of vorticity.** Taking the gradient mode of vorticity equals the curl-gradient contraction of the second derivative mode. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.modeGrad_vort_eq` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseProduct.lean:170`).

### Breakdown.Cert.CoerciveSmoothEpsPointwiseSecondDeriv

Differentiates gradient modes and reconstructs second-derivative and model-vorticity-gradient harmonics for the curl interactions.

**Paper context:** Appendix B, (B.16) and Proposition B.1: finite harmonic interactions in the curl-weighted estimate.

**Definition: The gradient mode integrand.** The gradient-mode integrand multiplies the rotated gradient coordinate by its complex Fourier phase. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.gradModeIntegrand` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:16`).

**Definition: Derivative of the mode integrand.** The proposed derivative composes the rotated second derivative with the coordinate functional and the complex Fourier phase. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.gradModeIntegrandDeriv` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:20`).

**Theorem: Evaluate the mode-integrand derivative.** Applying the gradient-mode integrand's derivative gives the phase-weighted rotated Hessian coordinate in the displayed direction. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.gradModeIntegrandDeriv_apply` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:26`).

**Theorem: The model gradient is differentiable.** The spatial gradient of the model field is differentiable on each time slice under the stated second-order regularity. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.slice_fderiv_differentiable` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:32`).

**Theorem: Differentiate the rotated integrand.** The displayed phase-weighted rotated integrand has the stated Fréchet derivative. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.hasFDerivAt_gradModeIntegrand` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:36`).

**Theorem: Bound the rotated integrand derivative.** The gradient-mode integrand derivative has operator norm at most that of the model Hessian at the rotated point. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.norm_gradModeIntegrandDeriv_le` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:50`).

**Theorem: Continuity of gradient-mode integrand.** Under the stated hypotheses, the gradient-mode integrand is continuous. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.continuous_gradModeIntegrand` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:67`).

**Theorem: Continuity of mode-integrand derivative.** Under the stated hypotheses, the spatial derivative of the gradient-mode integrand is continuous. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.continuous_gradModeIntegrandDeriv` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:78`).

**Theorem: A mode coefficient as a box integral.** The displayed mode coordinate is its phase-weighted time-angular integrand divided by the full angular length. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.modeGrad_eq_box` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:93`).

**Theorem: Differentiate a gradient mode.** The gradient-mode coordinate has a Fréchet derivative whose coordinate values are the corresponding second derivative mode entries. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.modeGrad_hasFDerivAt` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:104`).

**Theorem: A uniform derivative bound from decay.** The stated derivative-decay assumption gives a finite uniform bound for the displayed model derivative. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.secondDeriv_bound_of_decay` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:137`).

**Theorem: Opposite modes are conjugate.** For the displayed real input, reversing both frequency indices conjugates its complex mode coefficient. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.modeSecondDeriv_neg` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:150`).

**Theorem: Reconstruct second derivative modes.** The rotated model Hessian equals its zero mode plus the finite sum of its second derivative wave modes in the displayed real or complex form. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.secondDeriv_expansion` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:155`).

**Theorem: Reconstruct second derivative modes.** The rotated model Hessian equals its zero mode plus the finite sum of its second derivative wave modes in the displayed real or complex form. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.secondDerivC_expansion` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:194`).

**Theorem: Differentiate mean vorticity in modes.** A coordinate derivative of mean vorticity is the alternating-symbol contraction of the real zero-mode Hessian entries. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.meanCurl_fderiv_apply` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:208`).

**Theorem: Reconstruct the vorticity gradient.** The rotated model-vorticity gradient equals its mean part plus the finite wave sum of curl-gradient modes. Source: `Breakdown.Coercive.Internal.SmoothEpsPointwise.vortGradW_expansion` (`Breakdown/Cert/CoerciveSmoothEpsPointwiseSecondDeriv.lean:239`).

### Breakdown.Cert.CoerciveSmoothEpsRightGradient

Proves regularity, periodicity and finite gradient energy of the smooth linearised right-hand side used in the curl pairing.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: Cm regularity of derivative.** Under the stated hypotheses, the spatial derivative has continuous derivatives through order $m$. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.contDiff_fderiv_param` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:16`).

**Theorem: Cn regularity of function F.** Under the stated hypotheses, the function $F$ has continuous derivatives through order $n$. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.contDiff_slice` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:22`).

**Theorem: Time derivative from the joint field.** The time derivative equals the joint Fréchet derivative applied to the unit time direction. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.deriv_time_eq` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:27`).

**Definition: Transport as a spacetime function.** The joint transport field combines the scaled time derivative, half the velocity and half the derivative along the spatial radius. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.transportJoint` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:34`).

**Theorem: Joint and curried transport agree.** Evaluating the joint spacetime transport on a time-space pair gives the original time-dependent transport field. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.transportPart_eq` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:38`).

**Theorem: The joint similarity transport is C1.** Under the stated hypotheses, the joint similarity transport field has continuous derivatives through order $1$. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.contDiff_transportJoint` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:45`).

**Definition: The negative second derivative trace.** The negative trace map returns the negative sum of the second derivative evaluated on each repeated coordinate unit vector. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.negTrace` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:56`).

**Theorem: Evaluate the negative trace map.** The negative trace map is the negative sum of the three diagonal second derivative values. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.negTrace_apply` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:60`).

**Theorem: Expand the linearised right-hand side.** The displayed identity separates similarity transport, the negative Laplacian and the two linearised advection contributions, with the indicated subtraction where present. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.smoothRight_eq` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:63`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.matSq_le` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:70`).

**Theorem: Differentiate a derivative on a field.** Differentiating a field's derivative applied to another field gives the derivative-composition term plus the Hessian applied to the second field. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.apply_hasFDerivAt` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:80`).

**Theorem: Bound a differentiated operator product.** The norm of the differentiated operator-field product is bounded by the sum of the two operator-norm products from the product rule. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.norm_apply_deriv_le` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:86`).

**Theorem: Control the linearised gradient.** The spatial derivative of the linearised right-hand side is bounded by transport derivatives, third derivatives and the displayed model-perturbation derivative products. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.norm_fderiv_smoothRight_le` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:92`).

**Theorem: The second iterated derivative.** The second iterated derivative and the derivative of the derivative have equal norms. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.norm_iteratedFDeriv_two_eq` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:123`).

**Theorem: The third iterated derivative.** The third iterated derivative has the norm of the three successive Fréchet derivatives. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.norm_iteratedFDeriv_three_eq` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:127`).

**Theorem: Subadditivity of the period integral.** The nonnegative period integral of the sum is at most the sum of the two period integrals under the stated continuity assumptions. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.periodLIntegral_add_of_continuous` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:131`).

**Theorem: Scaling preserves finiteness.** Multiplication by the stated finite constant preserves finiteness of the nonnegative period integral. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.periodLIntegral_const_mul_lt_top` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:146`).

**Theorem: Domination gives a finite integral.** The supplied pointwise domination by a finite nonnegative period integral makes the displayed period integral finite. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.periodLIntegral_lt_top_of_le` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:157`).

**Theorem: Square of a five-term sum.** The square of a five-term real sum is at most five times the sum of the five squares. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.sq_sum_five_le` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:161`).

**Theorem: Finite gradient energy of the forcing.** The squared matrix norm of the gradient of the smooth linearised right-hand side has finite integral over one spacetime period. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.gradField_smoothRight_sq_finite` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:166`).

**Theorem: Time periodicity of linearised field.** Under the stated hypotheses, the linearised right-hand side has period one in time. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.smoothRight_periodic` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:280`).

**Theorem: The linearised gradient lies in L2.** The spatial gradient of the linearised right-hand side is measurable, one-periodic and square-integrable over the time slab. Source: `Breakdown.Coercive.Internal.SmoothRightGradient.gradField_smoothRight_square` (`Breakdown/Cert/CoerciveSmoothEpsRightGradient.lean:291`).

### Breakdown.Cert.CoerciveSmoothEpsSetting

Defines the signed curl-pairing density and gathers the admissibility, regularity and decay hypotheses for the smooth curl estimate.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Definition: Data for the curl-mode estimate.** These conditions collect admissible curl weights, model-field regularity and decay, and a smooth perturbation for the curl estimate. Source: `Breakdown.Coercive.SmoothEpsInternal.EpsSetting` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:14`).

**Definition: One curl-weight pairing density.** The curl-pairing density is the real part of the imaginary signed weight times the complex pairing of two vorticity modes. Source: `Breakdown.Coercive.SmoothEpsInternal.epsIntegrand` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:25`).

**Definition: One integrated curl-mode term.** The curl-mode term integrates its pairing density over space and one time period. Source: `Breakdown.Coercive.SmoothEpsInternal.epsModeTerm` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:29`).

**Theorem: The curl pairing is a mode sum.** The curl-weight pairing equals the sum over all modes of the corresponding integrated curl-mode terms. Source: `Breakdown.Coercive.SmoothEpsInternal.epsPairing_eq_tsum` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:32`).

**Definition: The negative spatial Laplacian.** This field is the negative trace of the spatial second derivative. Source: `Breakdown.Coercive.SmoothEpsInternal.negSumSecondPartialsOfField` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:35`).

**Definition: Curl-weight derivative charge.** The curl-weight derivative charge multiplies the weight-gradient bound by the vorticity and vorticity-gradient mode amplitudes. Source: `Breakdown.Coercive.SmoothEpsInternal.epsGradTerm` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:38`).

**Theorem: A negative sum of positive terms.** The displayed negative sum is nonpositive when its component quantities satisfy the stated sign assumptions. Source: `Breakdown.Coercive.SmoothEpsInternal.neg_sum_five_nonpos` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:41`).

**Theorem: Nonpositivity of curl remainder.** The curl-mode remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.SmoothEpsInternal.modeEpsRest_nonpos` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:44`).

**Theorem: Nonnegativity of curl density.** The positive curl-mode density is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.SmoothEpsInternal.modeEpsPos_nonneg` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:50`).

**Theorem: Nonnegative curl weight-gradient charge.** The curl-weight gradient charge is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.SmoothEpsInternal.epsGradTerm_nonneg` (`Breakdown/Cert/CoerciveSmoothEpsSetting.lean:55`).

### Breakdown.Cert.CoerciveSmoothEpsSquare

Provides the periodicity and finite gradient energies of the right-hand side and diffusion field needed for curl-mode square sums.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: Time periodicity of linearised field.** Under the stated hypotheses, the linearised right-hand side has period one in time. Source: `Breakdown.Coercive.SmoothEpsInternal.smoothRight_periodic` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:18`).

**Theorem: Negative Laplacian field is periodic.** Under the stated hypotheses, the negative Laplacian field has period one in time. Source: `Breakdown.Coercive.SmoothEpsInternal.negSumSecondPartialsOfField_periodic` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:29`).

**Theorem: Time periodicity of gradient.** Under the stated hypotheses, the spatial gradient field has period one in time. Source: `Breakdown.Coercive.SmoothEpsInternal.gradField_periodic` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:36`).

**Theorem: Time derivative from the joint field.** The time derivative equals the joint Fréchet derivative applied to the unit time direction. Source: `Breakdown.Coercive.SmoothEpsInternal.deriv_eq_fderiv` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:42`).

**Theorem: C1 regularity of second derivative.** Under the stated hypotheses, the spatial second derivative has continuous derivatives through order $1$. Source: `Breakdown.Coercive.SmoothEpsInternal.contDiff_secondDerivField_one` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:50`).

**Theorem: C1 regularity of linearised field.** Under the stated hypotheses, the linearised right-hand side has continuous derivatives through order $1$. Source: `Breakdown.Coercive.SmoothEpsInternal.contDiff_smoothRight` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:58`).

**Theorem: Continuity of gradient.** Under the stated hypotheses, the spatial gradient field is continuous. Source: `Breakdown.Coercive.SmoothEpsInternal.continuous_gradField_of` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:82`).

**Theorem: The forcing gradient has finite energy.** The squared matrix norm of the smooth right-hand side's gradient has finite period integral. Source: `Breakdown.Coercive.SmoothEpsInternal.periodLIntegral_gradSmoothRight_lt_top` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:87`).

**Definition: The negative second derivative trace.** The negative trace map returns the negative sum of the second derivative evaluated on each repeated coordinate unit vector. Source: `Breakdown.Coercive.SmoothEpsInternal.negTraceMap` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:93`).

**Theorem: Evaluate the negative trace map.** The negative trace map is the negative sum of the three diagonal second derivative values. Source: `Breakdown.Coercive.SmoothEpsInternal.negTraceMap_apply` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:97`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.SmoothEpsInternal.columnSq_le_three` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:100`).

**Theorem: Control the gradient of the Laplacian.** The squared column norm of the Laplacian gradient is bounded by three times the squared trace-map norm times the squared third derivative norm. Source: `Breakdown.Coercive.SmoothEpsInternal.columnSq_gradSumSecondPartials_le` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:110`).

**Theorem: Finite gradient energy of diffusion.** The squared matrix norm of the negative Laplacian field's gradient has finite period integral. Source: `Breakdown.Coercive.SmoothEpsInternal.periodLIntegral_gradSumSecondPartials_lt_top` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:130`).

**Theorem: The linearised gradient lies in L2.** The spatial gradient of the linearised right-hand side is measurable, one-periodic and square-integrable over the time slab. Source: `Breakdown.Coercive.SmoothEpsInternal.square_gradSmoothRight` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:153`).

**Theorem: The Laplacian gradient lies in L2.** The gradient of the negative-Laplacian field is measurable, periodic and square-integrable on the time slab. Source: `Breakdown.Coercive.SmoothEpsInternal.square_gradSumSecondPartials` (`Breakdown/Cert/CoerciveSmoothEpsSquare.lean:164`).

### Breakdown.Cert.CoerciveSmoothEpsSumSecondPartials

Obtains the weighted curl-diffusion lower bound from the real and imaginary mode integration-by-parts identity.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Theorem: The curl diffusion loss is controlled.** The curl pairing with the negative Laplacian is bounded below by minus the integrated curl-weight gradient charge. Source: `Breakdown.Coercive.SmoothEpsInternal.epsSumSecondPartials_lower` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartials.lean:15`).

### Breakdown.Cert.CoerciveSmoothEpsSumSecondPartialsModes

Relates derivatives and Laplacians of real and imaginary vorticity modes to the original derivative modes, and proves the necessary product integrability.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Definition: Real part of a vorticity mode.** The real vorticity-mode field is assembled from the real parts of its three complex coordinates. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortRe` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:16`).

**Definition: Imaginary part of a vorticity mode.** The imaginary vorticity-mode field is assembled from the imaginary parts of its three complex coordinates. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortIm` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:19`).

**Definition: The spatial Laplacian.** The spatial Laplacian is the trace of the second Fréchet derivative. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.sspOf` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:22`).

**Theorem: The real vorticity mode is C2.** Under the stated hypotheses, the real vorticity-mode field has continuous derivatives through order $2$. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortRe_contDiff` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:25`).

**Theorem: The imaginary vorticity mode is C2.** Under the stated hypotheses, the imaginary vorticity-mode field has continuous derivatives through order $2$. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortIm_contDiff` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:29`).

**Theorem: Differentiate real vorticity modes.** The spatial derivative of the real vorticity mode is the real part of the corresponding curl-gradient second derivative mode. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.fderiv_vortRe_apply` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:33`).

**Theorem: Differentiate imaginary vorticity modes.** The spatial derivative of the imaginary vorticity mode is the imaginary part of the corresponding curl-gradient second derivative mode. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.fderiv_vortIm_apply` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:39`).

**Theorem: Curl modes commute with the Laplacian.** The curl mode of the negative-Laplacian field is minus the combined Laplacians of the real and imaginary vorticity modes. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.curl_sumSecondPartials_mode` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:45`).

**Theorem: Read a coordinate expansion.** The indicated coordinate of a sum of coordinate unit vectors equals its coefficient. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.sum_unit_apply` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:51`).

**Theorem: Euclidean norm in coordinates.** The squared Euclidean norm is the sum of the squared real coordinates. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_sq_space` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:54`).

**Theorem: Inner product in coordinates.** The real inner product is the sum of coordinatewise products. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.inner_space` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:58`).

**Theorem: Norm of a coordinate expansion.** A vector expanded in the coordinate basis has squared norm equal to the sum of squared coefficients. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_sq_sum_unit` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:61`).

**Theorem: Imaginary pairing in real components.** The real part of the imaginary weighted complex pairing is the stated antisymmetric pairing of its real and imaginary vector components. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.re_I_cdot` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:65`).

**Theorem: Bound the weighted derivative flux.** The absolute derivative-flux sum is bounded by the weight-gradient norm times the two combined square-root energies. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.grad_pair_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:73`).

**Theorem: Read a real vorticity-mode coordinate.** A coordinate of the real vorticity-mode vector is the real part of that complex vorticity coordinate. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortRe_apply` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:100`).

**Theorem: Read an imaginary vorticity coordinate.** A coordinate of the imaginary vorticity-mode vector is the imaginary part of that complex vorticity coordinate. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortIm_apply` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:105`).

**Theorem: Real and imaginary squared norms.** A complex number's squared norm is the sum of its squared real and imaginary parts. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_sq_complex` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:110`).

**Theorem: Vorticity amplitude from its real parts.** The vorticity amplitude is the square root of the sum of the real and imaginary vorticity-vector squares. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortAmp_eq` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:114`).

**Theorem: Vorticity-gradient amplitude by columns.** The vorticity-gradient amplitude is the square root of the sum of squared real and imaginary gradient-column norms. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vortGradAmp_eq` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:122`).

**Theorem: Continuity of Laplacian.** Under the stated hypotheses, the spatial Laplacian is continuous. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.continuous_sspOf` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:135`).

**Definition: Amplitude of the vorticity Laplacian.** The amplitude is the complex norm of the vorticity mode of the negative Laplacian field. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.sspAmp` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:141`).

**Theorem: One component of a two-term norm.** The stated nonnegative component is at most the square root of the sum of the two squares. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_le_sqrt_add` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:144`).

**Theorem: A real component fits the mode amplitude.** The real or imaginary vorticity-vector norm is at most the full vorticity-mode amplitude. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_vortRe_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:148`).

**Theorem: A real component fits the mode amplitude.** The real or imaginary vorticity-vector norm is at most the full vorticity-mode amplitude. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_vortIm_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:153`).

**Theorem: Expansion in the coordinate basis.** A vector is the sum of its coordinates times the corresponding unit vectors. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.vec_expand` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:158`).

**Theorem: Operator norm from column squares.** The operator norm is at most the square root of the sum of squared coordinate-column norms. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.opNorm_le_cols` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:162`).

**Theorem: A mode derivative fits its amplitude.** The derivative norm of the real or imaginary vorticity mode is bounded by the full vorticity-gradient amplitude. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_fderiv_vortRe_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:180`).

**Theorem: A mode derivative fits its amplitude.** The derivative norm of the real or imaginary vorticity mode is bounded by the full vorticity-gradient amplitude. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_fderiv_vortIm_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:186`).

**Theorem: A mode Laplacian fits its amplitude.** The real or imaginary vorticity-mode Laplacian norm is at most the full vorticity-Laplacian amplitude. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_sspOf_vortRe_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:192`).

**Theorem: A mode Laplacian fits its amplitude.** The real or imaginary vorticity-mode Laplacian norm is at most the full vorticity-Laplacian amplitude. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_sspOf_vortIm_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:202`).

**Theorem: Alternating symbol bound.** The alternating symbol has absolute value at most one. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.abs_alternatingSymbol_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:212`).

**Theorem: An alternating coefficient costs no norm.** The norm of the alternating-symbol weighted coordinate is at most the sum of all coordinate norms. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_symbol_mul_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:215`).

**Theorem: Bound complex curl coordinates.** A complex curl coordinate is bounded by nine times the sum of the input gradient-entry norms. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_curlOfGrad_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:221`).

**Theorem: Bound complex curl-gradient entries.** A complex curl-gradient entry is bounded by nine times the sum of the second derivative entry norms. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.norm_curlGradOfSecondDeriv_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:231`).

**Theorem: A finite coordinate norm bound.** A complex-vector norm is at most the square root of the number of coordinates times the common coordinate bound. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.sqrt_cnormSq_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:242`).

**Theorem: Vorticity mode amplitude is in L2.** Under the stated hypotheses, the vorticity mode amplitude belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.memLp_vortAmp` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:250`).

**Theorem: Vorticity-gradient amplitude is in L2.** Under the stated hypotheses, the vorticity-gradient mode amplitude belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.memLp_vortGradAmp` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:267`).

**Theorem: Laplacian amplitude from real parts.** The vorticity-Laplacian amplitude is the square root of the two real and imaginary Laplacian-vector squares. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.sspAmp_eq` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:287`).

**Theorem: Vorticity-Laplacian amplitude is in L2.** Under the stated hypotheses, the vorticity-Laplacian mode amplitude belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.memLp_sspAmp` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:296`).

**Theorem: Integrable curl-amplitude product.** The product of the vorticity-gradient mode amplitude and vorticity-mode amplitude is spatially integrable. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.integrable_amp_pair` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:313`).

**Theorem: Integrable mixed gradient products.** The sum of the two products pairing a real or imaginary vorticity-mode gradient norm with the opposite field norm is spatially integrable. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.integrable_grad_pair` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:318`).

**Theorem: Integrable mixed diffusion products.** The sum of the two products pairing a real or imaginary vorticity-mode Laplacian norm with the opposite field norm is spatially integrable. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.integrable_ssp_pair` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:334`).

**Theorem: Weighted curl diffusion lower bound.** The curl-mode pairing with the negative Laplacian is bounded below by minus the integral of the weight-gradient norm times the two vorticity amplitudes. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartials.mode_lower` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsModes.lean:351`).

### Breakdown.Cert.CoerciveSmoothEpsSumSecondPartialsSquare

Establishes slice regularity and spatial square integrability of the gradient and second-derivative modes used in diffusion control.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Theorem: The mode average belongs to L2.** Under the stated hypotheses, the time-angular mode average belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.memLp_modeAverage_dom` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:19`).

**Theorem: A gradient-mode entry belongs to L2.** Each stated gradient-mode entry belongs to spatial $L^2$ on the chosen time slice. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.memLp_modeGrad_entry` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:27`).

**Theorem: A Hessian-mode entry belongs to L2.** Each stated second-derivative-mode entry belongs to spatial $L^2$ on the chosen time slice. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.memLp_modeSecondDeriv_entry` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:48`).

**Theorem: C4 regularity of function v.** Under the stated hypotheses, the function $v$ has continuous derivatives through order $4$. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.contDiff_four` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:72`).

**Theorem: C3 regularity of derivative.** Under the stated hypotheses, the spatial derivative has continuous derivatives through order $3$. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.contDiff_grad` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:76`).

**Theorem: C2 regularity of second derivative.** Under the stated hypotheses, the spatial second derivative has continuous derivatives through order $2$. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.contDiff_secondDeriv` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:81`).

**Definition: The second derivative trace map.** The trace map adds the second derivative values along the three coordinate axes. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.traceMap` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:86`).

**Theorem: Evaluate the trace map.** The trace map is the sum of the three diagonal second derivative values. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.traceMap_apply` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:90`).

**Theorem: Trace map norm at most three.** The operator norm of the second derivative trace map is at most three. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.norm_traceMap_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:93`).

**Theorem: The negative Laplacian through its trace.** The negative Laplacian field is the negative continuous trace-map value of the spatial Hessian. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.ssp_eq` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:103`).

**Definition: The negative spatial Laplacian.** This field is the negative trace of the spatial second derivative. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.sspAt` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:108`).

**Theorem: The negative Laplacian field is C2.** Under the stated hypotheses, the negative Laplacian field has continuous derivatives through order $2$. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.contDiff_ssp` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:110`).

**Theorem: C3 regularity of derivative.** Under the stated hypotheses, the spatial derivative has continuous derivatives through order $3$. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.slice_grad` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:119`).

**Theorem: Domination gives a finite integral.** The supplied pointwise domination by a finite nonnegative period integral makes the displayed period integral finite. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.periodLIntegral_lt_top_of_le` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:123`).

**Theorem: A perturbation gradient mode is L2.** Each entry of the perturbation's gradient mode belongs to spatial $L^2$ on the chosen time slice. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.memLp_grad_entry` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:135`).

**Theorem: A perturbation Hessian mode is L2.** Each entry of the perturbation's second-derivative mode belongs to spatial $L^2$ on the chosen time slice. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.memLp_secondDeriv_entry` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:147`).

**Theorem: A diffusion gradient-mode entry is L2.** Each entry of the negative Laplacian field's gradient mode belongs to spatial $L^2$ on the chosen time slice. Source: `Breakdown.Coercive.Internal.SmoothEpsSumSecondPartialsSquare.memLp_sspGrad_entry` (`Breakdown/Cert/CoerciveSmoothEpsSumSecondPartialsSquare.lean:159`).

### Breakdown.Cert.CoerciveSmoothEpsSummable

Uses mode square sums to prove summability of the integrated curl pairing.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: The gradient-mode energies are summable.** The series of integrated gradient-mode squared norms on the period slab is summable. Source: `Breakdown.Coercive.SmoothEpsInternal.summable_integral_cnormSq_modeGrad` (`Breakdown/Cert/CoerciveSmoothEpsSummable.lean:16`).

**Theorem: Integrated curl-mode pairing is summable.** Under the stated hypotheses, the integrated curl-mode pairing is summable over the indicated index. Source: `Breakdown.Coercive.SmoothEpsInternal.summable_epsModeTerm` (`Breakdown/Cert/CoerciveSmoothEpsSummable.lean:31`).

### Breakdown.Cert.CoerciveSmoothEpsTail

Bounds the infinite curl-remainder sum by finite vorticity, gradient and radially weighted velocity energies.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Definition: Nonnegative remainder energy.** The extended-nonnegative remainder energy adds squared vorticity, vorticity gradient, gradient and inverse-radius weighted velocity amplitudes. Source: `Breakdown.Coercive.SmoothEpsInternal.restAmp` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:16`).

**Definition: Real remainder energy.** The real remainder energy adds squared vorticity, vorticity gradient, gradient and inverse-radius weighted velocity amplitudes. Source: `Breakdown.Coercive.SmoothEpsInternal.restSq` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:20`).

**Theorem: Nonnegativity of real remainder energy.** The real remainder energy is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.SmoothEpsInternal.restSq_nonneg` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:24`).

**Theorem: Real and nonnegative remainder energies.** The extended-nonnegative remainder energy is the nonnegative embedding of the real remainder energy. Source: `Breakdown.Coercive.SmoothEpsInternal.restAmp_eq` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:28`).

**Theorem: A uniform bound for the mean field.** The mean model-field norm is at most nine times the stated model bound. Source: `Breakdown.Coercive.SmoothEpsInternal.norm_meanField_le` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:34`).

**Theorem: Uniform bounds for mean vorticity.** Mean vorticity and its spatial derivative admit one common finite uniform bound. Source: `Breakdown.Coercive.SmoothEpsInternal.meanField_deriv_bounds` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:60`).

**Theorem: Uniform bounds for the mean jet.** The mean model field, its vorticity and its vorticity gradient admit one common finite uniform bound. Source: `Breakdown.Coercive.SmoothEpsInternal.meanField_bounds` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:68`).

**Theorem: Bound the axial rotation generator.** The norm of the axial rotation generator is at most twice the spatial norm. Source: `Breakdown.Coercive.SmoothEpsInternal.norm_axialGen_le` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:84`).

**Theorem: Bound the relative mean velocity.** The relative mean speed is at most the mean-field norm plus radial-expansion speed and the stated rotational speed. Source: `Breakdown.Coercive.SmoothEpsInternal.norm_relativeVelocity_le` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:90`).

**Theorem: Uniform curl-remainder factor bounds.** All listed mean-flow and model-wave coefficients in the curl remainder admit one common finite bound after the indicated radial weights. Source: `Breakdown.Coercive.SmoothEpsInternal.restCoeff_bounded` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:101`).

**Theorem: Absorb a product into two squares.** The stated bounded coefficient times a product is controlled by the common bound times the sum of the two squares. Source: `Breakdown.Coercive.SmoothEpsInternal.prod_le_sq` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:197`).

**Theorem: Insert a reciprocal scaling factor.** The displayed product can be regrouped by inserting a nonzero scale and its reciprocal. Source: `Breakdown.Coercive.SmoothEpsInternal.regroup` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:207`).

**Theorem: Control the full curl-mode remainder.** The negative curl remainder is bounded by a finite constant times the same-mode and model-wave-shifted remainder energies. Source: `Breakdown.Coercive.SmoothEpsInternal.negRest_le_restAmp` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:211`).

**Theorem: Reindex shifted remainder energies.** Summing the same-mode and finitely shifted remainder energies multiplies the full mode sum by one plus the number of shifts. Source: `Breakdown.Coercive.SmoothEpsInternal.tsum_restAmp_shift` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:318`).

**Theorem: Split the four remainder-energy series.** The full remainder-energy mode sum equals the separate vorticity, vorticity-gradient, gradient and weighted-velocity mode sums. Source: `Breakdown.Coercive.SmoothEpsInternal.tsum_restAmp_eq` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:328`).

**Theorem: Finite total curl-remainder loss.** The period integral of the mode sum of the nonnegative negative curl remainders is finite. Source: `Breakdown.Coercive.SmoothEpsInternal.lintegral_negRest_lt_top` (`Breakdown/Cert/CoerciveSmoothEpsTail.lean:337`).

### Breakdown.Cert.CoerciveSmoothEpsTailDeriv

Extracts concrete derivative and curl-amplitude bounds from the model decay assumptions to control the curl remainder.

**Paper context:** Appendix B, Proposition B.1: the curl-weighted skew multiplier and its modewise frequency and error terms.

**Theorem: Alternating symbol bound.** The alternating symbol has absolute value at most one. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.alternatingSymbol_abs_le` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:15`).

**Theorem: Curl from a common entry bound.** A common bound on the gradient entries bounds the curl norm by twenty-seven times that bound. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.norm_curlVec_le` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:18`).

**Theorem: Recover the spatial slice derivative.** The spatial derivative is the joint spacetime derivative composed with the spatial inclusion map. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.slice_fderiv_eq` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:49`).

**Theorem: Continuity of derivative.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.slice_fderiv_continuous` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:56`).

**Theorem: The rotated gradient entry is continuous.** The pulled-back gradient entry varies continuously over the time-angle parameters. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.gradIntegrand_continuous` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:66`).

**Theorem: A Lipschitz bound for the model gradient.** The model gradient's difference at two spatial points is bounded by the model Hessian bound times their distance. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.slice_fderiv_sub_le` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:78`).

**Theorem: Mean-gradient entries are Lipschitz.** Each mean-gradient entry changes by at most the stated constant times the spatial distance. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.meanField_fderiv_entry_sub` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:87`).

**Theorem: Uniform bounds for mean vorticity.** Mean vorticity and its spatial derivative admit one common finite uniform bound. Source: `Breakdown.Coercive.Internal.SmoothEpsTailDeriv.meanField_curl_bounds` (`Breakdown/Cert/CoerciveSmoothEpsTailDeriv.lean:110`).

### Breakdown.Cert.CoerciveSmoothIsPerturbation

Shows that the smooth perturbation class satisfies the weak perturbation requirements by verifying derivatives, norms and integration-by-parts relations.

**Paper context:** Appendix B, Proposition B.1: approximation that extends the smooth coercive calculation to the perturbation domain.

**Definition: A field as a spacetime function.** The joint version evaluates a time-dependent field at the time and space coordinates of one pair. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.joint` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:14`).

**Theorem: Unbounded differentiability order.** Adding one to the displayed infinite differentiability order leaves it below the same infinite order. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.top_add_one_le` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:16`).

**Theorem: Spatial slices inherit regularity.** Each fixed-time spatial slice has the stated order of continuous differentiability. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.slice_contDiff` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:19`).

**Theorem: Time slices inherit regularity.** At each fixed spatial point, the time-dependent field has the stated order of continuous differentiability. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.line_contDiff` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:23`).

**Theorem: Spatial derivative from the joint field.** The spatial derivative is the joint Fréchet derivative restricted to spatial directions. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.fderiv_slice` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:27`).

**Theorem: Time derivative from the joint field.** The time derivative equals the joint Fréchet derivative applied to the unit time direction. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.deriv_line` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:39`).

**Theorem: Smoothness of derivative.** Under the stated hypotheses, the spatial derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.grad_contDiff` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:47`).

**Theorem: Smoothness of second derivative.** Under the stated hypotheses, the spatial second derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.secondDeriv_contDiff` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:53`).

**Theorem: Smoothness of time derivative.** Under the stated hypotheses, the time derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.time_contDiff` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:60`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.matSq_le` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:67`).

**Theorem: Squared trace bound.** The squared norm of the second derivative trace is at most nine times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.trace_sq_le` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:79`).

**Theorem: Integrate a pointwise scaled bound.** The stated pointwise bound passes to a period-integral bound with the nonnegative coefficient outside the integral. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.periodLIntegral_le_mul` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:98`).

**Theorem: Domination gives a finite integral.** The supplied pointwise domination by a finite nonnegative period integral makes the displayed period integral finite. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.periodLIntegral_lt_top` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:109`).

**Theorem: A classical gradient is a weak gradient.** The classical Fréchet derivative of the continuously differentiable field satisfies the weak-gradient identity. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.isWeakGradient_of_contDiff` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:113`).

**Theorem: Pair two square-integrable fields.** The inner product of the two square-integrable fields is integrable on the displayed measure space. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.inner_integrable` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:138`).

**Theorem: The weak integration identity vanishes.** The displayed sum of derivative pairings is integrable and has integral zero. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.ibp_zero` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:148`).

**Theorem: Expand a spatial spacetime direction.** A zero-time spacetime vector is the coordinate sum of the spatial basis directions. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.zero_prod_eq_sum` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:171`).

**Theorem: Expand the radial derivative.** The derivative in the radial spatial direction is the coordinate-weighted sum of the joint spatial coordinate derivatives. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.fderiv_slice_self` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:180`).

**Definition: A spatial coordinate functional.** The coordinate map extracts one spatial coordinate from a spacetime pair. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.coord` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:185`).

**Theorem: Read a spatial coordinate from spacetime.** The spatial coordinate functional returns the indicated spatial coordinate of the spacetime pair. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.coord_apply` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:188`).

**Theorem: The weak similarity-transport identity.** The smooth transport field satisfies the displayed integration-by-parts identity against compactly supported spacetime test fields. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.transport_identity` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:191`).

**Theorem: Continuity of similarity transport field.** Under the stated hypotheses, the similarity transport field is continuous. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.transport_continuous` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:270`).

**Theorem: Time derivatives preserve periodicity.** The time derivative of the one-periodic field has equal values at times separated by one. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.deriv_periodic` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:278`).

**Theorem: The second derivative norm.** The iterated second derivative and the displayed second Fréchet derivative have the same norm. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.norm_secondDeriv_eq` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:285`).

**Theorem: Second derivatives as weak gradients.** A gradient column has the corresponding flipped second derivative as its weak gradient. Source: `Breakdown.Coercive.Internal.SmoothIsPerturbation.secondDeriv_weak` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:289`).

**Theorem: Smooth perturbations are weak ones.** The smooth perturbation conditions imply the required weak derivatives, transport identity and integrability conditions. Source: `Breakdown.Coercive.smoothPerturbationIsPerturbationHolds_proof` (`Breakdown/Cert/CoerciveSmoothIsPerturbation.lean:306`).

### Breakdown.Cert.CoerciveSmoothMu

Combines velocity transport and pressure bounds into the smooth velocity-weight inequality.

**Paper context:** Appendix B, Proposition B.1: the velocity-weighted skew multiplier, frequency seminorm and remainder estimates.

**Theorem: The integrated velocity transport bound.** The velocity-frequency term is controlled by the signed inner-field pairing plus the integrated transport loss. Source: `Breakdown.Coercive.Internal.MuSmooth.transport_bound` (`Breakdown/Cert/CoerciveSmoothMu.lean:15`).

**Theorem: The velocity loss is measurable.** The nonnegative embedding of the negative velocity-mode remainder is a measurable spacetime function. Source: `Breakdown.Coercive.Internal.MuSmooth.rest_measurable_of` (`Breakdown/Cert/CoerciveSmoothMu.lean:29`).

**Theorem: Transport and pressure split the loss.** The negative velocity remainder splits into its transport and pressure losses, with the displayed integration when applicable. Source: `Breakdown.Coercive.Internal.MuSmooth.restMode_split` (`Breakdown/Cert/CoerciveSmoothMu.lean:36`).

**Theorem: Add pressure to the transport bound.** The transport lower bound and the pressure estimate give the displayed full velocity-mode inequality. Source: `Breakdown.Coercive.Internal.MuSmooth.mode_bound_of` (`Breakdown/Cert/CoerciveSmoothMu.lean:56`).

**Theorem: The smooth velocity-mode estimate.** The transport, pressure and summability bounds supply the smooth velocity-weight estimate. Source: `Breakdown.Coercive.modeMuEstimateSmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothMu.lean:94`).

### Breakdown.Cert.CoerciveSmoothMuDecay

Turns model-field decay into bounds for mean velocity, mean gradient and velocity-mode interactions.

**Paper context:** Appendix B, Proposition B.1: the velocity-weighted skew multiplier, frequency seminorm and remainder estimates.

**Theorem: A coordinate is bounded by the norm.** The absolute value of each real coordinate is at most the vector norm. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.coord_abs_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:16`).

**Theorem: Axial rotation preserves the norm.** Axial rotation preserves the Euclidean norm. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.rot_norm` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:22`).

**Theorem: A mode average obeys the uniform bound.** The norm of the normalised mode average is at most the supplied uniform bound on its real integrand. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.modeAverage_norm_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:26`).

**Theorem: Bound a velocity mode from coordinates.** The squared norm of a velocity mode is at most three times the square of the supplied coordinate bound. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.cnormSq_modeVel_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:54`).

**Theorem: Bound a gradient mode from entries.** The squared norm of a gradient mode is at most nine times the square of the supplied entry bound. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.cnormSq_modeGrad_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:66`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.unit_norm` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:84`).

**Theorem: Axial rotation preserves differences.** Axial rotation maps a vector difference to the difference of the rotated vectors. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.rot_sub` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:88`).

**Theorem: Mode averages preserve subtraction.** The mode average of a difference is the difference of the mode averages. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.modeAverage_sub` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:92`).

**Theorem: The mean model field inherits decay.** The mean model-field norm is at most three times the model decay bound divided by one plus the radius. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.meanField_norm_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:123`).

**Theorem: The model slice is differentiable.** The stated joint regularity of the model field implies spatial differentiability on each time slice. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.slice_differentiable` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:140`).

**Theorem: A local difference bound for the model.** The model field changes by at most the stated inverse-square radial coefficient times the spatial displacement. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.flow_sub_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:144`).

**Theorem: Continuity of rotated field or vector.** Under the stated hypotheses, the rotated field or vector is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.rot_continuous` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:163`).

**Theorem: The orbit entry is continuous.** The indicated coordinate of the time-shifted and pulled-back field is continuous in the time-angle parameters. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.integrand_continuous` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:168`).

**Theorem: Decay of the mean-model gradient.** The mean-model gradient norm is at most twelve times the model decay constant divided by $(1+|y|)^2$. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.meanField_fderiv_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:175`).

**Theorem: Indicator bounded by one.** A zero-one indicator is at most one. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.ind_le_one` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:206`).

**Theorem: Absorb a weighted product into energy.** The displayed coefficient-weighted product is bounded by the stated sum of gradient and inverse-radius velocity squares. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.prod_le_energy` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:210`).

**Theorem: Absorb a weighted velocity square.** The stated coefficient bound controls the velocity-square contribution by its inverse-radius weighted energy. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.sq_le_energy` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:224`).

**Theorem: Square of a finite sum.** The square of a finite sum is bounded by the number of terms times the sum of their squares. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.sum_sq_le_card` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:230`).

**Theorem: Bound the mean pressure charge.** The mean-gradient pressure term is bounded by the stated $144D^2/\eta_{\min}$ multiple of the comparison energy. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.press_mean_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:235`).

**Theorem: Bound the wave pressure charge.** The finite-wave pressure term is bounded by the stated gradient-decay, mode-count and positive-$\eta$ energy bound. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.press_wave_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:255`).

**Theorem: Bound the weighted pressure square.** The weighted pressure-square contribution is controlled by the stated uniform coefficient times the comparison energy. Source: `Breakdown.Coercive.Internal.MuSmooth.Decay.press_weight_le` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:285`).

**Definition: Energy for a velocity-mode remainder.** The mode energy is the squared gradient amplitude plus the squared inverse-radius weighted velocity amplitude. Source: `Breakdown.Coercive.Internal.MuSmooth.modeEnergy` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:311`).

**Theorem: Dominate the velocity-mode remainder.** One finite coefficient bounds the combined transport and pressure loss by the same-mode and finite-wave-shifted gradient and weighted-velocity energies. Source: `Breakdown.Coercive.Internal.MuSmooth.rest_pointwise` (`Breakdown/Cert/CoerciveSmoothMuDecay.lean:314`).

### Breakdown.Cert.CoerciveSmoothMuGlue

Defines the frequency and loss densities and assembles their signed velocity-mode inequalities.

**Paper context:** Appendix B, Proposition B.1: the velocity-weighted skew multiplier, frequency seminorm and remainder estimates.

**Definition: One velocity-weight pairing density.** The pairing density is the real part of the imaginary velocity weight times the complex pairing of the two velocity modes. Source: `Breakdown.Coercive.Internal.MuSmooth.pairTerm` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:14`).

**Definition: One integrated velocity-mode term.** The velocity-mode pairing integrates its density over space and one time period. Source: `Breakdown.Coercive.Internal.MuSmooth.pairMode` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:17`).

**Definition: Velocity-frequency density.** The density multiplies the velocity weight, the absolute rotating-frame frequency and the squared velocity-mode norm. Source: `Breakdown.Coercive.Internal.MuSmooth.dopDensity` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:20`).

**Definition: Integrated velocity-frequency density.** The extended-nonnegative mode value integrates the velocity-frequency density over space and one period. Source: `Breakdown.Coercive.Internal.MuSmooth.dopMode` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:24`).

**Definition: Integrated negative velocity remainder.** The remainder mode integrates the nonnegative magnitude of the negative velocity remainder over space and one period. Source: `Breakdown.Coercive.Internal.MuSmooth.restMode` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:27`).

**Theorem: A complex square sum is nonnegative.** The sum of squared complex coordinate norms is nonnegative. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm_nonneg` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:30`).

**Theorem: A negative sum of positive terms.** The displayed negative sum is nonpositive when its component quantities satisfy the stated sign assumptions. Source: `Breakdown.Coercive.Internal.MuSmooth.nonpos_combo` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:33`).

**Theorem: Nonnegative indicator.** A zero-one indicator is nonnegative. Source: `Breakdown.Coercive.Internal.MuSmooth.ind_nonneg` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:37`).

**Theorem: Nonpositivity of velocity remainder.** The velocity-mode remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.Internal.MuSmooth.rest_nonpos` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:41`).

**Theorem: The positive velocity density.** The positive velocity-mode density equals one minus the reserved coefficient times its nonnegative frequency density. Source: `Breakdown.Coercive.Internal.MuSmooth.pos_eq` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:60`).

**Theorem: Nonnegative velocity-frequency density.** The velocity-frequency density is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.MuSmooth.dopDensity_nonneg` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:66`).

**Theorem: Exchange the mode sum and integral.** Under the stated measurability assumptions, the nonnegative sum over modes can be interchanged with integration over one time period and space. Source: `Breakdown.Coercive.Internal.MuSmooth.swap_sum` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:71`).

**Theorem: Recover a finite real lower bound.** The signed extended-nonnegative inequality proves finiteness of the left quantity and the displayed bound for its real value. Source: `Breakdown.Coercive.Internal.MuSmooth.toReal_le_of` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:78`).

**Theorem: Turn a real bound into a sign split.** The stated real inequality gives the corresponding extended-nonnegative inequality after positive and negative parts are separated. Source: `Breakdown.Coercive.Internal.MuSmooth.ennreal_bound` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:94`).

**Theorem: Assemble modewise lower bounds.** The stated summability and per-mode bounds combine into the split lower-bound predicate for the full mode sum. Source: `Breakdown.Coercive.Internal.MuSmooth.split_of_modes` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:102`).

**Definition: Transport, diffusion and advection.** The inner field combines similarity transport, the negative Laplacian and advection of the perturbation by the model field. Source: `Breakdown.Coercive.Internal.MuSmooth.innerPart` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:161`).

**Definition: Velocity transport error charge.** The transport loss collects the relative-flow, weight-gradient, rotation and off-mode advection bounds. Source: `Breakdown.Coercive.Internal.MuSmooth.transportLoss` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:164`).

**Definition: Velocity pressure error charge.** The pressure loss balances the model-gradient coupling against the weighted velocity square using the positive parameter $\eta$. Source: `Breakdown.Coercive.Internal.MuSmooth.pressureLoss` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:171`).

**Theorem: Transport and pressure split the loss.** The negative velocity remainder splits into its transport and pressure losses, with the displayed integration when applicable. Source: `Breakdown.Coercive.Internal.MuSmooth.neg_rest_eq` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:178`).

**Theorem: Nonnegativity of transport loss.** The transport loss is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.MuSmooth.transportLoss_nonneg` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:184`).

**Theorem: Nonnegativity of pressure loss.** The pressure loss is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.MuSmooth.pressureLoss_nonneg` (`Breakdown/Cert/CoerciveSmoothMuGlue.lean:198`).

### Breakdown.Cert.CoerciveSmoothMuMeasure

Proves continuity of velocity and gradient modes and measurability of the resulting frequency densities.

**Paper context:** Appendix B, Proposition B.1: the velocity-weighted skew multiplier, frequency seminorm and remainder estimates.

**Theorem: Fourier averaging preserves continuity.** The normalised time-angle Fourier integral depends continuously on the external parameter under the stated hypotheses. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_average` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:16`).

**Theorem: Continuity of velocity mode.** Under the stated hypotheses, the velocity mode is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_modeVel` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:37`).

**Theorem: Continuity of gradient mode.** Under the stated hypotheses, the gradient mode is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_modeGrad` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:52`).

**Theorem: Continuity of velocity mode amplitude.** Under the stated hypotheses, the velocity mode amplitude is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_velAmp` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:72`).

**Theorem: Continuity of gradient mode amplitude.** Under the stated hypotheses, the gradient mode amplitude is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_gradAmp` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:77`).

**Theorem: Continuity of velocity mode square.** Under the stated hypotheses, the squared complex norm of the velocity mode is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_cnormSq_modeVel` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:83`).

**Theorem: Continuity of mean model field.** Under the stated hypotheses, the mean model field is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.meanField_continuous` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:89`).

**Theorem: Relative velocity is measurable.** Under the stated hypotheses, the mean velocity relative to the moving frame is measurable. Source: `Breakdown.Coercive.Internal.MuSmooth.relativeVelocity_measurable` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:95`).

**Theorem: Velocity-frequency density is measurable.** Under the stated hypotheses, the velocity-frequency density is measurable. Source: `Breakdown.Coercive.Internal.MuSmooth.dop_measurable_of` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:109`).

**Theorem: The two velocity losses are measurable.** The transport loss and pressure loss are measurable spacetime functions under the stated assumptions. Source: `Breakdown.Coercive.Internal.MuSmooth.loss_measurable_of` (`Breakdown/Cert/CoerciveSmoothMuMeasure.lean:124`).

### Breakdown.Cert.CoerciveSmoothMuModeCalc

Computes the Fourier effects of time differentiation and angular transport, including the component-rotation correction.

**Paper context:** Appendix B, (B.15) and Proposition B.1: rotating-frame frequencies and the finite frequency seminorm.

**Definition: The axial rotation generator.** The rotation generator sends the first two coordinates to their quarter turn and sets the axial coordinate to zero. Source: `Breakdown.Coercive.Internal.ModeCalc.rotZ` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:15`).

**Definition: The time derivative field.** The time-derivative field differentiates the velocity with respect to its time variable. Source: `Breakdown.Coercive.Internal.ModeCalc.timeField` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:17`).

**Definition: The angular derivative field.** The angular derivative field differentiates the velocity along the axial rotation generator. Source: `Breakdown.Coercive.Internal.ModeCalc.azimField` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:19`).

**Theorem: First coordinate of axial rotation.** The first rotated coordinate is the cosine times the first coordinate minus the sine times the second. Source: `Breakdown.Coercive.Internal.ModeCalc.rot_zero` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:22`).

**Theorem: Second coordinate of axial rotation.** The second rotated coordinate is the sine times the first coordinate plus the cosine times the second. Source: `Breakdown.Coercive.Internal.ModeCalc.rot_one` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:25`).

**Theorem: Axial rotation fixes height.** Axial rotation leaves the third coordinate unchanged. Source: `Breakdown.Coercive.Internal.ModeCalc.rot_two` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:28`).

**Definition: One rotated coordinate functional.** This linear functional returns one coordinate after applying the axial rotation. Source: `Breakdown.Coercive.Internal.ModeCalc.rotCoord` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:31`).

**Theorem: Evaluate a rotated coordinate.** The rotated-coordinate linear functional returns the indicated coordinate after axial rotation. Source: `Breakdown.Coercive.Internal.ModeCalc.rotCoord_apply` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:37`).

**Theorem: Exchange time and angle integration.** The displayed continuous complex integrand has equal iterated integrals in the two orders over the bounded rectangle. Source: `Breakdown.Coercive.Internal.ModeCalc.box_swap` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:39`).

**Theorem: Differentiate a Fourier phase.** Differentiating the displayed complex exponential multiplies it by the negative imaginary phase frequency. Source: `Breakdown.Coercive.Internal.ModeCalc.exp_hasDerivAt` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:50`).

**Theorem: Differentiate a shifted rotated field.** The derivative in the time-shift parameter is the same rotated coordinate of the time-derivative field. Source: `Breakdown.Coercive.Internal.ModeCalc.time_hasDerivAt` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:60`).

**Theorem: Integration by parts for a phase.** Under the matched endpoint conditions, the phase-weighted derivative integral is the imaginary frequency times the phase-weighted field integral. Source: `Breakdown.Coercive.Internal.ModeCalc.tau_ibp` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:70`).

**Theorem: Time integration by parts in a mode.** Periodic integration by parts turns a time derivative inside the mode average into multiplication by its imaginary temporal frequency. Source: `Breakdown.Coercive.Internal.ModeCalc.modeAverage_tau_ibp` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:81`).

**Theorem: Time differentiation multiplies a mode.** The mode of the time derivative is the original mode multiplied by the imaginary temporal frequency. Source: `Breakdown.Coercive.Internal.ModeCalc.time_mode` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:122`).

**Theorem: Differentiate a Fourier phase.** Differentiating the displayed complex exponential multiplies it by the negative imaginary phase frequency. Source: `Breakdown.Coercive.Internal.ModeCalc.exp_hasDerivAt'` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:147`).

**Theorem: Angular integration by parts in a mode.** Periodic angular integration by parts turns an angular derivative into multiplication by the imaginary angular frequency. Source: `Breakdown.Coercive.Internal.ModeCalc.modeAverage_phi_ibp` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:157`).

**Theorem: Differentiate the rotation angle.** The angular derivative of a rotated vector is the axial rotation generator applied to that rotated vector. Source: `Breakdown.Coercive.Internal.ModeCalc.rot_hasDerivAt` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:193`).

**Theorem: Differentiate a field along a rotation.** Differentiating the field along the angular orbit gives its derivative in the axial rotation direction. Source: `Breakdown.Coercive.Internal.ModeCalc.field_hasDerivAt` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:208`).

**Theorem: Differentiate one coordinate.** The derivative of a coordinate of a differentiable vector curve is the corresponding coordinate of its derivative. Source: `Breakdown.Coercive.Internal.ModeCalc.coord_hasDerivAt` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:215`).

**Theorem: Differentiate the first orbit component.** The angular derivative of the first pulled-back field component adds the second component to the pulled-back angular derivative. Source: `Breakdown.Coercive.Internal.ModeCalc.azim_deriv0` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:219`).

**Theorem: Differentiate the second orbit component.** The angular derivative of the second pulled-back field component subtracts the first component from the pulled-back angular derivative. Source: `Breakdown.Coercive.Internal.ModeCalc.azim_deriv1` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:236`).

**Theorem: Differentiate the axial component.** The angular derivative of the pulled-back axial component is the pulled-back angular derivative, without a component-rotation term. Source: `Breakdown.Coercive.Internal.ModeCalc.azim_deriv2` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:252`).

**Theorem: Equal integrands have equal modes.** The two mode averages agree when their indicated scalar integrands agree pointwise. Source: `Breakdown.Coercive.Internal.ModeCalc.modeAverage_congr_point` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:266`).

**Theorem: A rotating-coordinate mode identity.** The angular derivative mode is its imaginary angular frequency term minus the displayed coordinate-rotation correction. Source: `Breakdown.Coercive.Internal.ModeCalc.mode_shift_coord` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:271`).

**Theorem: A full rotation is the identity.** Axial rotation through the displayed positive or negative full turn fixes every vector. Source: `Breakdown.Coercive.Internal.ModeCalc.rot_period` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:291`).

**Theorem: A full rotation is the identity.** Axial rotation through the displayed positive or negative full turn fixes every vector. Source: `Breakdown.Coercive.Internal.ModeCalc.rot_neg_period` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:295`).

**Theorem: Zero-angle rotation.** Axial rotation through zero fixes every vector. Source: `Breakdown.Coercive.Internal.ModeCalc.rot_zero_angle` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:299`).

**Theorem: Continuity of angular derivative field.** Under the stated hypotheses, the angular derivative field is continuous. Source: `Breakdown.Coercive.Internal.ModeCalc.azimField_continuous` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:303`).

**Theorem: Angular differentiation of vector modes.** The angular derivative mode equals imaginary angular frequency times the velocity mode plus the rotation-generator correction. Source: `Breakdown.Coercive.Internal.ModeCalc.azim_mode` (`Breakdown/Cert/CoerciveSmoothMuModeCalc.lean:312`).

### Breakdown.Cert.CoerciveSmoothMuPress

Controls the pressure contribution through an eta-balanced reflected-field pairing.

**Paper context:** Appendix B, Proposition B.1: the Leray-projected velocity pairing and control of its pressure correction.

**Theorem: Bound the integral of a mode pairing.** The nonnegative absolute integrated mode pairing is at most the integral of its absolute pairing density. Source: `Breakdown.Coercive.Internal.MuSmooth.ofReal_abs_pairMode_le` (`Breakdown/Cert/CoerciveSmoothMuPress.lean:15`).

**Theorem: Separate a constant-weighted integral.** The nonnegative integral of the displayed sum equals the first integral plus the constant times the second integral. Source: `Breakdown.Coercive.Internal.MuSmooth.split_const` (`Breakdown/Cert/CoerciveSmoothMuPress.lean:24`).

**Theorem: Balance a pairing with eta.** The weighted imaginary pairing is bounded by the displayed pair of squared norms weighted by $\eta$ and its reciprocal. Source: `Breakdown.Coercive.Internal.MuSmooth.weighted_product_term` (`Breakdown/Cert/CoerciveSmoothMuPress.lean:35`).

**Theorem: Control the reflected pressure pairing.** The negative pairing with the reflected model-gradient field is bounded by the integrated pressure loss. Source: `Breakdown.Coercive.Internal.MuSmooth.pressure_bound_of` (`Breakdown/Cert/CoerciveSmoothMuPress.lean:51`).

### Breakdown.Cert.CoerciveSmoothMuRest

Bounds the total negative velocity remainder by finite gradient and inverse-radius velocity mode energies.

**Paper context:** Appendix B, Proposition B.1: the velocity-weighted skew multiplier, frequency seminorm and remainder estimates.

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.Internal.MuSmooth.unitVector_norm` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:15`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.MuSmooth.matSq_le` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:19`).

**Theorem: Continuity of gradient mode square.** Under the stated hypotheses, the squared complex norm of the gradient mode is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_cnormSq_modeGrad` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:28`).

**Theorem: The comparison mode energy is measurable.** Under the stated hypotheses, the gradient and weighted-velocity mode energy is measurable. Source: `Breakdown.Coercive.Internal.MuSmooth.energy_measurable` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:34`).

**Theorem: Measurable slice comparison energy.** Under the stated hypotheses, the gradient and weighted-velocity mode energy is measurable. Source: `Breakdown.Coercive.Internal.MuSmooth.energy_slice_measurable` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:42`).

**Theorem: The spatial mode energy is measurable.** The nonnegative spatial integral of the gradient and inverse-radius velocity mode energy is a measurable function of time. Source: `Breakdown.Coercive.Internal.MuSmooth.energy_outer_measurable` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:48`).

**Theorem: Finite total comparison mode energy.** The sum of the modewise period integrals of gradient and inverse-radius velocity energy is finite. Source: `Breakdown.Coercive.Internal.MuSmooth.energy_tsum_lt_top` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:52`).

**Theorem: Finite total velocity-remainder loss.** The series of integrated nonnegative negative velocity remainders is finite. Source: `Breakdown.Coercive.Internal.MuSmooth.rest_finite_of` (`Breakdown/Cert/CoerciveSmoothMuRest.lean:92`).

### Breakdown.Cert.CoerciveSmoothMuSplit

Splits the forcing pairing into the smooth inner-field pairing and the reflected solenoidal correction.

**Paper context:** Appendix B, Proposition B.1: the Leray-projected velocity pairing and control of its pressure correction.

**Theorem: Expand the linearised right-hand side.** The displayed identity separates similarity transport, the negative Laplacian and the two linearised advection contributions, with the indicated subtraction where present. Source: `Breakdown.Coercive.Internal.MuSmooth.innerPart_eq` (`Breakdown/Cert/CoerciveSmoothMuSplit.lean:15`).

**Theorem: The weighted mode pairing is integrable.** The imaginary signed-weight velocity-mode pairing is integrable on the unit spacetime slab. Source: `Breakdown.Coercive.Internal.MuSmooth.term_integrable` (`Breakdown/Cert/CoerciveSmoothMuSplit.lean:20`).

**Theorem: Separate the solenoidal gradient part.** A solenoidal part of the model-gradient term exists and gives the displayed decomposition of each velocity-mode pairing. Source: `Breakdown.Coercive.Internal.MuSmooth.pair_split_of` (`Breakdown/Cert/CoerciveSmoothMuSplit.lean:53`).

### Breakdown.Cert.CoerciveSmoothMuSum

Uses an inverse-radius field rescaling and Parseval to prove summability of the velocity-mode pairings.

**Paper context:** Appendix B, Proposition B.1: the velocity-weighted skew multiplier, frequency seminorm and remainder estimates.

**Theorem: Axial rotation is real linear.** Axial rotation commutes with the displayed real scalar combination. Source: `Breakdown.Coercive.Internal.MuSmooth.axialRot_smul` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:14`).

**Definition: Velocity with inverse radial weight.** The weighted velocity is divided by one plus the spatial norm. Source: `Breakdown.Coercive.Internal.MuSmooth.weighted` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:19`).

**Theorem: A radial weight commutes with modes.** Multiplying the field by the inverse radial weight multiplies its mode coefficient by the same weight. Source: `Breakdown.Coercive.Internal.MuSmooth.modeVel_weighted` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:21`).

**Theorem: Radial scaling of velocity-mode energy.** The squared norm of the radially scaled velocity mode is the original squared mode norm divided by $(1+|y|)^2$. Source: `Breakdown.Coercive.Internal.MuSmooth.cnormSq_weighted` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:35`).

**Theorem: Bound a velocity pairing by squares.** The absolute velocity-mode pairing is bounded by the stated weighted-velocity and partner-mode square energies. Source: `Breakdown.Coercive.Internal.MuSmooth.pairTerm_le` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:45`).

**Theorem: Finite inverse-radius velocity energy.** The velocity divided by one plus the radius has finite squared-norm period integral. Source: `Breakdown.Coercive.Internal.MuSmooth.weighted_square` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:73`).

**Theorem: Continuity of weighted velocity.** Under the stated hypotheses, the weighted velocity is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.weighted_continuous` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:84`).

**Theorem: Time periodicity of weighted velocity.** Under the stated hypotheses, the weighted velocity has period one in time. Source: `Breakdown.Coercive.Internal.MuSmooth.weighted_periodic` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:90`).

**Theorem: Finite total velocity-mode energy.** The sum over all modes of their integrated velocity-mode squared norms is finite. Source: `Breakdown.Coercive.Internal.MuSmooth.tsum_mode_lt_top` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:95`).

**Theorem: Summable velocity-mode pairings.** Under the stated hypotheses, the integrated velocity-mode pairing is summable over the indicated index. Source: `Breakdown.Coercive.Internal.MuSmooth.pair_summable_of` (`Breakdown/Cert/CoerciveSmoothMuSum.lean:102`).

### Breakdown.Cert.CoerciveSmoothMuTransport

Decomposes the rotating-frame velocity equation and bounds the integrated advection and diffusion contributions around its positive frequency term.

**Paper context:** Appendix B, Proposition B.1: the velocity-weighted skew multiplier, frequency seminorm and remainder estimates.

**Definition: Spacetime measure on one period.** The measure is Lebesgue measure restricted to the unit time interval, multiplied by spatial Lebesgue measure. Source: `Breakdown.Coercive.Internal.MuTransport.slabVol` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:19`).

**Definition: The negative spatial Laplacian.** This field is the negative trace of the spatial second derivative. Source: `Breakdown.Coercive.Internal.MuTransport.sumSecondPartialsPart` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:21`).

**Definition: Velocity-weight derivative charge.** The charge multiplies the velocity-weight gradient bound by the gradient and velocity mode amplitudes. Source: `Breakdown.Coercive.Internal.MuTransport.gradLoss` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:23`).

**Definition: Advection by the relative mean flow.** The relative-flow field differentiates the perturbation along the mean velocity relative to the rotating and expanding frame. Source: `Breakdown.Coercive.Internal.MuTransport.relField` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:28`).

**Definition: Advection by the model waves.** The wave field differentiates the perturbation along the model field with its mean removed. Source: `Breakdown.Coercive.Internal.MuTransport.waveField` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:31`).

**Theorem: Decompose the transport field.** The inner field decomposes into time derivative, half the velocity, relative-frame advection, angular transport and the negative Laplacian, with model waves separated where displayed. Source: `Breakdown.Coercive.Internal.MuTransport.innerPart_decomp` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:34`).

**Theorem: Continuity of time-derivative field.** Under the stated hypotheses, the time-derivative field is continuous. Source: `Breakdown.Coercive.Internal.MuTransport.timeField_continuous` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:41`).

**Theorem: Continuity of derivative.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.Internal.MuTransport.gradField_continuous` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:54`).

**Theorem: Continuity of negative Laplacian field.** Under the stated hypotheses, the negative Laplacian field is continuous. Source: `Breakdown.Coercive.Internal.MuTransport.sumSecondPartialsPart_continuous` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:59`).

**Theorem: The rotated operator entry is continuous.** Applying the shifted field of linear maps to the supplied continuous vector and pulling back by rotation gives a continuous time-angle coordinate. Source: `Breakdown.Coercive.Internal.MuTransport.clm_integrand_continuous` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:67`).

**Theorem: Rotate the axial generator.** Applying the axial rotation generator before or after axial rotation gives the same vector. Source: `Breakdown.Coercive.Internal.MuTransport.rotJ_comm` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:79`).

**Theorem: Inverse axial rotations cancel.** Successive axial rotations through opposite angles return the original vector. Source: `Breakdown.Coercive.Internal.MuTransport.rot_neg_rot` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:85`).

**Theorem: The mean field is axially equivariant.** Pulling back the mean field at a rotated point gives its unrotated coordinate value. Source: `Breakdown.Coercive.Internal.MuTransport.meanField_rot_coord` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:89`).

**Theorem: Modes of a matrix-vector product.** The mode of the displayed matrix-vector product is the mean contribution plus the convolution of the finite coefficient modes with shifted input modes. Source: `Breakdown.Coercive.Internal.MuTransport.mode_product_vec` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:104`).

**Theorem: Real vectors inside complex space.** Viewing a real vector as a complex vector preserves its Euclidean norm. Source: `Breakdown.Coercive.Internal.MuTransport.cnorm3_real` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:155`).

**Theorem: Bound relative-mean-flow advection.** The relative-flow advection mode has amplitude at most the relative speed times the gradient-mode amplitude. Source: `Breakdown.Coercive.Internal.MuTransport.rel_mode_le` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:162`).

**Theorem: Bound advection by the model waves.** The advection amplitude from the model waves is at most the finite convolution of model velocity amplitudes with shifted perturbation-gradient amplitudes. Source: `Breakdown.Coercive.Internal.MuTransport.wave_mode_le` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:202`).

**Theorem: Modes of the transport decomposition.** Taking the time-angular mode preserves the displayed sum of transport, frame, wave and diffusion contributions. Source: `Breakdown.Coercive.Internal.MuTransport.inner_mode_linear` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:247`).

**Theorem: Isolate the rotating-frame frequency.** The transport mode separates into the imaginary frame-frequency term, component rotation, half the velocity, bounded advection terms and diffusion. Source: `Breakdown.Coercive.Internal.MuTransport.inner_mode_split` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:330`).

**Theorem: Complex Cauchy–Schwarz bound.** The norm of the complex pairing is at most the product of the two complex-vector norms. Source: `Breakdown.Coercive.Internal.MuTransport.norm_cdot_le_amp` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:358`).

**Theorem: The rotation generator contracts energy.** The squared complex norm of the axial rotation generator is at most the squared norm of the input vector. Source: `Breakdown.Coercive.Internal.MuTransport.cnormSq_rotZ_le` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:367`).

**Theorem: Expand the frame-frequency pairing.** The imaginary pairing with the decomposed transport field becomes the frequency-weighted square plus the rotation, advection and diffusion pairings. Source: `Breakdown.Coercive.Internal.MuTransport.pairTerm_expand` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:373`).

**Theorem: Bound an imaginary weighted real part.** The absolute real part of an imaginary real-weighted complex number is at most the absolute weight times the complex norm. Source: `Breakdown.Coercive.Internal.MuTransport.abs_re_I_mul_le` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:386`).

**Theorem: A pointwise velocity transport bound.** The frequency density minus the transport loss with the gradient charge restored, plus the diffusion pairing, is at most the inner-field pairing. Source: `Breakdown.Coercive.Internal.MuTransport.transport_pointwise` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:390`).

**Theorem: A diffusion lower bound on each slice.** For almost every time in the unit interval, the diffusion mode pairing is bounded below by the negative integrated weight-gradient loss. Source: `Breakdown.Coercive.Internal.MuTransport.sumSecondPartials_slice` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:458`).

**Theorem: Velocity-frequency density is integrable.** Under the stated hypotheses, the velocity-frequency density is integrable. Source: `Breakdown.Coercive.Internal.MuTransport.integrable_dopDensity` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:487`).

**Theorem: Integrability of transport loss.** Under the stated hypotheses, the transport loss is integrable. Source: `Breakdown.Coercive.Internal.MuTransport.integrable_transportLoss` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:531`).

**Theorem: The velocity gradient charge is L1.** Under the stated hypotheses, the velocity-weight gradient charge is integrable. Source: `Breakdown.Coercive.Internal.MuTransport.integrable_gradLoss` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:582`).

**Theorem: Nonnegative velocity gradient charge.** The velocity-weight gradient charge is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.MuTransport.gradLoss_nonneg` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:619`).

**Theorem: Continuity of velocity pairing.** Under the stated hypotheses, the velocity-weight pairing density is continuous. Source: `Breakdown.Coercive.Internal.MuTransport.pairTerm_continuous` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:624`).

**Theorem: The diffusion field lies in period L2.** The negative-Laplacian field is measurable, one-periodic and square-integrable over one time period and space. Source: `Breakdown.Coercive.Internal.MuTransport.sumSecondPartialsPart_square` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:633`).

**Theorem: A weighted square bound for the pairing.** The absolute velocity-mode pairing is at most twice the weight bound times the sum of the weighted-velocity and partner-mode squares. Source: `Breakdown.Coercive.Internal.MuTransport.pairTerm_weighted_le` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:647`).

**Theorem: The diffusion mode pairing is integrable.** The weighted imaginary pairing of the velocity mode with the negative-Laplacian mode is integrable on the period slab. Source: `Breakdown.Coercive.Internal.MuTransport.integrable_pairSumSecondPartials` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:682`).

**Theorem: Control the transport pairing error.** After removing the frequency and diffusion terms, the remaining transport pairing is bounded by transport loss minus the separately reserved weight-gradient charge. Source: `Breakdown.Coercive.Internal.MuTransport.inner_pointwise_abs` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:709`).

**Theorem: The inner transport field is continuous.** Under the stated hypotheses, the transport-diffusion-advection field is continuous. Source: `Breakdown.Coercive.Internal.MuTransport.innerPart_continuous` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:784`).

**Theorem: The inner-field pairing integrates.** The weighted imaginary pairing of the velocity mode with the inner-field mode is integrable on the period slab. Source: `Breakdown.Coercive.Internal.MuTransport.integrable_pairInner` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:814`).

**Theorem: Every transport-pairing term integrates.** The transport pairing, frequency density, transport loss, diffusion pairing and weight-gradient charge are all integrable on the unit time slab. Source: `Breakdown.Coercive.Internal.MuTransport.transport_integrable` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:841`).

**Theorem: Read the real integral on the slab.** The displayed iterated real integral equals the integral against the unit-time product measure. Source: `Breakdown.Coercive.Internal.MuTransport.slab_integral_eq` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:861`).

**Theorem: A nonnegative integral gives a real one.** The nonnegative slab integral equals the nonnegative embedding of the real slab integral under the stated sign and integrability assumptions. Source: `Breakdown.Coercive.Internal.MuTransport.slab_lintegral_eq` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:865`).

**Theorem: The integrated velocity transport bound.** The velocity-frequency term is controlled by the signed inner-field pairing plus the integrated transport loss. Source: `Breakdown.Coercive.Internal.MuTransport.transport_bound_of` (`Breakdown/Cert/CoerciveSmoothMuTransport.lean:871`).

### Breakdown.Cert.CoerciveSmoothMuWave

Expands model waves and differentiates their mode coefficients to estimate advection and model-gradient convolution terms.

**Paper context:** Appendix B, (B.16) and Proposition B.1: finite harmonic interactions in the velocity-weighted estimate.

**Theorem: Multiplying phases subtracts frequencies.** Multiplying the negative extraction phase by a positive wave phase gives the extraction phase at the frequency difference. Source: `Breakdown.Coercive.Internal.MuSmooth.exp_pair_mul` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:19`).

**Theorem: Conjugate phases add frequencies.** Multiplying the two negative Fourier phases gives the negative phase at the sum of their frequencies. Source: `Breakdown.Coercive.Internal.MuSmooth.exp_pair_mul_conj` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:29`).

**Theorem: The real wave and its conjugate.** A complex exponential times a coefficient has real part equal to half its sum with the conjugate wave. Source: `Breakdown.Coercive.Internal.MuSmooth.re_exp_mul_eq` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:39`).

**Theorem: A real wave shifts a mode twice.** Multiplication by a real Fourier wave gives half the sum of the two shifted modes weighted by the coefficient and its conjugate. Source: `Breakdown.Coercive.Internal.MuSmooth.mode_re_mul` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:46`).

**Definition: Integrate over time and angle.** The double integral runs over one unit of time and one full angular turn. Source: `Breakdown.Coercive.Internal.MuSmooth.boxInt` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:86`).

**Theorem: Additivity of the box integral.** The time-angular box integral of a sum is the sum of the two box integrals. Source: `Breakdown.Coercive.Internal.MuSmooth.boxInt_add` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:88`).

**Theorem: Scale the box integral.** A constant complex factor can be pulled out of the time-angular box integral. Source: `Breakdown.Coercive.Internal.MuSmooth.boxInt_const_mul` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:101`).

**Theorem: The box integral of zero.** The time-angular box integral of zero is zero. Source: `Breakdown.Coercive.Internal.MuSmooth.boxInt_zero` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:105`).

**Theorem: Integrate a finite Fourier sum.** The time-angular box integral commutes with the displayed finite sum. Source: `Breakdown.Coercive.Internal.MuSmooth.boxInt_sum` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:108`).

**Theorem: Normalise the Fourier box integral.** The mode average is the phase-weighted box integral divided by the full angular length. Source: `Breakdown.Coercive.Internal.MuSmooth.modeAverage_eq_boxInt` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:118`).

**Theorem: Inverse axial rotations cancel.** Successive axial rotations through opposite angles return the original vector. Source: `Breakdown.Coercive.Internal.MuSmooth.rot_rot_neg` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:122`).

**Theorem: Expansion in the coordinate basis.** A vector is the sum of its coordinates times the corresponding unit vectors. Source: `Breakdown.Coercive.Internal.MuSmooth.vec_expand` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:131`).

**Theorem: Axial rotation is real linear.** Axial rotation commutes with the displayed real scalar combination. Source: `Breakdown.Coercive.Internal.MuSmooth.rot_sum` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:135`).

**Theorem: Apply an operator in rotated coordinates.** A rotated operator value expands as the sum of its rotated matrix entries times the rotated input coordinates. Source: `Breakdown.Coercive.Internal.MuSmooth.rot_apply_clm` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:141`).

**Theorem: The complex orbit entry is continuous.** The real pulled-back orbit coordinate, embedded into complex numbers, is continuous in the time-angle parameters. Source: `Breakdown.Coercive.Internal.MuSmooth.cont_rot_field` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:154`).

**Theorem: Continuity of complex Fourier phase.** Under the stated hypotheses, the complex Fourier phase is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.cont_exp_pair` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:166`).

**Theorem: Modes of a matrix-vector product.** The mode of the displayed matrix-vector product is the mean contribution plus the convolution of the finite coefficient modes with shifted input modes. Source: `Breakdown.Coercive.Internal.MuSmooth.mode_product` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:170`).

**Theorem: Rotate the velocity-mode coefficients.** The displayed mode of a rotated and time-shifted field equals the rotated coordinate combination of its shifted mode coefficients. Source: `Breakdown.Coercive.Internal.MuSmooth.rot_modeVel_eq` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:225`).

**Theorem: Real parts through real linear sums.** The real part of a finite real-weighted complex sum equals the same weighted sum of real parts. Source: `Breakdown.Coercive.Internal.MuSmooth.re_sum_real_mul` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:258`).

**Theorem: Reconstruct the model field from modes.** The rotated model field equals its mean plus the displayed finite wave sum. Source: `Breakdown.Coercive.Internal.MuSmooth.rot_field_expansion` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:263`).

**Theorem: The zero mode ignores the time origin.** The zero temporal-angular mode is independent of the displayed time origin. Source: `Breakdown.Coercive.Internal.MuSmooth.modeVel_mean_shift` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:283`).

**Theorem: C2 regularity of function W.** Under the stated hypotheses, the function $W$ has continuous derivatives through order $2$. Source: `Breakdown.Coercive.Internal.MuSmooth.slice_contDiff_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:307`).

**Theorem: Continuity of derivative.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_slice_fderiv_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:311`).

**Theorem: Differentiate the rotated integrand.** The displayed phase-weighted rotated integrand has the stated Fréchet derivative. Source: `Breakdown.Coercive.Internal.MuSmooth.hasFDerivAt_integrand_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:318`).

**Theorem: Continuous mode-test derivatives.** Under the stated hypotheses, the spatial derivative of the mode-test integrand is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_integrandDeriv_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:351`).

**Theorem: The mode-test integrand is continuous.** Under the stated hypotheses, the rotated mode-test integrand is continuous. Source: `Breakdown.Coercive.Internal.MuSmooth.continuous_integrand_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:372`).

**Theorem: A mode coefficient as a box integral.** The displayed mode coordinate is its phase-weighted time-angular integrand divided by the full angular length. Source: `Breakdown.Coercive.Internal.MuSmooth.modeVel_eq_box_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:385`).

**Theorem: Differentiate a velocity-mode coordinate.** The velocity-mode coordinate has a Fréchet derivative whose coordinate values are the corresponding gradient-mode entries. Source: `Breakdown.Coercive.Internal.MuSmooth.modeVel_hasFDerivAt_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:395`).

**Theorem: Opposite modes are conjugate.** For the displayed real input, reversing both frequency indices conjugates its complex mode coefficient. Source: `Breakdown.Coercive.Internal.MuSmooth.modeAverage_neg` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:437`).

**Theorem: Opposite modes are conjugate.** For the displayed real input, reversing both frequency indices conjugates its complex mode coefficient. Source: `Breakdown.Coercive.Internal.MuSmooth.modeGrad_neg` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:452`).

**Theorem: Opposite Fourier phases are conjugate.** Negating the frequency pair conjugates the time-angular Fourier phase. Source: `Breakdown.Coercive.Internal.MuSmooth.phase_neg` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:457`).

**Theorem: A symmetric wave sum is real.** For the stated conjugate-symmetric coefficients and frequency set, the complex Fourier sum equals the embedding of its real part. Source: `Breakdown.Coercive.Internal.MuSmooth.re_sum_sym` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:466`).

**Definition: The complex three-vector norm.** The complex three-vector norm is the square root of the sum of squared coordinate norms. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:477`).

**Theorem: Complex Euclidean norm.** The square root of the complex coordinate square sum is the Euclidean norm of the corresponding complex vector. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_eq` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:479`).

**Theorem: The complex vector norm is nonnegative.** The square root of the sum of squared complex coordinate norms is nonnegative. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_nonneg` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:483`).

**Theorem: Triangle inequality for complex norms.** The complex-vector norm of a sum is at most the sum of the two norms. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_add_le` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:485`).

**Theorem: The zero vector has zero norm.** The complex-vector norm of zero is zero. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_zero` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:489`).

**Theorem: Norm of a finite vector sum.** The norm of a finite sum of complex vectors is at most the sum of their norms. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_sum_le` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:492`).

**Theorem: Recover a norm bound from its square.** The supplied squared-norm bound implies the nonnegative complex-vector norm bound. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_le_of_sq` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:501`).

**Theorem: Square of the complex norm.** Squaring the nonnegative complex-vector norm recovers the sum of squared coordinate norms. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_sq` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:506`).

**Theorem: Matrix action bounded by entry squares.** The complex matrix-vector norm is at most the matrix's square-root entry norm times the input vector norm. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_mat_le` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:508`).

**Theorem: Read a coordinate expansion.** The indicated coordinate of a sum of coordinate unit vectors equals its coefficient. Source: `Breakdown.Coercive.Internal.MuSmooth.space_sum_apply` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:520`).

**Theorem: Matrix action in coordinates.** The indicated coordinate of a linear-map value is the sum of matrix entries times the input coordinates. Source: `Breakdown.Coercive.Internal.MuSmooth.clm_coord` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:523`).

**Theorem: Euclidean norm in coordinates.** The squared Euclidean norm is the sum of the squared real coordinates. Source: `Breakdown.Coercive.Internal.MuSmooth.space_norm_sq` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:528`).

**Theorem: A real operator on a complex vector.** The norm of a real operator extended to complex coordinates is at most its real operator norm times the complex-vector norm. Source: `Breakdown.Coercive.Internal.MuSmooth.cnorm3_clm_le` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:532`).

**Theorem: The model slice is differentiable.** The stated joint regularity of the model field implies spatial differentiability on each time slice. Source: `Breakdown.Coercive.Internal.MuSmooth.slice_differentiable_of` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:566`).

**Theorem: Reconstruct the model gradient.** The rotated model gradient equals its mean gradient plus the displayed finite gradient-mode wave sum. Source: `Breakdown.Coercive.Internal.MuSmooth.grad_expansion` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:570`).

**Theorem: The mean gradient is the zero mode.** Each mean-field gradient coordinate is the real part of the corresponding zero gradient mode. Source: `Breakdown.Coercive.Internal.MuSmooth.meanField_fderiv_apply` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:615`).

**Theorem: Bound model-gradient coupling by modes.** The displayed model-gradient coupling mode is bounded by the stated mean and finite-wave gradient-amplitude contributions. Source: `Breakdown.Coercive.Internal.MuSmooth.stretch_mode_le` (`Breakdown/Cert/CoerciveSmoothMuWave.lean:632`).
<!-- /passage:front -->

