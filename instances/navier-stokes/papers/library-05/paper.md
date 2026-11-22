
<!-- passage:front -->
# Library guide 5: Breakdown/Cert

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) **5** [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Cert.CoerciveSmoothPairingSplit` to `Breakdown.Cert.Data` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.Cert.CoerciveSmoothPairingSplit

Identifies the smooth multiplier pairing with its base, curl and velocity components by approximation with periodic test fields.

**Paper context:** Appendix B, (B.14) and Proposition B.1: interpretation and splitting of the multiplier pairing.

**Theorem: Move radial damping out of a pairing.** Pairing the original velocity mode equals one plus the radius times the pairing with its radially damped mode. Source: `Breakdown.Coercive.Internal.SmoothModeSplit.cdot_scaled` (`Breakdown/Cert/CoerciveSmoothPairingSplit.lean:18`).

**Theorem: Move the radial factor into the weight.** The velocity-pairing integrand can be expressed using damped velocity after multiplying its weight by one plus the radius. Source: `Breakdown.Coercive.Internal.SmoothModeSplit.mu_integrand_eq` (`Breakdown/Cert/CoerciveSmoothPairingSplit.lean:27`).

**Theorem: The weighted velocity-mode pairing.** The velocity-mode pairing is the general weighted-mode term for damped velocity and the rescaled spatial weight. Source: `Breakdown.Coercive.Internal.SmoothModeSplit.muTerm_eq` (`Breakdown/Cert/CoerciveSmoothPairingSplit.lean:37`).

**Theorem: Read curl pairing as a vorticity term.** The curl-mode pairing is the general weighted-mode term applied to the two vorticity fields. Source: `Breakdown.Coercive.Internal.SmoothModeSplit.epsTerm_eq` (`Breakdown/Cert/CoerciveSmoothPairingSplit.lean:43`).

**Theorem: Test-field pairings converge to the form.** The mode-sum pairings of the approximating test fields converge to the sum of the curl and velocity pairings. Source: `Breakdown.Coercive.Internal.SmoothModeSplit.modeSum_tendsto_smooth` (`Breakdown/Cert/CoerciveSmoothPairingSplit.lean:51`).

**Theorem: The multiplier pairing splits exactly.** The solenoidal multiplier pairing equals the negative-Laplacian energy pairing plus the curl-weight and velocity-weight pairings. Source: `Breakdown.Coercive.Internal.SmoothModeSplit.solenoidal_multiplier_pairing_smooth` (`Breakdown/Cert/CoerciveSmoothPairingSplit.lean:130`).

**Theorem: Split the smooth multiplier pairing.** The smooth multiplier pairing splits into its Laplacian, curl-weight and velocity-weight contributions. Source: `Breakdown.Coercive.modePairingSplitSmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothPairingSplit.lean:172`).

### Breakdown.Cert.CoerciveSmoothPairingSplitClass

Verifies the square-integrability and regularity requirements for the forcing, diffusion and weighted fields used in the pairing split.

**Paper context:** Appendix B, (B.14) and Proposition B.1: interpretation and splitting of the multiplier pairing.

**Definition: Spacetime measure on one period.** The measure is Lebesgue measure restricted to the unit time interval, multiplied by spatial Lebesgue measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.periodProductMeasure` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:16`).

**Theorem: Square integrability of function h.** Under the stated hypotheses, the function $h$ belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_of_real` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:19`).

**Theorem: An L2 scalar field has finite energy.** The real scalar field's squared period integral is finite under the stated $L^2$ hypothesis. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.lt_top_of_memLp_real` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:30`).

**Theorem: Square integrability of function h.** Under the stated hypotheses, the function $h$ belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_of_continuous_real` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:39`).

**Theorem: Square integrability of function h.** Under the stated hypotheses, the function $h$ belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_of_bound` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:44`).

**Theorem: The second iterated derivative.** The second iterated derivative and the derivative of the derivative have equal norms. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.norm_iter_two` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:51`).

**Theorem: The third iterated derivative.** The third iterated derivative has the norm of the three successive Fréchet derivatives. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.norm_iter_three` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:57`).

**Theorem: Smoothness of derivative.** Under the stated hypotheses, the spatial derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.slice_contDiff` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:63`).

**Theorem: Smoothness of time derivative.** Under the stated hypotheses, the time derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.time_contDiff` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:68`).

**Theorem: Smoothness of similarity transport field.** Under the stated hypotheses, the similarity transport field is smooth. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.transport_contDiff` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:75`).

**Theorem: A slice inherits joint regularity.** Each spatial time slice has the same stated order of continuous differentiability as the joint spacetime field. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.slice_of_joint` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:82`).

**Theorem: Expand the linearised right-hand side.** The displayed identity separates similarity transport, the negative Laplacian and the two linearised advection contributions, with the indicated subtraction where present. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.smoothRight_eq` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:87`).

**Theorem: Smoothness of second derivative trace.** Under the stated hypotheses, the second derivative trace is smooth. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.secondDerivTrace_contDiff` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:91`).

**Theorem: C1 regularity of linearised field.** Under the stated hypotheses, the linearised right-hand side has continuous derivatives through order $1$. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.smoothRight_contDiff'` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:97`).

**Theorem: Time periodicity of linearised field.** Under the stated hypotheses, the linearised right-hand side has period one in time. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.smoothRight_periodic'` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:115`).

**Theorem: Trace bounded by operator norm.** The norm of the second derivative trace is at most three times the operator norm. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.norm_secondDerivTrace_le` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:129`).

**Definition: The second derivative trace map.** The trace map adds the second derivative values along the three coordinate axes. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.traceCLM` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:141`).

**Theorem: Evaluate the trace map.** The trace map is the sum of the three diagonal second derivative values. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.traceCLM_apply` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:145`).

**Theorem: Bound the derivative of the trace.** The derivative norm of the second derivative trace is at most three times the derivative norm of its operator-valued input. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.norm_fderiv_trace_le` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:148`).

**Theorem: Bound a differentiated operator product.** The norm of the differentiated operator-field product is bounded by the sum of the two operator-norm products from the product rule. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.norm_fderiv_apply_le` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:161`).

**Theorem: The decay constant is nonnegative.** The decay assumptions force the displayed decay constant to be nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.decay_nonneg` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:167`).

**Theorem: Simplify a radial decay factor.** Under the stated exponent and sign assumptions, the inverse power of one plus the radius is bounded by the displayed weaker radial factor. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.div_pow_le_div` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:174`).

**Theorem: Simplify a radial decay factor.** Under the stated exponent and sign assumptions, the inverse power of one plus the radius is bounded by the displayed weaker radial factor. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.div_pow_le` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:181`).

**Theorem: The radially weighted norm is continuous.** The velocity norm divided by one plus the radius is jointly continuous in time and space. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.weighted_continuous` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:184`).

**Theorem: The radially weighted norm lies in L2.** The velocity norm divided by one plus the radius belongs to $L^2$ for the period product measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_weighted` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:188`).

**Theorem: The spatial derivative norm is in L2.** Under the stated hypotheses, the norm of the spatial derivative belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_deriv_one` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:197`).

**Theorem: The second derivative norm is in L2.** Under the stated hypotheses, the norm of the spatial second derivative belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_deriv_two` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:206`).

**Theorem: The third derivative norm is in L2.** Under the stated hypotheses, the norm of the spatial third derivative belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_deriv_three` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:216`).

**Theorem: The similarity-transport norm is in L2.** Under the stated hypotheses, the norm of the similarity transport field belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_transport` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:229`).

**Theorem: The transport-gradient norm is in L2.** Under the stated hypotheses, the norm of the spatial derivative of the similarity transport field belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.memLp_transport_deriv` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:238`).

**Theorem: Control the linearised field norm.** The linearised-field norm is bounded by transport, three times the Hessian norm, and the displayed model-weighted gradient and velocity terms. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.smoothRight_norm_le` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:248`).

**Theorem: The linearised field lies in period L2.** The linearised right-hand side is measurable, periodic and square-integrable over one time period and space. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.smoothRight_square'` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:278`).

**Theorem: Control the linearised gradient.** The spatial derivative of the linearised right-hand side is bounded by transport derivatives, third derivatives and the displayed model-perturbation derivative products. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.smoothRight_fderiv_norm_le` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:293`).

**Theorem: The forcing gradient has finite energy.** The squared matrix norm of the spatial derivative of the smooth right-hand side has finite period integral. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.smoothRight_fderiv_sq` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:367`).

**Theorem: The Laplacian preserves zero divergence.** The negative Laplacian of the stated smooth divergence-free field has zero divergence. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.divergence_negSsp` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:389`).

**Theorem: Decay gives integrability.** The displayed measurable function is integrable under the supplied integrable domination. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.integrable_of_far` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:446`).

**Theorem: A gradient pairing in coordinates.** Pairing a vector with a scalar gradient equals the sum of its coordinates times the scalar's coordinate derivatives. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.inner_gradientAt` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:451`).

**Theorem: The Laplacian is orthogonal to gradients.** The negative Laplacian of the stated divergence-free field has zero integral pairing with the test-potential gradient. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.slice_negSsp_orthogonal` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:460`).

**Theorem: The negative Laplacian is C1.** The negative spatial Laplacian of the perturbation is continuously differentiable in spacetime. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.negSsp_contDiff` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:511`).

**Theorem: Finite second-derivative norm energy.** The squared operator norm of the second spatial derivative has finite period integral. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.sq_iter_two_finite` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:515`).

**Theorem: Finite third-derivative norm energy.** The squared operator norm of the third spatial derivative has finite period integral. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.sq_iter_three_finite` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:523`).

**Theorem: Finite diffusion-gradient energy.** The squared matrix norm of the negative Laplacian field's spatial derivative has finite period integral. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.negSsp_fderiv_sq` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:531`).

**Theorem: The negative Laplacian is solenoidal.** The negative-Laplacian field is its own solenoidal part under the stated smoothness and energy assumptions. Source: `Breakdown.Coercive.Internal.SmoothPairingClass.negSsp_solenoidal_self` (`Breakdown/Cert/CoerciveSmoothPairingSplitClass.lean:547`).

### Breakdown.Cert.CoerciveSmoothPieceDensity

Assembles finite mode-piece curl and velocity estimates with the base energy identity into the signed smooth density bound.

**Paper context:** Appendix B, (B.16), (B.19) and Proposition B.1: assembly of the finite mode-piece multiplier bounds.

**Theorem: Read a split bound as a real inequality.** For the stated finite nonnegative quantities, the sign-split inequality is equivalent to the displayed inequality between real values. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.real_form` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:21`).

**Theorem: A finite remainder forces finiteness.** The split lower-bound inequality forces the positive quantity to be finite when the stated remainder is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.ne_top_of_split` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:38`).

**Theorem: Add two split lower bounds.** Adding two signed lower-bound inequalities gives the corresponding split inequality for the sums. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.split_add` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:42`).

**Theorem: Sum finitely many split lower bounds.** A finite family of signed lower bounds adds to the split lower bound for the summed terms. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.split_sum` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:54`).

**Theorem: A sum under a nonnegative integral.** The displayed sum of nonnegative iterated integrals is at most the iterated integral of the sum. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.dbl_sum` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:69`).

**Theorem: Rebalance a real difference.** The displayed positive and negative parts agree after a real difference is distributed between the two sides. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.ofReal_identity` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:84`).

**Theorem: Allocate positive and negative densities.** The displayed pointwise sign-split inequality combines base density, finite curl and velocity pieces, and their block charges without dropping a negative contribution. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.point` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:95`).

**Theorem: Bound the combined negative part.** The combined negative density and block terms are at most the sum of the separately charged negative parts. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.neg_point` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:154`).

**Theorem: Assemble the piece-density lower bound.** The individual measurable finite split bounds combine into the full piece-density lower bound with the stated stretching term. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.assemble` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:191`).

**Theorem: Nonnegative edge charge.** The mode-edge charge is nonnegative under the stated nonnegativity assumptions on its amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.edgeSum_nonneg_of` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:322`).

**Theorem: Nonpositivity of curl-piece remainder.** The curl-piece mode remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.epsRest_nonpos` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:334`).

**Theorem: Velocity-piece remainder is nonpositive.** The velocity-piece mode remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.muRest_nonpos` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:341`).

**Theorem: The curl-piece block is nonpositive.** The curl-piece block remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.epsBlock_nonpos` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:350`).

**Theorem: The velocity-piece block is nonpositive.** The velocity-piece block remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.muBlock_nonpos` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:368`).

**Theorem: Assemble the smooth piece density.** The base estimate and the curl and velocity piece estimates combine into the smooth piece-density lower bound. Source: `Breakdown.Coercive.pieceDensitySmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothPieceDensity.lean:386`).

### Breakdown.Cert.CoerciveSmoothPieceDensityBase

Proves the negative base-density estimate for the mode-piece formulation from finite derivative mode sums.

**Paper context:** Appendix B, (B.16) and Proposition B.1: the conversion weights that replace curl energies by derivative energies.

**Definition: Velocity with a square-root weight.** The damped velocity is divided by the square root of one plus the squared spatial norm. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.dampVel` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:19`).

**Theorem: Square-root radial damping of a mode.** The velocity mode of the square-root damped field is the original mode multiplied by the same radial damping factor. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.modeVel_dampVel` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:22`).

**Theorem: Square-root damping of mode energy.** The damped velocity-mode square equals the original mode square divided by one plus the squared spatial norm. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.cnormSq_modeVel_dampVel` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:32`).

**Theorem: Square-root damping of physical energy.** The damped physical velocity square equals the original velocity square divided by one plus the squared spatial norm. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.norm_dampVel_sq` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:40`).

**Theorem: Exchange the mode sum and integral.** Under the stated measurability assumptions, the nonnegative sum over modes can be interchanged with integration over one time period and space. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.tsum_slab_base` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:46`).

**Theorem: Domination gives a finite integral.** The supplied pointwise domination by a finite nonnegative period integral makes the displayed period integral finite. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.periodLIntegral_lt_top_of_le_base` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:55`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.norm_unitVector_base` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:67`).

**Theorem: Squared Hessian norm bound.** The sum of squared second derivative entries is at most nine times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.secondDerivSq_le_base` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:71`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.matSq_le_base` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:86`).

**Theorem: Dominate the negative base density.** The negative expanded base expression is bounded by the displayed nonnegative combination of derivative squares and radially weighted velocity squares. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.base_coef_bound` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:97`).

**Theorem: Bound the conversion-weight Hessian.** The Hessian norms of all displayed conversion weights admit one common finite bound. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.secondDerivNorm_convD_bound_base` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:148`).

**Theorem: Finite negative base-density mass.** The period integral of the nonnegative sum of the negative base-density mode contributions is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.base_neg_finite_of_mode_sums` (`Breakdown/Cert/CoerciveSmoothPieceDensityBase.lean:175`).

### Breakdown.Cert.CoerciveSmoothPieceDensityBlock

Establishes measurability of the frame-speed, vorticity and vorticity-gradient supremum bounds and the piece block losses.

**Paper context:** Appendix B, (B.16), (B.19) and Proposition B.1: assembly of the finite mode-piece multiplier bounds.

**Theorem: C1 regularity of curl vector.** Under the stated hypotheses, the curl vector has continuous derivatives through order $1$. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.contDiff_curlVec` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:17`).

**Theorem: Coordinate evaluation is continuous.** Taking a fixed real coordinate of a spatial vector is a continuous function. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.continuous_coord` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:21`).

**Theorem: A continuous supremum is measurable.** The pointwise supremum of the stated family of continuous functions is measurable under the supplied hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.measurable_iSup_of` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:24`).

**Theorem: Measurability of frame speed.** Under the stated hypotheses, the supremum of the frame-relative speed is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.measurable_frameSpeedSup` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:29`).

**Theorem: Measurability of model vorticity.** Under the stated hypotheses, the model-vorticity norm bound is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.measurable_vortSup` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:48`).

**Theorem: Model vorticity gradient is measurable.** Under the stated hypotheses, the model-vorticity-gradient norm bound is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.measurable_vortGradSup` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:61`).

**Theorem: Norm over a mode piece is ae measurable.** Under the stated hypotheses, the norm over a mode piece is almost everywhere measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.aemeasurable_pieceNorm` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:77`).

**Theorem: Both block losses are measurable.** For each mode piece, the nonnegative embeddings of both negative block remainders are almost everywhere measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.aemeasurable_block_terms` (`Breakdown/Cert/CoerciveSmoothPieceDensityBlock.lean:97`).

### Breakdown.Cert.CoerciveSmoothPieceDensityEnergy

Converts the smooth vorticity and stretching energy identity to the unit-slab integrals used in the piece-density assembly.

**Paper context:** Appendix B, Proposition B.1: the base smooth energy identity leading to the coercive inequality (B.20).

**Theorem: Stretching-form density is ae measurable.** Under the stated hypotheses, the stretching-form density is almost everywhere measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.aemeasurable_stretch_slab` (`Breakdown/Cert/CoerciveSmoothPieceDensityEnergy.lean:24`).

**Theorem: Integrability of stretching-form density.** Under the stated hypotheses, the stretching-form density is integrable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.stretch_integrable_slab` (`Breakdown/Cert/CoerciveSmoothPieceDensityEnergy.lean:34`).

**Theorem: Integrable vorticity energy on the slab.** The vorticity-gradient square plus one quarter of the vorticity square is integrable on the unit spacetime slab. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.vorticity_integrable_slab` (`Breakdown/Cert/CoerciveSmoothPieceDensityEnergy.lean:117`).

**Theorem: Split stretching into finite sign parts.** The stretching density has measurable finite positive and negative integrals, and the smooth energy integral splits into vorticity energy plus their real difference. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.energy_split` (`Breakdown/Cert/CoerciveSmoothPieceDensityEnergy.lean:174`).

### Breakdown.Cert.CoerciveSmoothPieceDensityMeasure

Controls measurability and finiteness of the mode-piece frequency seminorms and density contributions.

**Paper context:** Appendix B, (B.16), (B.19) and Proposition B.1: assembly of the finite mode-piece multiplier bounds.

**Theorem: Measurability of the assembled densities.** The curl pieces, velocity pieces, base density and all listed negative remainder sums are almost everywhere measurable on the time slab. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.parts_measurable` (`Breakdown/Cert/CoerciveSmoothPieceDensityMeasure.lean:24`).

**Theorem: Magnitude of a mode-piece sign.** The absolute mode-piece sign equals the indicator of membership in the piece or its reflected partner. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.abs_sgn_eq` (`Breakdown/Cert/CoerciveSmoothPieceDensityMeasure.lean:139`).

**Theorem: A sum under a nonnegative integral.** The displayed sum of nonnegative iterated integrals is at most the iterated integral of the sum. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.sum_le_dbl` (`Breakdown/Cert/CoerciveSmoothPieceDensityMeasure.lean:148`).

**Theorem: Each velocity-piece seminorm is finite.** The velocity-piece frequency seminorm is finite under the stated admissibility and perturbation assumptions. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.part_finite` (`Breakdown/Cert/CoerciveSmoothPieceDensityMeasure.lean:160`).

### Breakdown.Cert.CoerciveSmoothPieceDensityPairing

Establishes the regularity, finite period energy and pairing decomposition of the smooth right-hand side in the piece formulation.

**Paper context:** Appendix B, (B.14) and Proposition B.1: interpretation and splitting of the multiplier pairing.

**Theorem: Pair two square-integrable fields.** The inner product of the two square-integrable fields is integrable on the displayed measure space. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.slab_integrable_inner` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:22`).

**Theorem: Read the real integral on the slab.** The displayed iterated real integral equals the integral against the unit-time product measure. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.slab_pairing_eq` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:63`).

**Theorem: Linearity of the period pairing.** Pairing a field plus a finite actuator combination with a multiplier gives the field pairing plus the same finite linear combination of actuator pairings. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.pairing_linear` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:71`).

**Theorem: Finiteness of a summed period integral.** The period integral of the sum of the two stated nonnegative integrands is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.period_add_lt_top` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:101`).

**Theorem: A square bound for the linearised field.** The squared linearised-field norm is bounded by the explicit $4(9+D^2)$ multiple of transport, Hessian, gradient and weighted-velocity square energies. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.smoothRight_sq_le` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:112`).

**Theorem: Expand the linearised right-hand side.** The displayed identity separates similarity transport, the negative Laplacian and the two linearised advection contributions, with the indicated subtraction where present. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.smoothRight_eq` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:156`).

**Theorem: Time derivative from the joint field.** The time derivative equals the joint Fréchet derivative applied to the unit time direction. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.deriv_time_eq` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:160`).

**Theorem: Continuity of similarity transport field.** Under the stated hypotheses, the similarity transport field is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.continuous_transportPart` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:169`).

**Theorem: Measurability of second derivative trace.** Under the stated hypotheses, the second derivative trace is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.measurable_sumSecondPartials` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:182`).

**Theorem: Strong measurability of linearised field.** Under the stated hypotheses, the linearised right-hand side is almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.aesm_smoothRight` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:191`).

**Theorem: Time periodicity of linearised field.** Under the stated hypotheses, the linearised right-hand side has period one in time. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.periodic_smoothRight` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:209`).

**Theorem: The linearised field lies in period L2.** The linearised right-hand side is measurable, periodic and square-integrable over one time period and space. Source: `Breakdown.Coercive.Internal.SmoothPieceDensity.right_side_sq` (`Breakdown/Cert/CoerciveSmoothPieceDensityPairing.lean:222`).

### Breakdown.Cert.CoerciveSmoothPieceEps

Combines curl-piece frequency, diffusion and remainder estimates into the signed smooth curl-piece inequality.

**Paper context:** Appendix B, Proposition B.1: the curl-piece terms of the multiplier and their frequency gains and error charges.

**Theorem: Nonnegative indicator.** A zero-one indicator is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.ind_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:15`).

**Theorem: Nonnegative edge charge.** The mode-edge charge is nonnegative under the stated nonnegativity assumptions on its amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.edgeSum_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:19`).

**Theorem: Nonnegative piece norm.** The square-root sum of mode squares over a piece is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:32`).

**Theorem: Nonnegativity of curl-piece density.** The positive curl-piece density is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.pos_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:40`).

**Theorem: Nonpositivity of curl-piece remainder.** The curl-piece mode remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.rest_nonpos` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:45`).

**Theorem: The curl-piece block is nonpositive.** The curl-piece block remainder is nonpositive under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.block_nonpos` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:60`).

**Theorem: Turn a real bound into a sign split.** The stated real inequality gives the corresponding extended-nonnegative inequality after positive and negative parts are separated. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.ennreal_step` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:89`).

**Theorem: Build a bound from the signs.** The stated real bound, measurability, finiteness and sign conditions supply the split lower-bound predicate. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.split_of_signs` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:104`).

**Theorem: Finite time-weighted curl-mode energy.** The period integral of the mode sum of temporal-frequency squares times vorticity-mode squares is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.time_series_finite` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:120`).

**Theorem: Finite angle-weighted curl-mode energy.** The period integral of the mode sum of weighted absolute angular frequency times vorticity-mode squares is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.angular_series_finite` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:126`).

**Theorem: Finite curl-piece frequency energy.** The period integral of the mode sum of the positive curl-piece frequency densities is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.frequency_series_finite` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:134`).

**Theorem: Finite curl-piece negative loss.** The period integral of the negative curl-piece mode remainders together with the negative block remainder is finite after nonnegative embedding. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.negative_parts_finite` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:238`).

**Theorem: The integrated curl-piece lower bound.** The integrated positive curl-piece series is at most its signed curl pairing plus the integrated negative mode and block charges. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.core_inequality` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:319`).

**Theorem: The smooth curl-piece estimate.** The positive frequency series and finite negative charges supply the smooth curl-piece lower bound. Source: `Breakdown.Coercive.pieceEpsEstimateSmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothPieceEps.lean:341`).

### Breakdown.Cert.CoerciveSmoothPieceEpsBounds

Provides uniform coordinate, norm and decay bounds for the finite model harmonics and their derivative amplitudes.

**Paper context:** Appendix B, Proposition B.1: the curl-piece terms of the multiplier and their frequency gains and error charges.

**Theorem: A mode average obeys the uniform bound.** The norm of the normalised mode average is at most the supplied uniform bound on its real integrand. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.norm_modeAverage_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:15`).

**Theorem: A finite coordinate norm bound.** A complex-vector norm is at most the number of coordinates times the supplied nonnegative coordinate bound. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.sqrt_cnormSq_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:36`).

**Theorem: A coordinate is bounded by the norm.** The absolute value of each real coordinate is at most the vector norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.abs_coord_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:57`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.norm_unit` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:61`).

**Theorem: Rotated coordinate vectors are unit.** An axially rotated coordinate unit vector still has norm one. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.norm_rot_unit` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:64`).

**Theorem: Decay of the model velocity modes.** Each model velocity-mode amplitude is at most $3D/(1+|y|)$. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.velAmp_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:73`).

**Theorem: Decay of the model gradient modes.** Each model gradient-mode amplitude is at most $9D/(1+|y|)^2$. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.gradAmp_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:86`).

**Theorem: Decay of the model Hessian modes.** Each model second derivative amplitude is at most $27D/(1+|y|)^3$. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.secondDerivAmp_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:102`).

**Theorem: Decay of model vorticity amplitudes.** Each model vorticity-mode amplitude is bounded by the displayed $16\cdot9D/(1+|y|)^2$ estimate. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.vortAmp_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:122`).

**Theorem: Decay of model vorticity-gradient modes.** Each model vorticity-gradient amplitude is bounded by $27\cdot27D/(1+|y|)^3$. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.vortGradAmp_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:135`).

**Theorem: Nonnegative frame-speed bound.** The supremum of the frame-relative speed is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.frameSpeedSup_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:151`).

**Theorem: Nonnegative vorticity bound.** The supremum of the model vorticity norm is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.vortSup_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:154`).

**Theorem: Nonnegative vorticity-gradient bound.** The supremum of the model vorticity-gradient norm is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.vortGradSup_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:157`).

**Theorem: Curl from the operator norm.** The curl norm is at most twenty-seven times the input operator norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.norm_curlVec_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:161`).

**Theorem: Bound the axial rotation generator.** The norm of the axial rotation generator is at most twice the spatial norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.norm_perp_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:189`).

**Theorem: The decay constant is nonnegative.** The decay assumptions force the displayed decay constant to be nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.decay_const_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:199`).

**Theorem: A radial bound for the frame speed.** The frame-relative speed is at most the model bound plus $(1/2+2|a|)$ times the spatial norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.frameSpeedSup_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:204`).

**Theorem: Decay of the model-vorticity supremum.** The model-vorticity supremum is bounded by $27D/(1+|y|)^2$. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.vortSup_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:224`).

**Theorem: Curl is additive in the gradient.** The curl vector of a sum of gradient matrices is the sum of their curl vectors. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.curlVec_add` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:233`).

**Theorem: Curl respects scalar multiplication.** The curl vector of a real scalar multiple of a matrix is the same scalar multiple of its curl vector. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.curlVec_smul` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:246`).

**Definition: Curl as a continuous linear map.** This bundles the matrix-to-curl operation as a continuous linear map. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.curlLinear` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:259`).

**Theorem: Evaluate the linear curl map.** The continuous linear curl map returns the curl vector of its matrix argument. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.curlLinear_apply` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:265`).

**Theorem: Decay of the vorticity-gradient supremum.** The model-vorticity-gradient supremum is bounded by $27D/(1+|y|)^3$. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.vortGradSup_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsBounds.lean:267`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompression

Bounds the within-piece harmonic interactions by block suprema and charges the interactions that cross piece edges.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Theorem: The four edge-charge series converge.** The four displayed vorticity-weighted edge-charge series are summable over the modes under the stated finite-energy assumptions. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.edge_summable` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompression.lean:21`).

**Theorem: Bound the vorticity-transport series.** Almost everywhere with finite negative series, the signed vorticity transport series is summable and its adverse contribution is bounded by its edge charges and the stated frame-speed block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.transport_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompression.lean:54`).

**Theorem: Bound the model-stretching series.** Almost everywhere with finite negative series, the signed model stretching series is summable and its adverse contribution is bounded by its edge charges and the stated half-vorticity block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.stretch_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompression.lean:72`).

**Theorem: Bound the model-vorticity transport.** Almost everywhere with finite negative series, the signed model-vorticity transport series is summable and its adverse contribution is bounded by its edge charges and the stated vorticity-gradient block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.vortTransport_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompression.lean:89`).

**Theorem: Bound the model-vorticity stretching.** Almost everywhere with finite negative series, the signed model-vorticity stretching series is summable and its adverse contribution is bounded by its edge charges and the stated vorticity block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.vortStretch_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompression.lean:107`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompressionAssembly

Assembles transport, stretching and model-vorticity compression estimates into the curl-piece remainder bound.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Theorem: Nonnegative indicator.** A zero-one indicator is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.ind_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionAssembly.lean:16`).

**Theorem: Indicator bounded by one.** A zero-one indicator is at most one. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.ind_le_one` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionAssembly.lean:19`).

**Theorem: Bound a signed curl-piece term.** The absolute curl-piece pairing term is bounded by the piece indicator, nonnegative spatial weight and the two mode amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.term_abs_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionAssembly.lean:22`).

**Theorem: Pass from compressed modes to their sum.** The pointwise approximation and summability assumptions give both upper and lower bounds for the signed remainder sum by the edge charges plus the retained block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.assemble` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionAssembly.lean:32`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompressionGrid

Proves finite Fourier-grid orthogonality and the no-aliasing identities needed to bound a restricted convolution.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Theorem: A nontrivial grid root is not one.** The displayed nonzero frequency smaller than the grid size gives a complex grid phase distinct from one. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.exp_ne_one_of_lt` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:16`).

**Theorem: Orthogonality on a one-dimensional grid.** The finite geometric phase sum is the grid size at zero frequency and zero at the stated nonzero frequencies. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.geom_phase_sum` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:36`).

**Definition: Fourier phase on a finite grid.** The grid phase evaluates a time-angular Fourier character at the chosen equally spaced grid point. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.gridPhase` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:55`).

**Theorem: Separate the two grid phases.** The time-angular grid phase is the product of its temporal and angular grid exponentials. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.gridPhase_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:58`).

**Theorem: Multiply grid Fourier phases.** The grid phase at the sum of two frequencies equals the product of their grid phases. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.gridPhase_add` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:67`).

**Theorem: Conjugation reverses the grid frequency.** The conjugate grid phase equals the grid phase at the negative frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.gridPhase_conj` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:76`).

**Theorem: Orthogonality on the time-angular grid.** The two-dimensional grid phase sum is the squared grid size at zero frequency and zero for the stated other frequencies. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.gridPhase_sum` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:85`).

**Definition: A finite Hermitian pairing.** The pairing sums each first-vector coordinate times the conjugate of the corresponding second-vector coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.dotq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:100`).

**Theorem: Self-pairing is the squared norm.** The Hermitian pairing of a complex vector with itself equals its real squared norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.dotq_self` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:102`).

**Theorem: Complex Cauchy–Schwarz bound.** The norm of the complex pairing is at most the product of the two complex-vector norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.norm_dotq_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:110`).

**Definition: A finite Fourier combination.** The combination sums the displayed vectors after multiplication by their grid Fourier phases. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.combG` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:119`).

**Theorem: Pair two finite grid Fourier sums.** The Hermitian pairing of two finite grid reconstructions expands into frequency-difference phases times their coefficient pairings. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.dot_combG` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:123`).

**Theorem: The grid selects equal frequencies.** Summing the two finite Fourier reconstructions' pairings over the grid keeps precisely equal-frequency coefficient pairs, scaled by the squared grid size. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.grid_dot` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:138`).

**Theorem: Apply the symbol to a Fourier sum.** Applying the matrix symbol to a finite Fourier combination gives the convolution combination indexed by sums of frequencies. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.symbol_apply_comb` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:156`).

**Theorem: Finite-grid Parseval identity.** The sum of squared reconstruction norms on the grid equals the squared grid size times the sum of squared mode norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.grid_norm` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:173`).

**Theorem: Keep differences inside the grid.** The stated component bounds place the indicated frequency difference strictly below the chosen grid size. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.abs_lt_of3` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:188`).

**Theorem: Keep differences inside the grid.** The stated component bounds place the indicated frequency difference strictly below the chosen grid size. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.abs_lt_of2` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:194`).

**Theorem: Choose a grid with no aliasing.** A positive grid size can be chosen larger than all frequency differences among the three displayed finite frequency sets. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.grid_size` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:199`).

**Theorem: A finite convolution pairing bound.** A uniform matrix-symbol bound controls the finite convolution pairing by that bound times the two coefficient $\ell^2$ norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.finite_symbol_pairing_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionGrid.lean:231`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompressionParts

Separates each convolution into its within-piece and edge terms and verifies the signed piece algebra.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Theorem: First coordinate of axial rotation.** The first rotated coordinate is the cosine times the first coordinate minus the sine times the second. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.rc0` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:18`).

**Theorem: Second coordinate of axial rotation.** The second rotated coordinate is the sine times the first coordinate plus the cosine times the second. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.rc1` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:21`).

**Theorem: Axial rotation fixes height.** Axial rotation leaves the third coordinate unchanged. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.rc2` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:24`).

**Theorem: First rotation-generator coordinate.** The first coordinate of the axial rotation generator is the negative second coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.pc0` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:27`).

**Theorem: Second rotation-generator coordinate.** The second coordinate of the axial rotation generator is the first coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.pc1` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:29`).

**Theorem: Zero axial generator coordinate.** The third coordinate of the axial rotation generator is zero. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.pc2` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:31`).

**Theorem: Pull back the frame components.** Pulling back the model vector plus radial and rotational frame vectors gives the pulled-back model vector plus the frame vectors at the original point. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.rot_frame` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:33`).

**Theorem: Rotate a matrix without losing its bound.** The complex squared norm of the rotated real operator applied to a vector is bounded by the squared real operator norm times the input square. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.rot_clm_cnormSq_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:49`).

**Theorem: Velocity-mode squares are summable.** For almost every point of the stated measure space, the velocity-mode squares form a summable series. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.summable_vel_ae` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:98`).

**Theorem: A piece excludes opposite pairs.** A valid selected curl-mode half-piece contains no mode together with its negative. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.piece_disjoint` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:128`).

**Theorem: Piece restriction preserves summability.** The complex-mode square sum restricted by the piece indicator is summable. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.ind_summable` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:143`).

**Theorem: The required mode-amplitude squares sum.** For almost every spacetime point, the displayed gradient, vorticity and derivative amplitude-square series are summable. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.summable_ae` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:151`).

**Theorem: Compress vorticity transport.** Almost everywhere with finite negative series, vorticity transport admits a retained mode-piece part with the stated edge-error bound and summed pairing bound. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.transport_compression` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:202`).

**Theorem: Compress model stretching.** Almost everywhere with finite negative series, model stretching admits a retained mode-piece part with the stated edge-error bound and summed pairing bound. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.stretch_compression` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:294`).

**Theorem: Compress model-vorticity transport.** Almost everywhere with finite negative series, model-vorticity transport admits a retained mode-piece part with the stated edge-error bound and summed pairing bound. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.vortTransport_compression` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:423`).

**Theorem: Compress model-vorticity stretching.** Almost everywhere with finite negative series, model-vorticity stretching admits a retained mode-piece part with the stated edge-error bound and summed pairing bound. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompressionParts.vortStretch_compression` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionParts.lean:507`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompressionProduct

Expands finite products of model harmonics with perturbation modes to connect physical-space multiplication with frequency convolution.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Theorem: Squared norm of a sum.** The squared norm of a sum equals the two squared norms plus twice the real part of their complex pairing. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.cnormSq_add` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:16`).

**Theorem: Triangle inequality for complex norms.** The complex-vector norm of a sum is at most the sum of the two norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.sqrt_cnormSq_add_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:21`).

**Theorem: Norm of a finite vector sum.** The norm of a finite sum of complex vectors is at most the sum of their norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.sqrt_cnormSq_sum_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:35`).

**Theorem: Reindex a symmetric finite set.** Negation reindexes the finite sum over the stated symmetric frequency set without changing its value. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.sum_neg_reindex` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:46`).

**Theorem: Combine two square-root products.** The sum of the two square-root products is bounded by the product of the square roots of their two paired sums. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.sqrt_mul_add_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:51`).

**Theorem: A half-piece square fits the full piece.** The squared norm retained by the displayed half-piece is bounded by the full-piece membership indicator times the mode square. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.halfSq_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:61`).

**Theorem: Split a mode piece into two halves.** The full-piece squared mode norm is the sum of the selected half-piece square and its reflected half-piece square. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.ind_split` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:72`).

**Theorem: Compress convolution inside a piece.** The mode product admits a retained within-piece part whose omitted part is bounded by edge charges and whose signed pairing is controlled by the symbol bound and the two piece norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.compression_of_product` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionProduct.lean:87`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompressionSymbol

Transfers a pointwise matrix-symbol bound to the square-summable within-piece mode coupling.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Theorem: The half-piece square is nonnegative.** The squared norm restricted to a half-piece is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.halfSq_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:17`).

**Definition: Squared matrix-entry norm.** The squared matrix-entry norm is the sum of squared complex norms of all entries. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.matSqMat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:25`).

**Theorem: A matrix square bound on its action.** The squared norm of the matrix-vector product is bounded by the matrix entry-square sum times the squared vector norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.cnormSq_applyMat_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:27`).

**Theorem: Pairing with a finite sum.** Pairing with a finite sum equals the sum of the individual pairings. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.cdot_finset_sum` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:42`).

**Definition: A coupling kept inside a mode piece.** The coupling pairs a mode with a matrix-applied shifted mode when both belong to the chosen piece, and is zero otherwise. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.pairPiece` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:49`).

**Theorem: Split a half-piece pairing by harmonics.** The half-piece pairing is the finite sum of its individual coefficient-harmonic couplings. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.halfPairing_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:53`).

**Theorem: Within-piece mode coupling is summable.** Under the stated hypotheses, the within-piece mode coupling is summable over the indicated index. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.pairPiece_summable` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:69`).

**Theorem: Rewrite a finite restricted convolution.** The partial half-piece pairing sum equals the displayed finite convolution sum over retained output and shifted input indices. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.partial_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:101`).

**Theorem: The full symbol pairing bound.** The half-piece pairing is summable, and its total norm is bounded by the uniform symbol bound times the two half-piece $\ell^2$ norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.symbol_pairing_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbol.lean:130`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompressionSymbolDefs

Defines the Fourier matrix symbol, restricted half-piece convolution and their pairings used in the compression argument.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Definition: Complex matrix-vector multiplication.** The matrix application forms each output coordinate by summing matrix entries times input coordinates. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.applyMat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbolDefs.lean:16`).

**Definition: A time-angular Fourier character.** The character is the complex exponential of the temporal and angular phase determined by the integer frequency pair. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.torusPhase` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbolDefs.lean:18`).

**Definition: The matrix Fourier symbol.** The symbol matrix sums the coefficient matrices against their time-angular Fourier characters. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.symbolMat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbolDefs.lean:20`).

**Definition: Convolution restricted to one piece.** The restricted convolution retains only shifted input modes that remain inside the chosen half-piece. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.halfPart` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbolDefs.lean:25`).

**Definition: Squared norm on a half-piece.** The half-piece square is the squared mode norm inside the selected set and zero outside it. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.halfSq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbolDefs.lean:30`).

**Definition: Pairing on a half-piece.** The half-piece pairing couples a selected mode to the restricted convolution, and vanishes outside the selected set. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.halfPairing` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionSymbolDefs.lean:34`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCompressionVector

Specialises the matrix-symbol compression bound to vector and matrix interactions by controlling their coordinate rows.

**Paper context:** Appendix B, Proposition B.1: within-piece harmonic estimates and edge errors in the skew multiplier calculation.

**Definition: Matrix for vector contraction.** This matrix packages contraction of the gradient coordinates with the mean vector or the indicated model-wave vector. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.vecMat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:17`).

**Theorem: The contraction matrix acts rowwise.** Applying the packaged vector-contraction matrix gives the displayed rowwise contraction with its mean or wave coefficient. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.applyMat_vecMat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:20`).

**Theorem: Cauchy–Schwarz for complex coordinates.** The norm of the coordinate product sum is at most the product of the two complex coordinate norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.norm_sum_mul_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:27`).

**Theorem: A matrix square bound on its action.** The squared norm of the matrix-vector product is bounded by the matrix entry-square sum times the squared vector norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.cnormSq_rows_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:34`).

**Theorem: The symbol reconstructs the flow.** The vector-contraction symbol acts by rowwise contraction with the mean vector plus its finite wave reconstruction. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.symbolMat_vecMat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:52`).

**Theorem: A vector product as matrix convolution.** The mean-plus-wave vector product equals the finite convolution of the packaged coefficient matrices with shifted gradient modes. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.vec_product_sum` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:72`).

**Theorem: The row-contraction amplitude bound.** The contraction amplitude is at most the product of the two square-root coordinate-square norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.rows_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:88`).

**Theorem: Compress convolution inside a piece.** The mode product admits a retained within-piece part whose omitted part is bounded by edge charges and whose signed pairing is controlled by the symbol bound and the two piece norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.compression_vec` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:93`).

**Definition: Mean and wave matrix coefficients.** The coefficient matrix is the mean matrix at zero frequency and the corresponding wave matrix at every other frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.matMat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:132`).

**Theorem: Two matrix-square encodings agree.** The row-and-column matrix square equals the complex coordinate square of the same flattened entries. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.matSqMat_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:135`).

**Theorem: The row-contraction amplitude bound.** The contraction amplitude is at most the product of the two square-root coordinate-square norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.mat_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:139`).

**Theorem: Compress convolution inside a piece.** The mode product admits a retained within-piece part whose omitted part is bounded by edge charges and whose signed pairing is controlled by the symbol bound and the two piece norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCompression.compression_mat` (`Breakdown/Cert/CoerciveSmoothPieceEpsCompressionVector.lean:144`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCore

Provides the measurable piece norms, weighted diffusion bound and integrated signed remainder ingredients of the curl-piece estimate.

**Paper context:** Appendix B, Proposition B.1: the curl-piece terms of the multiplier and their frequency gains and error charges.

**Definition: Data for the curl-piece estimate.** These conditions collect admissible mode pieces, regular decaying model data and a smooth perturbation for the curl-piece argument. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.CoreSetting` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:19`).

**Definition: One signed curl-piece pairing.** The signed curl-piece term pairs two vorticity modes with the piece sign and spatial weight. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.pieceTerm` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:30`).

**Theorem: The curl pairing is a mode sum.** The curl-weight pairing equals the sum over all modes of the corresponding integrated curl-mode terms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.epsPairing_eq_tsum` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:35`).

**Definition: The negative spatial Laplacian.** This field is the negative trace of the spatial second derivative. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.negSumSecondPartials` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:39`).

**Definition: The curl-piece gradient charge.** The charge is the weight-gradient norm times the two piece norms of vorticity and its gradient. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.gradPart` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:42`).

**Definition: Positive curl-piece mode series.** The positive series sums the nonnegative curl-piece frequency contributions over every mode. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.posSeries` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:46`).

**Definition: Negative curl-piece mode series.** The negative series sums the modewise curl remainders and the common block remainder with their signs reversed. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.negSeries` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:50`).

**Theorem: Integrate the signed density bound.** The stated measurable and finite positive and negative densities give the real integrated lower bound after their pointwise and integral estimates are combined. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.core_of_parts` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:55`).

**Theorem: A nonnegative series is measurable a.e..** The pointwise series of the stated nonnegative measurable terms is almost everywhere measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.aem_tsum_of_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:75`).

**Theorem: Norm over a mode piece is ae measurable.** Under the stated hypotheses, the norm over a mode piece is almost everywhere measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.aem_pieceNorm` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:84`).

**Theorem: A continuous supremum is measurable.** The pointwise supremum of the stated continuous family is measurable under the supplied hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.measurable_iSup_of_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:93`).

**Theorem: Continuity of rotated field or vector.** Under the stated hypotheses, the rotated field or vector is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.continuous_rot` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:99`).

**Theorem: C2 regularity of function W.** Under the stated hypotheses, the function $W$ has continuous derivatives through order $2$. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.slice_contDiff` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:103`).

**Theorem: Differentiate curl by a linear map.** The spatial derivative of model vorticity is the continuous curl map composed with the model Hessian. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortGrad_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:109`).

**Theorem: Measurability of frame speed.** Under the stated hypotheses, the supremum of the frame-relative speed is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.measurable_frameSpeedSup` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:117`).

**Theorem: Measurability of model vorticity.** Under the stated hypotheses, the model-vorticity norm bound is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.measurable_vortSup` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:146`).

**Theorem: Model vorticity gradient is measurable.** Under the stated hypotheses, the model-vorticity-gradient norm bound is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.measurable_vortGradSup` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:157`).

**Theorem: A real series from its sign parts.** The real sum of the summable series is the real positive-part sum minus the real negative-part sum. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.tsum_eq_parts` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:180`).

**Theorem: Exchange a dominated series and integral.** The stated integrable absolute bound yields almost-everywhere summability, integrability of the sum and equality of the sum of integrals with the integral of the sum. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.exchange_of_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:192`).

**Theorem: Mode-piece sign bounded by one.** The absolute value of a mode-piece sign is at most one. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.abs_sgn_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:231`).

**Theorem: Measurable positive and negative series.** The positive curl-piece series and the combined negative series are almost everywhere measurable on the unit time slab. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.parts_aemeasurable` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:240`).

**Theorem: The linearised gradient lies in L2.** The spatial gradient of the linearised right-hand side is measurable, one-periodic and square-integrable over the time slab. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.right_gradient_finite` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:303`).

**Theorem: Integrate the curl-piece series.** The curl-piece series is almost everywhere summable and integrable, and its integral equals the full signed curl pairing. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.pairing_exchange_of` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:310`).

**Theorem: Integrate the curl-piece series.** The curl-piece series is almost everywhere summable and integrable, and its integral equals the full signed curl pairing. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.pairing_exchange` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:386`).

**Theorem: The Laplacian gradient lies in L2.** The gradient of the negative-Laplacian field is measurable, periodic and square-integrable on the time slab. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.negSumSecondPartials_gradient_finite` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:399`).

**Theorem: The curl gradient charge integrates.** The piece curl weight-gradient charge is integrable on the unit spacetime slab. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.gradPart_integrable` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:428`).

**Theorem: Magnitude of a mode-piece sign.** The absolute mode-piece sign equals the indicator of membership in the piece or its reflected partner. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.abs_sgn_eq_ind` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:502`).

**Theorem: Scale a derivative norm.** The norm of the derivative of a constant multiple is bounded by the absolute constant times the original derivative norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.norm_fderiv_const_mul_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:507`).

**Theorem: A summable piecewise product bound.** The selected real product series is summable and its sum is bounded by the common coefficient times the two piece norms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.piece_sum_mul_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:525`).

**Theorem: Diffusion pays only a gradient charge.** The curl-piece pairing with the negative Laplacian plus the integrated weight-gradient charge is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.sumSecondPartials_pairing_lower` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:579`).

**Theorem: The curl-piece diffusion lower bound.** The summed curl-piece pairing with the negative Laplacian is bounded below by minus the integrated piece weight-gradient charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.sumSecondPartials_lower` (`Breakdown/Cert/CoerciveSmoothPieceEpsCore.lean:725`).

### Breakdown.Cert.CoerciveSmoothPieceEpsCoreModes

Computes the rotating-frame curl-mode equation and applies the signed compression bounds to its component remainders.

**Paper context:** Appendix B, Proposition B.1: the curl-piece terms of the multiplier and their frequency gains and error charges.

**Theorem: An algebraic curl transport identity.** The displayed alternating-symbol expansion rewrites the curl of the two matrix-product transport terms using the stated zero traces. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.frame_alg` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:16`).

**Theorem: Matrix action in coordinates.** The indicated coordinate of a linear-map value is the sum of matrix entries times the input coordinates. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.apply_expand` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:27`).

**Theorem: Curl of two trace-free compositions.** For the stated trace-free maps, the sum of the curls of their two compositions equals minus each map applied to the other's curl. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.curl_comp_pair` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:36`).

**Theorem: Differentiate a matrix curve's curl.** Differentiating the curl of a differentiable matrix curve gives the curl of its derivative. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.hasDerivAt_curlVec` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:54`).

**Theorem: The Hessian flip fixes a direction.** The stated symmetry of the second derivative identifies its flipped evaluation with evaluation in the unflipped direction. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.flip_eq_of_symm` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:72`).

**Theorem: The vorticity equation in a moving frame.** The vorticity of the linearised field minus diffusion splits into scaled time derivative, vorticity, angular frame transport and the full frame remainder. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortField_identity` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:78`).

**Theorem: Time differentiation multiplies a mode.** The mode of the time derivative is the original mode multiplied by the imaginary temporal frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.modeVel_time_vort` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:169`).

**Theorem: Differentiate a Fourier phase.** Differentiating the displayed complex exponential multiplies it by the negative imaginary phase frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.hasDerivAt_angle_phase` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:202`).

**Theorem: The phase matches at period ends.** The complex Fourier phase has the same value at the two displayed endpoints of one period. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.angle_phase_period` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:210`).

**Theorem: Angular integration by parts in a mode.** Periodic angular integration by parts turns an angular derivative into multiplication by the imaginary angular frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.modeAverage_angle_deriv` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:218`).

**Theorem: First coordinate of axial rotation.** The first rotated coordinate is the cosine times the first coordinate minus the sine times the second. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.rot_coord0` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:256`).

**Theorem: Second coordinate of axial rotation.** The second rotated coordinate is the sine times the first coordinate plus the cosine times the second. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.rot_coord1` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:259`).

**Theorem: Axial rotation fixes height.** Axial rotation leaves the third coordinate unchanged. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.rot_coord2` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:262`).

**Theorem: First rotation-generator coordinate.** The first coordinate of the axial rotation generator is the negative second coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.perp_coord0` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:265`).

**Theorem: Second rotation-generator coordinate.** The second coordinate of the axial rotation generator is the first coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.perp_coord1` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:267`).

**Theorem: Zero axial generator coordinate.** The third coordinate of the axial rotation generator is zero. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.perp_coord2` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:269`).

**Theorem: Differentiate the rotation angle.** The angular derivative of a rotated vector is the axial rotation generator applied to that rotated vector. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.hasDerivAt_rot_angle` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:271`).

**Theorem: Differentiate one coordinate.** The derivative of a coordinate of a differentiable vector curve is the corresponding coordinate of its derivative. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.hasDerivAt_coord` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:289`).

**Theorem: Differentiate a pulled-back field.** Differentiating a vector field pulled back by axial rotation gives its angular derivative minus the rotation of its vector components. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.hasDerivAt_rot_field` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:293`).

**Theorem: Angular transport of vorticity modes.** The corrected angular transport of vorticity has mode equal to imaginary angular frequency times the vorticity mode. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.modeVel_angular_vort` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:326`).

**Theorem: The curl-mode equation in the frame.** The linearised curl mode minus diffusion equals imaginary frame frequency times vorticity, plus vorticity and the frame-remainder mode. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.mode_identity` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:364`).

**Theorem: Rotate the axial-generator contribution.** The rotated generator has the displayed cross-coupled first two coordinates and zero axial coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.rot_perp` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:419`).

**Theorem: Pull a real factor through a mode.** The pointwise scalar relation between integrands gives the same real scalar relation between their mode averages. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.modeAverage_congr_mul` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:432`).

**Theorem: Coordinates of the rotation remainder.** The rotation-remainder mode swaps the first two vorticity-mode coordinates with the displayed signs and has zero axial coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.modeVel_rotationRest` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:439`).

**Theorem: Bound the rotation pairing.** The absolute rotation pairing is at most the product of the absolute weight, absolute rotation rate and squared mode norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.rotation_term_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:451`).

**Theorem: Split the five frame-remainder terms.** The frame remainder splits into transport, negative stretching, model-vorticity transport, negative model-vorticity stretching and rotation terms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.restPart_split` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:484`).

**Theorem: Bound the vorticity-transport series.** Almost everywhere with finite negative series, the signed vorticity transport series is summable and its adverse contribution is bounded by its edge charges and the stated frame-speed block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.transport_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:527`).

**Theorem: Bound the model-stretching series.** Almost everywhere with finite negative series, the signed model stretching series is summable and its adverse contribution is bounded by its edge charges and the stated half-vorticity block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.stretch_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:540`).

**Theorem: Bound the model-vorticity transport.** Almost everywhere with finite negative series, the signed model-vorticity transport series is summable and its adverse contribution is bounded by its edge charges and the stated vorticity-gradient block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortTransport_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:552`).

**Theorem: Bound the model-vorticity stretching.** Almost everywhere with finite negative series, the signed model-vorticity stretching series is summable and its adverse contribution is bounded by its edge charges and the stated vorticity block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortStretch_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:565`).

**Theorem: Bound the vorticity-rotation series.** Almost everywhere with finite negative series, the rotation-remainder series is summable and its adverse contribution is bounded by the weighted absolute frame rate times the squared vorticity piece norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.rotation_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:578`).

**Theorem: Charge the summed curl remainder.** The negative sum of the curl frame remainder is controlled by the combined negative series after removing the separately allocated weight-gradient charge. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.compression_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:642`).

**Theorem: Separate a difference of curl pairings.** The difference of the two imaginary pairings equals the frequency-weighted square plus the remainder pairing. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.term_split` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:737`).

**Theorem: Opposite modes have opposite frequency.** Negating both mode indices negates the rotating-frame frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.frameFreq_neg` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:753`).

**Theorem: Signed frame frequency is positive.** On a valid mode piece, its sign times the frame frequency equals the membership indicator times the absolute frame frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.sgn_mul_frameFreq` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:759`).

**Theorem: The curl-piece pairing difference.** Subtracting the diffusion pairing from the linearised curl-piece pairing gives the positive frequency density plus the frame-remainder term. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.pieceTerm_sub` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:782`).

**Theorem: The pointwise curl-piece bound.** At almost every point with finite positive and negative series, the positive series is controlled by the linearised pairing, negative charges and the displayed diffusion correction. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.pointwise_lower` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:806`).

**Theorem: The integrated curl-piece lower bound.** The integrated positive curl-piece series is at most its signed curl pairing plus the integrated negative mode and block charges. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.core_inequality_of_setting` (`Breakdown/Cert/CoerciveSmoothPieceEpsCoreModes.lean:849`).

### Breakdown.Cert.CoerciveSmoothPieceEpsFrequency

Proves finite temporal and angular frequency-weighted vorticity energies using mode differentiation and square sums.

**Paper context:** Appendix B, (B.15) and Proposition B.1: rotating-frame frequencies and the finite frequency seminorm.

**Theorem: Spatial derivative from the joint field.** The spatial derivative is the joint Fréchet derivative restricted to spatial directions. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.gradField_eq_of_smooth` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:15`).

**Theorem: Continuity of gradient.** Under the stated hypotheses, the spatial gradient field is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.continuous_gradField_of_smooth` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:20`).

**Theorem: Time derivative from the joint field.** The time derivative equals the joint Fréchet derivative applied to the unit time direction. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.deriv_time_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:29`).

**Theorem: Smoothness of time derivative.** Under the stated hypotheses, the time derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.timeDeriv_smooth` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:36`).

**Theorem: Commute time and gradient derivatives.** The time derivative of the spatial gradient applied to a direction equals the gradient of the time-derivative field in that direction. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.hasDerivAt_gradField_time` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:45`).

**Theorem: Differentiate a Fourier phase.** Differentiating the displayed complex exponential multiplies it by the negative imaginary phase frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.hasDerivAt_phase` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:89`).

**Theorem: The phase matches at period ends.** The complex Fourier phase has the same value at the two displayed endpoints of one period. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.phase_one` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:100`).

**Theorem: Time integration by parts in a mode.** Periodic integration by parts turns a time derivative inside the mode average into multiplication by its imaginary temporal frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.modeAverage_time_deriv` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:108`).

**Theorem: A finite square sum is continuous.** The squared complex coordinate norm is a continuous real function. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.continuous_cnormSq'` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:151`).

**Theorem: Squared norm after complex scaling.** Scaling every complex coordinate multiplies the squared coordinate norm by the squared norm of the scalar. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.cnormSq_const_mul` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:155`).

**Theorem: Exchange the mode sum and integral.** Under the stated measurability assumptions, the nonnegative sum over modes can be interchanged with integration over one time period and space. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.iter_tsum_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:162`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.matSq_le_three` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:169`).

**Theorem: Differentiate a rotated vector curve.** The derivative of a rotated coordinate of a vector curve is the same rotated coordinate of its derivative. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.hasDerivAt_rot_coord` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:179`).

**Theorem: The orbit gradient entry is continuous.** The gradient family evaluated on a rotated coordinate vector and pulled back by rotation is continuous in the time-angle parameters. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.continuous_rot_family` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:185`).

**Theorem: Time derivative of a gradient mode.** The gradient mode of the time derivative is the gradient mode multiplied by the imaginary temporal frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.modeGrad_time` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:196`).

**Theorem: Finite time-weighted curl-mode energy.** The period integral of the sum of squared temporal frequencies times squared vorticity-mode amplitudes is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.time_series_finite` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:231`).

**Theorem: Control angular contraction by radius.** The squared matrix contraction with the angular direction is at most the squared spatial radius times the sum of squared matrix entries. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.contracted_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:289`).

**Theorem: Angular frequency from a gradient bound.** The stated angular derivative relation bounds angular-frequency squared times the mode square by eight times the mode square plus twice the radius-weighted derivative square. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.angular_pointwise_general` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:309`).

**Theorem: Angular gradient-mode energy bound.** For almost every spacetime point, angular-frequency squared times the gradient-mode square is bounded by its stated gradient and radius-weighted Hessian terms. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.angular_grad_mode_bound` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:329`).

**Theorem: Control absolute frequency by squares.** The assumed squared-frequency bound gives the displayed absolute-frequency bound with coefficients three and the radius factor. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.abs_mul_le_of_sq` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:398`).

**Theorem: Monotonicity over one period.** The stated pointwise or almost-everywhere ordering passes to the iterated nonnegative integral over one time period. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.slab_mono_ae` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:411`).

**Theorem: Finite angle-weighted curl-mode energy.** The period integral of the sum of spatially weighted absolute angular frequencies times squared vorticity-mode amplitudes is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsFrequency.angular_series_finite` (`Breakdown/Cert/CoerciveSmoothPieceEpsFrequency.lean:419`).

### Breakdown.Cert.CoerciveSmoothPieceEpsNeg

Bounds the negative curl-piece mode and block contributions by a finite comparison-energy integral.

**Paper context:** Appendix B, Proposition B.1: the curl-piece terms of the multiplier and their frequency gains and error charges.

**Theorem: Dominate the edge sum by shifted modes.** The edge charge is at most the common coefficient times the finite sum of the two shifted comparison amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.edgeSum_le_crude` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:14`).

**Theorem: Sum the shifted product charges.** The sum of the mode-amplitude times shifted-amplitude products is bounded by the shift count times the stated two square sums. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.tsum_edge_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:31`).

**Theorem: A piece norm fits the full mode energy.** The nonnegative squared piece norm is at most the sum of all mode-amplitude squares. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.ofReal_pieceNorm_sq_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:60`).

**Theorem: Scale a mode-piece norm.** Multiplying every amplitude by the stated nonnegative scalar multiplies the piece norm by the same scalar. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.pieceNorm_mul` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:73`).

**Theorem: Separate four error products.** The nonnegative embedding of the four-term remainder product is bounded by the stated common coefficient times the four separated products. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.rest_term_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:81`).

**Theorem: Nonnegative piece norm.** The square-root sum of mode squares over a piece is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.pieceNorm_nonneg'` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:103`).

**Theorem: Simplify a radial decay factor.** Under the stated exponent and sign assumptions, the inverse power of one plus the radius is bounded by the displayed weaker radial factor. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.decay_le_self` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:111`).

**Theorem: Control the curl-piece edge remainder.** The negative curl-piece edge series is bounded by the displayed harmonic count and decay coefficient times vorticity, vorticity-gradient, gradient and weighted-velocity square sums. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.rest_pointwise` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:114`).

**Theorem: Bound four block products by squares.** The four coefficient-weighted block products are at most four times the common coefficient bound times the four-square sum. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.block_real` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:188`).

**Theorem: Control the curl-piece block remainder.** The negative curl-piece block is bounded by the explicit coefficient built from weight, frame-rate and model-decay bounds times the four required mode-square sums. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.block_pointwise` (`Breakdown/Cert/CoerciveSmoothPieceEpsNeg.lean:205`).

### Breakdown.Cert.CoerciveSmoothPieceEpsRestDefs

Defines the transport, stretching, model-vorticity and rotation remainders in the curl equation and records their regularity.

**Paper context:** Appendix B, Proposition B.1: the curl-piece terms of the multiplier and their frequency gains and error charges.

**Definition: The axial rotation generator.** The rotation generator sends the first two coordinates to their quarter turn and sets the axial coordinate to zero. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.axialPerp` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:20`).

**Definition: The vorticity field.** The vorticity field is the curl of the spatial velocity gradient. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortField` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:22`).

**Definition: The curl equation's frame remainder.** The frame remainder combines vorticity transport, model stretching, transport of model vorticity, vorticity stretching and frame rotation. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.frameRest` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:24`).

**Definition: One complex vorticity mode.** The vorticity mode is the curl contraction of the corresponding gradient mode. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortMode` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:29`).

**Definition: Pair with the full frame remainder.** The remainder term pairs a vorticity mode with the frame-remainder mode using the piece sign and weight. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.restTerm` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:32`).

**Definition: Vorticity transport in the frame.** This remainder differentiates perturbation vorticity along the model velocity plus radial expansion minus frame rotation. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.transportRest` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:38`).

**Definition: Model gradient acting on vorticity.** This remainder applies the model gradient to the perturbation vorticity. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.stretchRest` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:41`).

**Definition: Transport of model vorticity.** This remainder differentiates model vorticity along the perturbation velocity. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortTransportRest` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:44`).

**Definition: Model vorticity acting on the gradient.** This remainder applies the perturbation gradient to the model vorticity. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortStretchRest` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:47`).

**Definition: Rotation of perturbation vorticity.** The rotation remainder is the frame rate times the axial rotation generator applied to perturbation vorticity. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.rotationRest` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:50`).

**Definition: Pair with one curl remainder.** The partial remainder pairs the vorticity mode with the supplied remainder-field mode using the piece sign and weight. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.restPart` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:53`).

**Theorem: Nonnegative edge charge.** The mode-edge charge is nonnegative under the stated nonnegativity assumptions on its amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.edge_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:56`).

**Theorem: Continuity of second derivative.** Under the stated hypotheses, the spatial second derivative is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.secondDeriv_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:71`).

**Theorem: Continuity of vorticity field.** Under the stated hypotheses, the vorticity field is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortField_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:79`).

**Theorem: The vorticity gradient is continuous.** Under the stated hypotheses, the spatial derivative of the vorticity field is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortGrad_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:83`).

**Theorem: Continuity of axial rotation generator.** Under the stated hypotheses, the axial rotation generator is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.axialPerp_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:92`).

**Theorem: Modes preserve field differences.** Taking a time-angular mode commutes with subtraction of the displayed fields. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.modeVel_sub'` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:98`).

**Theorem: Additivity in the second argument.** The complex pairing distributes over addition in its second argument. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.cdot_add` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:111`).

**Theorem: Subtraction in the second argument.** The complex pairing distributes over subtraction in its second argument. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.cdot_sub` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:115`).

**Theorem: Continuity of derivative.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.fderiv_slice_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:119`).

**Theorem: Smoothness of vorticity field.** Under the stated hypotheses, the vorticity field is smooth. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortField_smooth` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:124`).

**Theorem: The curl-frame remainder is continuous.** Under the stated hypotheses, the full vorticity frame remainder is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.frameRest_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:131`).

**Theorem: Curl contraction equals a vorticity mode.** The curl contraction of a gradient mode equals the velocity-mode construction applied to the vorticity field. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.vortMode_eq_modeVel` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:146`).

**Theorem: Magnitude of a mode-piece sign.** The absolute mode-piece sign equals the indicator of membership in the piece or its reflected partner. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsCore.abs_sgn_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsRestDefs.lean:154`).

### Breakdown.Cert.CoerciveSmoothPieceEpsSeries

Controls the measurability, interchange and finiteness of the nonnegative mode series used to integrate curl-piece estimates.

**Paper context:** Appendix B, Proposition B.1: the curl-piece terms of the multiplier and their frequency gains and error charges.

**Theorem: Exchange the mode sum and integral.** Under the stated measurability assumptions, the nonnegative sum over modes can be interchanged with integration over one time period and space. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.slab_tsum_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:16`).

**Theorem: Measurability on the period slab.** The supplied function is almost everywhere measurable for the restricted unit-slab measure. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.slab_aem` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:28`).

**Theorem: Scale a mode average.** A real constant can be pulled out of the mode average. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.modeAverage_const_mul` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:32`).

**Theorem: Radial scaling of velocity-mode energy.** The squared norm of the radially scaled velocity mode is the original squared mode norm divided by $(1+|y|)^2$. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.cnormSq_modeVel_weighted` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:42`).

**Theorem: Four nonnegative integrals.** The nonnegative integral of the four-term sum is the sum of the four nonnegative integrals. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.lintegral_add4` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:65`).

**Theorem: Finite dominated mode integrals.** The stated domination gives finiteness of the series of nonnegative mode integrals over one spacetime period. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.series_finite_of_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:76`).

**Theorem: Finite total remainder-amplitude energy.** The period integral of the four mode-square sums for vorticity, vorticity gradient, gradient and inverse-radius velocity is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.amplitudeSeries_finite` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:88`).

**Theorem: Finiteness of three scaled integrals.** The nonnegative period integral of the stated three-term constant-weighted sum is finite. Source: `Breakdown.Coercive.Internal.SmoothPieceEps.iterated_add3_lt_top` (`Breakdown/Cert/CoerciveSmoothPieceEpsSeries.lean:182`).

### Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsCurl

Proves the curl and Laplacian commutation identities that turn curl-piece diffusion into a vorticity Laplacian pairing.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Theorem: Smoothness of curl vector.** Under the stated hypotheses, the curl vector is smooth. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.vort_smooth` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsCurl.lean:16`).

**Theorem: The vector Laplacian through two curls.** For the stated divergence-free field, the negative Laplacian equals the curl of its curl. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.curl_fun_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsCurl.lean:29`).

**Theorem: Curl commutes with diffusion.** The curl of the negative-Laplacian field equals the negative Laplacian of the vorticity field. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.vort_negSumSecondPartials` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsCurl.lean:46`).

**Theorem: Modes commute with field negation.** Taking a velocity mode commutes with negating the field. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.modeVel_neg` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsCurl.lean:67`).

### Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsField

Differentiates smooth spatial fields and expresses their second derivatives and Laplacians in coordinate form.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Theorem: Smoothness of derivative.** Under the stated hypotheses, the spatial derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.field_fderiv_smooth` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:18`).

**Theorem: Derivatives of real and imaginary modes.** The real and imaginary velocity modes are twice continuously differentiable, and their first and second derivatives are the corresponding real and imaginary derivative modes. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.field_mode_derivatives` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:23`).

**Theorem: Continuity of second derivatives.** Under the stated hypotheses, the spatial second derivative field is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.field_secondDeriv_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:68`).

**Theorem: The Laplacian from column derivatives.** The second derivative trace is the sum of the displayed column derivatives applied to their matching unit directions. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.trace_of_columns` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:79`).

**Theorem: A real matrix column.** A column of the real matrix is the real vector formed from that complex column. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.reMat_unit` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:94`).

**Theorem: An imaginary matrix column.** A column of the imaginary matrix is the imaginary vector formed from that complex column. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.imMat_unit` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:99`).

**Theorem: Real parts commute with sums.** The sum of real-part vectors is the real-part vector of the sum. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.reVec_sum` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:104`).

**Theorem: Imaginary parts commute with sums.** The sum of imaginary-part vectors is the imaginary-part vector of the sum. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.imVec_sum` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:110`).

**Theorem: Modes commute with the Laplacian.** The real and imaginary velocity modes are twice continuously differentiable and their Laplacians are the real and imaginary parts of the Laplacian mode. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.field_mode_sumSecondPartials` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsField.lean:116`).

### Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsMode

Identifies derivatives of real and imaginary vorticity modes with second-derivative modes and their Laplacians with curl-diffusion modes.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Definition: Cross product with a coordinate vector.** The linear map packages the alternating-symbol contraction with the chosen coordinate unit vector. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.crossMap` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:18`).

**Theorem: Coordinates of the cross-product map.** Each coordinate of the cross-product map is the displayed alternating-symbol contraction with the input vector. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.crossMap_coord` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:21`).

**Theorem: Real curl from real gradient columns.** The real curl vector is the sum of the coordinate cross-product maps applied to the real gradient columns. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.reVec_curl` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:25`).

**Theorem: Imaginary curl from gradient columns.** The imaginary curl vector is the sum of the coordinate cross-product maps applied to the imaginary gradient columns. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.imVec_curl` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:32`).

**Theorem: Real curl from real gradient columns.** The real curl vector is the sum of the coordinate cross-product maps applied to the real gradient columns. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.vortRe_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:39`).

**Theorem: Imaginary curl from gradient columns.** The imaginary curl vector is the sum of the coordinate cross-product maps applied to the imaginary gradient columns. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.vortIm_eq` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:44`).

**Theorem: The real vorticity mode is C2.** The real-part vector of the gradient mode's curl has two continuous spatial derivatives. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.vortRe_contDiff` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:49`).

**Theorem: The imaginary vorticity mode is C2.** The imaginary-part vector of the gradient mode's curl has two continuous spatial derivatives. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.vortIm_contDiff` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:54`).

**Theorem: Differentiate real vorticity modes.** The spatial derivative of the real vorticity mode is the real part of the corresponding curl-gradient second derivative mode. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.fderiv_vortRe_apply` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:59`).

**Theorem: Differentiate imaginary vorticity modes.** The spatial derivative of the imaginary vorticity mode is the imaginary part of the corresponding curl-gradient second derivative mode. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.fderiv_vortIm_apply` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:75`).

**Theorem: Smoothness of derivative.** Under the stated hypotheses, the spatial derivative is smooth. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.joint_fderiv` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:91`).

**Theorem: The negative Laplacian field is smooth.** The negative trace of the perturbation's spatial second derivative is smooth in spacetime. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.negSumSecondPartials_smooth` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:98`).

**Theorem: Continuity of rotated field or vector.** Under the stated hypotheses, the rotated field or vector is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.rot_continuous` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:105`).

**Theorem: Curl modes commute with the Laplacian.** The curl mode of the negative-Laplacian field is minus the combined Laplacians of the real and imaginary vorticity modes. Source: `Breakdown.Coercive.Internal.SmoothPieceEpsSumSecondPartials.curl_sumSecondPartials_mode` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsMode.lean:109`).

### Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsSlice

Obtains spatial square-integrability of the mode fields on almost every time slice for the weighted diffusion integration by parts.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Theorem: The box measure as a restriction.** The time-angular box measure is the restriction of two-dimensional volume to the displayed half-open period rectangle. Source: `Breakdown.Coercive.Internal.ModeSlice.box_eq_restrict` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSlice.lean:14`).

**Theorem: Integrability of function f.** Under the stated hypotheses, the function $f$ is integrable. Source: `Breakdown.Coercive.Internal.ModeSlice.box_integrable` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSlice.lean:20`).

**Theorem: The box has area two pi.** The real measure of the full time-angular box is $2\pi$. Source: `Breakdown.Coercive.Internal.ModeSlice.box_real_univ` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSlice.lean:26`).

**Theorem: Cauchy–Schwarz on the time-angular box.** The square of the box integral is at most $2\pi$ times the box integral of the square. Source: `Breakdown.Coercive.Internal.ModeSlice.box_sq_integral_le` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSlice.lean:32`).

**Theorem: The mode average belongs to L2.** Under the stated hypotheses, the time-angular mode average belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.ModeSlice.memLp_modeAverage_dom` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSlice.lean:54`).

### Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsSliceShift

Transfers spatial and period integrability through time shifts and axial rotations when forming time-angle mode slices.

**Paper context:** Appendix B, Proposition B.1: weight-gradient errors from the curl multiplier paired with diffusion.

**Theorem: Rotation preserves spatial integration.** A nonnegative spatial integral is unchanged by axial rotation of its argument. Source: `Breakdown.Coercive.Internal.ModeSlice.rot_lintegral` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSliceShift.lean:17`).

**Theorem: Shift the time integration window.** The integral of a one-periodic function is unchanged by shifting its unit-length time window. Source: `Breakdown.Coercive.Internal.ModeSlice.periodic_shift_Ioc` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSliceShift.lean:27`).

**Theorem: Average shifted rotating square energy.** Spatial integration of the time-angular averaged shifted squared field equals $2\pi$ times its period square integral. Source: `Breakdown.Coercive.Internal.ModeSlice.lintegral_box_rot_shift` (`Breakdown/Cert/CoerciveSmoothPieceEpsSumSecondPartialsSliceShift.lean:42`).

### Breakdown.Cert.CoerciveSmoothPieceMu

Combines the velocity-piece transport lower bound with its reflected pressure estimate and frequency seminorm.

**Paper context:** Appendix B, Proposition B.1: the velocity-piece contribution to the frequency seminorm and coercive lower bound.

**Theorem: Nonnegative indicator.** A zero-one indicator is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.ind_nonneg'` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:20`).

**Theorem: Nonnegative edge charge.** The mode-edge charge is nonnegative under the stated nonnegativity assumptions on its amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.edgeSum_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:25`).

**Theorem: Nonnegative frame-speed bound.** The supremum of the frame-relative speed is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.frameSpeedSup_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:33`).

**Theorem: Nonnegative piece norm.** The square-root sum of mode squares over a piece is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.pieceNorm_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:37`).

**Theorem: Build a bound from the signs.** The stated real bound, measurability, finiteness and sign conditions supply the split lower-bound predicate. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.splitLowerBound_of_nonpos` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:40`).

**Theorem: The piece frequency seminorm.** The velocity-piece seminorm equals the integral of the piece indicator, spatial weight, absolute frame frequency and squared velocity-mode amplitude. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.seminorm_eq` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:63`).

**Theorem: Separate the solenoidal correction.** The velocity-piece pairing with the forcing splits into its inner-field pairing and its solenoidal correction pairing. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.pairing_additive` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:112`).

**Theorem: Pay for the pressure correction.** Subtracting the integrated piece pressure charge from the inner-field pairing gives a lower bound for the forcing pairing. Source: `Breakdown.Coercive.Internal.SmoothPieceMu.pressure_bound` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:147`).

**Theorem: The smooth velocity-piece estimate.** The transport estimate and reflected pressure bound supply the smooth velocity-piece lower bound. Source: `Breakdown.Coercive.pieceMuEstimateSmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothPieceMu.lean:176`).

### Breakdown.Cert.CoerciveSmoothPieceMuDivergence

Shows that the smooth inner-field combination is divergence-free and orthogonal to gradients, and computes its mode phase under shifts and rotations.

**Paper context:** Appendix B, Proposition B.1: the Leray-projected velocity pairing and control of its pressure correction.

**Theorem: Coordinates commute with sums.** Taking a vector coordinate commutes with a finite sum. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.coord_sum` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:16`).

**Theorem: Coordinates of a scalar multiple.** A coordinate of a real scalar multiple is the scalar times that coordinate. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.coord_smul` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:20`).

**Theorem: Expand a linear-map argument.** A linear map applied to a vector is the sum of the vector's coordinates times the images of the unit vectors. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.clm_expand` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:24`).

**Theorem: Trace is cyclic for two maps.** The trace of a product of two linear maps is unchanged when their order is reversed. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.trace_comp_comm` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:28`).

**Theorem: Differentiate zero divergence.** Differentiating the divergence-free identity gives zero trace for the corresponding directional second derivative. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.second_trace_zero` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:41`).

**Theorem: Time preserves zero divergence.** The spatial divergence of the time derivative vanishes under the stated smoothness and zero-divergence hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.time_deriv_trace_zero` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:61`).

**Theorem: A divergence-free inner field.** Subtracting two copies of the model-gradient action from the smooth right-hand side gives a divergence-free spatial field. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.innerPart_sub_div_zero` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:120`).

**Theorem: Gradients pair to zero.** The integral pairing of the divergence-free field with the potential gradient vanishes under the stated regularity and decay hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.orthogonal_of_div_zero` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:181`).

**Theorem: Opposite velocity modes are conjugate.** For a real field, negating both frequency indices conjugates the velocity-mode coefficient. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.modeVel_neg` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:225`).

**Theorem: Shift and rotation change the phase.** A simultaneous time shift and pulled-back axial rotation multiply each velocity mode by its corresponding unit complex phase. Source: `Breakdown.Coercive.Internal.SmoothPieceMuDivergence.modeVel_shiftRot` (`Breakdown/Cert/CoerciveSmoothPieceMuDivergence.lean:240`).

### Breakdown.Cert.CoerciveSmoothPieceMuHarmonics

Reconstructs the finite model and model-gradient harmonics and bounds their convolution with perturbation velocity modes.

**Paper context:** Appendix B, (B.16) and Proposition B.1: finite harmonic interactions in the velocity-weighted estimate.

**Theorem: Opposite modes have equal amplitude.** The model's velocity-mode amplitude is unchanged when both frequency indices are negated. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.velAmp_neg` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:14`).

**Theorem: A symmetric wave sum is real.** For the stated conjugate-symmetric coefficients and frequency set, the complex Fourier sum equals the embedding of its real part. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.exp_sum_real` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:21`).

**Theorem: Recover the real model orbit.** The pulled-back model field on its time-angle orbit is the finite sum of the real parts of its harmonic waves. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.orbit_expansion_re` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:43`).

**Theorem: Recover the complex model orbit.** The real model field embedded in complex coordinates equals its finite harmonic expansion along the time-angle orbit. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.orbit_expansion` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:61`).

**Theorem: Differentiate a velocity-mode coordinate.** The velocity-mode coordinate has a Fréchet derivative whose coordinate values are the corresponding gradient-mode entries. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.modeVel_hasFDerivAt_local` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:79`).

**Theorem: Recover the real gradient orbit.** Each pulled-back model-gradient entry is the finite sum of the real parts of its gradient-mode waves. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.grad_orbit_expansion_re` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:125`).

**Theorem: Recover the complex gradient orbit.** Each real model-gradient entry embedded in complex space equals its finite harmonic expansion along the time-angle orbit. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.grad_orbit_expansion` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:170`).

**Theorem: Bound the harmonic gradient coupling.** The mode amplitude of the model gradient applied to the perturbation is bounded by the finite convolution of model-gradient amplitudes with shifted perturbation velocity amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceMuHarmonics.stretch_mode_le` (`Breakdown/Cert/CoerciveSmoothPieceMuHarmonics.lean:184`).

### Breakdown.Cert.CoerciveSmoothPieceMuNeg

Bounds the negative velocity-piece remainder, block and pressure charges by finite comparison energy.

**Paper context:** Appendix B, Proposition B.1: the velocity-piece contribution to the frequency seminorm and coercive lower bound.

**Theorem: Indicator bounded by one.** A zero-one indicator is at most one. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.ind_le_one` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:16`).

**Theorem: Nonnegative indicator.** A zero-one indicator is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.ind_nonneg_of` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:20`).

**Theorem: Nonnegative edge charge.** The mode-edge charge is nonnegative under the stated nonnegativity assumptions on its amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.edgeSum_nonneg_of` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:25`).

**Theorem: Count shifted copies of a square sum.** Summing a nonnegative square sequence over every frequency shift in a finite set gives the set's cardinality times the original square sum. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.tsum_shift_sum` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:33`).

**Theorem: Bound the piece-edge loss.** The weighted velocity and harmonic edge interaction is bounded by the stated multiple of gradient energy and inverse-radius velocity energy. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.edge_pointwise` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:46`).

**Theorem: Bound the piece pressure loss.** The pressure loss from the harmonic convolution and weighted velocity is bounded by the stated coefficients times inverse-radius velocity energy. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.press_pointwise` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:87`).

**Theorem: Bound the velocity-piece block loss.** The negative velocity-piece block is controlled by the stated weight, frame and decay constants times gradient energy plus inverse-radius velocity energy. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.block_pointwise_mu` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:169`).

**Theorem: Bounds on a velocity-piece weight.** Each velocity-piece weight is nonnegative, has a uniform radial bound, and has a uniformly bounded radially weighted gradient as specified. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.weight_facts` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:247`).

**Theorem: The piece pressure charge is nonnegative.** The selected sum of the harmonic pressure-convolution square and the balanced weighted velocity square is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.pressure_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:266`).

**Theorem: Finite velocity-piece negative mass.** The period integral of the negative velocity-piece mode remainders and negative block remainder is finite after nonnegative embedding. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.negPart_finite` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:274`).

**Theorem: The piece pressure loss is finite.** The mode-summed piece pressure charge has finite nonnegative period integral. Source: `Breakdown.Coercive.Internal.SmoothPieceMuNeg.pressureLoss_finite` (`Breakdown/Cert/CoerciveSmoothPieceMuNeg.lean:358`).

### Breakdown.Cert.CoerciveSmoothPieceMuReflect

Bounds the velocity-piece pairing with the solenoidal reflection by the eta-balanced piece pressure loss.

**Paper context:** Appendix B, Proposition B.1: the Leray-projected velocity pairing and control of its pressure correction.

**Theorem: Radial scaling of velocity-mode energy.** The squared norm of the radially scaled velocity mode is the original squared mode norm divided by $(1+|y|)^2$. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.cnormSq_scaled` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:19`).

**Theorem: Balance a pairing with eta.** The weighted imaginary pairing is bounded by the displayed pair of squared norms weighted by $\eta$ and its reciprocal. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.pointwise_absorb` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:32`).

**Definition: Pressure charge on a velocity piece.** The density adds the squared model-gradient convolution divided by twice $\eta$ and the matching weighted velocity square. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.pressDensity` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:67`).

**Definition: Reflected-field pressure charge.** The reflected density replaces the model-gradient convolution by the reflected field's mode square in the same $\eta$-balanced charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.reflDensity` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:73`).

**Theorem: The two indicator values.** A proposition's indicator is either zero or one. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.ind_cases` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:79`).

**Theorem: Magnitude of a mode-piece sign.** The absolute mode-piece sign equals the indicator of membership in the piece or its reflected partner. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.abs_sgn` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:85`).

**Theorem: Split a nonnegative weighted quotient.** The nonnegative embedding of the weighted quotient-plus-term equals the sum of the two separately embedded weighted terms under the stated sign assumptions. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.ofReal_split` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:90`).

**Theorem: Bound the reflected correction.** The velocity-piece pairing with the reflected solenoidal correction is bounded below by the negative integrated piece pressure charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuReflect.reflected_pairing_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuReflect.lean:97`).

### Breakdown.Cert.CoerciveSmoothPieceMuSeminorm

Proves finiteness of each velocity-piece frequency seminorm by controlling the absolute frame frequency with temporal and angular indices.

**Paper context:** Appendix B, (B.15) and Proposition B.1: rotating-frame frequencies and the finite frequency seminorm.

**Theorem: Mode-piece sign bounded by one.** The absolute value of a mode-piece sign is at most one. Source: `Breakdown.Coercive.Internal.SmoothPieceMuSeminorm.sgn_abs_le_one` (`Breakdown/Cert/CoerciveSmoothPieceMuSeminorm.lean:14`).

**Theorem: Bound the frame frequency.** The absolute rotating-frame frequency is at most the sum of the absolute mode indices times $2\pi/P+|a|$. Source: `Breakdown.Coercive.Internal.SmoothPieceMuSeminorm.frameFreq_abs_le` (`Breakdown/Cert/CoerciveSmoothPieceMuSeminorm.lean:18`).

**Theorem: The velocity-piece seminorm is finite.** The velocity-piece frequency seminorm is finite under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothPieceMuSeminorm.seminorm_finite` (`Breakdown/Cert/CoerciveSmoothPieceMuSeminorm.lean:33`).

### Breakdown.Cert.CoerciveSmoothPieceMuSumSecondPartials

Bounds the imaginary weighted velocity-diffusion pairing by a single weight-gradient error on almost every time slice.

**Paper context:** Appendix B, Proposition B.1: the weighted imaginary diffusion pairing in the velocity estimate.

**Theorem: Modes preserve field negation.** Negating a real field negates every coordinate of its velocity-mode coefficient. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.modeVel_neg_apply` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:16`).

**Theorem: Imaginary pairing in real components.** The real part of the imaginary weighted complex pairing is the stated antisymmetric pairing of its real and imaginary vector components. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.re_I_cdot_eq` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:27`).

**Theorem: Recover the real and imaginary energy.** The complex squared norm equals the squared norms of the supplied real and imaginary vectors, with the allowed sign convention on the imaginary part. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.cnormSq_parts` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:35`).

**Theorem: Recover the real and imaginary energy.** The complex squared norm equals the squared norms of the supplied real and imaginary vectors, with the allowed sign convention on the imaginary part. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.cnormSq_neg_parts` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:43`).

**Theorem: Read a coordinate expansion.** The indicated coordinate of a sum of coordinate unit vectors equals its coefficient. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.sum_smul_unit_apply` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:51`).

**Theorem: Bound the weighted derivative flux.** The absolute derivative-flux sum is bounded by the weight-gradient norm times the two combined square-root energies. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.flux_sum_le` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:55`).

**Theorem: Absorb a radial product into squares.** The supplied coefficient bound controls the weighted product by half the stated sum of an unweighted square and an inverse-radius square. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.weighted_prod_le` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:84`).

**Theorem: Bound the matrix operator norm.** The squared operator norm is at most three times the sum of squared column norms. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.opNorm_sq_le` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:100`).

**Theorem: Continuity of second derivative trace.** Under the stated hypotheses, the second derivative trace is continuous. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.continuous_ssp` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:110`).

**Theorem: Bound an antisymmetric real pairing.** The absolute difference of the two real inner products is at most the sum of the two products of norms. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.inner_pair_le` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:117`).

**Theorem: Diffusion costs one weight gradient.** The imaginary weighted diffusion pairing and its weight-gradient bound are spatially integrable, and the absolute pairing integral is bounded by that weight-gradient integral. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.slice_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:121`).

**Theorem: Diffusion control on almost every slice.** For almost every time in the unit period, the imaginary weighted diffusion pairing is integrable and bounded in absolute integral by the weight-gradient, gradient-mode and velocity-mode product. Source: `Breakdown.Coercive.Internal.ModeSumSecondPartials.sumSecondPartials_mode_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuSumSecondPartials.lean:292`).

### Breakdown.Cert.CoerciveSmoothPieceMuTransport

Splits frame advection into within-piece and edge interactions, controls their sums, and assembles the velocity-piece transport lower bound.

**Paper context:** Appendix B, Proposition B.1: the velocity-piece contribution to the frequency seminorm and coercive lower bound.

**Definition: The axial rotation generator.** The rotation generator sends the first two coordinates to their quarter turn and sets the axial coordinate to zero. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.axisTurn` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:23`).

**Definition: Transport, diffusion and advection.** The inner field combines similarity transport, the negative Laplacian and advection of the perturbation by the model field. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.innerField` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:25`).

**Definition: The axial rotation generator.** The rotation generator sends the first two coordinates to their quarter turn and sets the axial coordinate to zero. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turnDir` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:28`).

**Definition: Advection in the moving frame.** The frame-advection field differentiates the perturbation along the model velocity plus radial expansion minus frame rotation. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frameAdvection` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:30`).

**Definition: The negative spatial Laplacian.** This field is the negative trace of the spatial second derivative. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.negSumSecondPartialsField` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:33`).

**Definition: A signed velocity-piece pairing.** The field term pairs the velocity mode with the supplied field mode using the piece sign and spatial weight. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.fieldTerm` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:36`).

**Definition: The frame-rotation pairing.** The turn term pairs the velocity mode with its axial rotation generator, weighted by the piece sign, weight and frame rate. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turnTerm` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:40`).

**Definition: One velocity-piece frequency term.** The frequency term is the piece indicator times its weight, the absolute frame frequency and the squared velocity amplitude. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.freqTerm` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:45`).

**Definition: Integrated velocity-piece frequency.** The frequency series integrates the nonnegative sum of velocity-piece frequency terms over one period and space. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.freqSeries` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:49`).

**Definition: Integrated velocity edge charges.** The edge series integrates velocity amplitudes paired with the off-piece gradient charges. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.edgeSeries` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:52`).

**Definition: Integrated rotation block charge.** The turn block integrates the piece's squared velocity norm times its spatial weight and absolute frame rate. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turnBlock` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:56`).

**Definition: Integrated frame-advection charge.** The advection block integrates the frame-speed bound times the weighted gradient and velocity piece norms. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advectionBlock` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:60`).

**Definition: Integrated weight-gradient charge.** The diffusion block integrates the weight-gradient norm times the gradient and velocity piece norms. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartialsBlock` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:65`).

**Definition: The time derivative field.** The time-derivative field differentiates the velocity with respect to its time variable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.timeDerivField` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:70`).

**Definition: The angular derivative field.** The angular derivative field differentiates the velocity along the axial rotation generator. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turnField` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:72`).

**Theorem: Time differentiation multiplies a mode.** The mode of the time derivative is the original mode multiplied by the imaginary temporal frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.time_mode` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:75`).

**Theorem: Angular differentiation of vector modes.** The angular derivative mode equals imaginary angular frequency times the velocity mode plus the rotation-generator correction. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turn_mode` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:80`).

**Theorem: Decompose the transport field.** The inner field decomposes into time derivative, half the velocity, relative-frame advection, angular transport and the negative Laplacian, with model waves separated where displayed. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.innerField_decomp` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:86`).

**Theorem: Decompose the transport field.** The inner field decomposes into time derivative, half the velocity, relative-frame advection, angular transport and the negative Laplacian, with model waves separated where displayed. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.rotated_decomp` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:93`).

**Theorem: Continuity of time-derivative field.** Under the stated hypotheses, the time-derivative field is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.timeDerivField_continuous` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:104`).

**Theorem: Continuity of derivative.** Under the stated hypotheses, the spatial derivative is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.gradSlice_continuous` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:117`).

**Theorem: Continuity of negative Laplacian field.** Under the stated hypotheses, the negative Laplacian field is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.negSumSecondPartialsField_continuous` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:122`).

**Theorem: The orbit operator value is continuous.** The shifted field of operators applied to the parameter-dependent vector and pulled back by rotation has continuous time-angle coordinates. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.applied_integrand_continuous` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:131`).

**Theorem: Isolate the rotating-frame frequency.** The transport mode separates into the imaginary frame-frequency term, component rotation, half the velocity, bounded advection terms and diffusion. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.mode_split_of` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:143`).

**Definition: The complete frame-advection charge.** The advection loss adds the rotation block, frame-speed block and off-piece edge charges. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advectionLoss` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:201`).

**Theorem: Opposite modes have opposite frequency.** Negating both mode indices negates the rotating-frame frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frameFreq_neg` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:209`).

**Theorem: Signed frame frequency is positive.** On a valid mode piece, its sign times the frame frequency equals the membership indicator times the absolute frame frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sgn_mul_frameFreq` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:215`).

**Theorem: Expand the frame-frequency pairing.** The imaginary pairing with the decomposed transport field becomes the frequency-weighted square plus the rotation, advection and diffusion pairings. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.term_expand` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:233`).

**Theorem: Split the piece transport pairing.** The inner-field pairing density is the sum of its frame-frequency, component-rotation, frame-advection and diffusion contributions. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.fieldTerm_split` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:245`).

**Theorem: A sum under a nonnegative integral.** The displayed sum of nonnegative iterated integrals is at most the iterated integral of the sum. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.lintegral_three_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:269`).

**Theorem: Cauchy–Schwarz on a mode piece.** The nonnegative sum of modewise products over the piece is at most the common coefficient times the two piece norms. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.piece_sum_mul_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:276`).

**Theorem: Recover a real nonnegative series.** A summable nonnegative real series equals the real value of its extended-nonnegative series. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.tsum_eq_toReal_ofReal` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:312`).

**Theorem: Norm over a mode piece is ae measurable.** Under the stated hypotheses, the norm over a mode piece is almost everywhere measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.aem_pieceNorm_of` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:317`).

**Theorem: Off-piece edge charge is ae measurable.** Under the stated hypotheses, the off-piece edge charge is almost everywhere measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.aem_edgeSum` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:331`).

**Theorem: A radial bound for the frame speed.** The frame-relative speed is at most the model bound plus $(1/2+2|a|)$ times the spatial norm. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frame_term_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:355`).

**Theorem: Measurability of frame speed.** Under the stated hypotheses, the supremum of the frame-relative speed is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frameSpeedSup_measurable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:378`).

**Theorem: Magnitude of a mode-piece sign.** The absolute mode-piece sign equals the indicator of membership in the piece or its reflected partner. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.abs_sgn_eq_ind` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:404`).

**Theorem: Nonnegative indicator.** A zero-one indicator is nonnegative. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.ind_nonneg_of` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:409`).

**Theorem: Indicator bounded by one.** A zero-one indicator is at most one. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.ind_le_one_of` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:412`).

**Theorem: Bound the component-rotation term.** The absolute component-rotation pairing is at most the piece weight times the absolute frame rate times the selected velocity-mode square. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turnTerm_abs_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:415`).

**Theorem: Bound the weighted field pairing.** The absolute piece-weighted imaginary pairing is at most the weight times the selected product of the two velocity-mode amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.fieldTerm_abs_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:444`).

**Definition: The retained advection convolution.** The inner mode retains the model-velocity and perturbation-gradient convolution terms whose shifted frequency remains in the selected piece, together with radial and rotational advection. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.innerMode` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:458`).

**Definition: The discarded advection convolution.** The outer mode retains precisely the model-velocity and perturbation-gradient convolution terms whose shifted frequency falls outside the selected piece. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.outerMode` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:465`).

**Theorem: Nonnegative edge charge.** The mode-edge charge is nonnegative under the stated nonnegativity assumptions on its amplitudes. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.edgeSum_nonneg` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:470`).

**Theorem: Rotate the axial generator.** Applying the axial rotation generator before or after axial rotation gives the same vector. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turnDir_axialRot` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:478`).

**Theorem: Pull back the frame velocity.** Pulling back the frame velocity rotates the model field while retaining the radial vector and axial rotation-generator terms at the original point. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frame_vector_rot` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:483`).

**Theorem: Continuous complex orbit matrix entries.** The pulled-back matrix entry on the time-angle orbit, embedded in complex numbers, depends continuously on the orbit parameters. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.clm_orbit_continuous` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:492`).

**Theorem: Modes of a matrix-vector product.** The mode of the displayed matrix-vector product is the mean contribution plus the convolution of the finite coefficient modes with shifted input modes. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.clm_mode_product` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:500`).

**Theorem: Bound interactions leaving a piece.** The outer advection mode is bounded by the finite harmonic sum of model velocity amplitude times perturbation-gradient amplitude at shifted frequencies outside the piece. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.outerMode_le_sum` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:551`).

**Theorem: Orbit Fourier energies are summable.** The series of squared norms of the orbit function's Fourier coefficients is summable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.orbit_mode_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:572`).

**Theorem: Integrate a periodic Fourier phase.** The complex exponential integrates to the interval length at zero frequency and to zero at each permitted nonzero frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.integral_exp_linear` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:595`).

**Theorem: Fourier coefficients of a constant.** The constant-one function has coefficient one at the zero mode and zero at every other mode. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.mode_one` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:616`).

**Theorem: The two coefficients of a real wave.** A real Fourier wave has half its complex coefficient at its frequency and half the conjugate coefficient at the opposite frequency. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.mode_re_exp` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:654`).

**Theorem: Parseval on the time-angle torus.** For the continuous periodic input, the sum of squared Fourier coefficient norms equals its time-angle square integral divided by $2\pi$. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.torus_squareSum_cont` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:672`).

**Definition: A finite gradient Fourier sum.** The truncated gradient sums the real parts of the selected gradient modes with their Fourier phases. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.truncGrad` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:697`).

**Definition: The reconstructed frame velocity.** The orbit-frame velocity adds radial expansion to the finite model-field Fourier reconstruction and subtracts the frame rate times the axial rotation generator. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.orbitFrame` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:702`).

**Definition: Truncated gradient against frame flow.** The truncated product contracts the finite gradient reconstruction with the reconstructed frame velocity. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.truncProduct` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:706`).

**Theorem: The truncated gradient is continuous.** Under the stated hypotheses, the truncated gradient reconstruction is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.truncGrad_continuous` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:710`).

**Theorem: A continuous truncated frame product.** Under the stated hypotheses, the truncated gradient-frame product is continuous. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.truncProduct_continuous` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:715`).

**Theorem: Modes commute with finite sums.** The mode average of the finite sum equals the sum of the mode averages. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.modeAverage_finset_sum` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:720`).

**Theorem: Reindex a symmetric finite set.** Negation reindexes the finite sum over the stated symmetric frequency set without changing its value. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sum_neg_index` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:733`).

**Theorem: Modes of a truncated gradient.** The finite gradient reconstruction retains the original gradient coefficient on the selected modes and is zero on all other modes. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.truncGrad_mode` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:738`).

**Theorem: A product couples shifted modes.** The selected product coefficient is the frame term plus the positive and negative harmonic shifts with their one-half wave coefficients. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.truncProduct_term` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:764`).

**Theorem: Recover the within-piece product.** Under the mode-support hypotheses, the coefficient of the finite product reconstruction equals the within-piece advection mode. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.truncProduct_mode` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:796`).

**Theorem: Sum inside the time-angle integral.** The nonnegative time-angle integral of a finite sum equals the sum of its integrals. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.lintegral_box_sum` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:822`).

**Theorem: Scale the time-angle integral.** A constant nonnegative factor can be pulled out of the nonnegative time-angle integral. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.lintegral_box_const_mul` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:832`).

**Theorem: A pointwise bound controls mode energy.** The supplied pointwise square bound gives the corresponding bound on the finite sum of output-mode squares by the input-mode square sum. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.modeSq_sum_le_of_pointwise` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:837`).

**Theorem: Rotate a difference.** Axial rotation carries the stated vector difference to the difference of the rotated vectors. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.rot_sub_of` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:872`).

**Theorem: Rotate the axial generator.** Applying the axial rotation generator before or after axial rotation gives the same vector. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turnDir_rot` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:876`).

**Theorem: Frame velocity on the orbit.** The pulled-back frame velocity is the pulled-back model field plus the original radial vector minus the original axial rotation-generator term. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.rot_frame_eq` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:880`).

**Theorem: Decompose a frame-transport mode.** The transport mode splits into its imaginary frame-frequency term, component rotation, half-velocity term, frame-advection mode and diffusion mode. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.mode_split` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:905`).

**Theorem: The piece frequency density integrates.** Under the stated hypotheses, the velocity-piece frequency term is integrable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.freq_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:912`).

**Theorem: The frame-advection field is in L2.** The frame-advection field is measurable, one-periodic and square-integrable over one time period and space. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frameAdvection_square` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:955`).

**Theorem: The frame-advection pairing integrates.** The piece-weighted pairing of the velocity mode with the frame-advection mode is integrable on the period slab. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frameAdvection_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1034`).

**Theorem: Integrability of rotation pairing term.** Under the stated hypotheses, the rotation pairing term is integrable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.turn_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1110`).

**Theorem: Integrable rotation-advection pairings.** The sum of the component-rotation and frame-advection mode pairings is integrable on the period slab. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1175`).

**Theorem: The piece diffusion pairing integrates.** The piece-weighted pairing of the velocity mode with its negative-Laplacian mode is integrable on the period slab. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1180`).

**Theorem: Integrable transport remainders.** The component-rotation plus advection pairing and the diffusion pairing are integrable on the unit spacetime slab. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.rest_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1247`).

**Theorem: Integrable transport contributions.** The frequency, rotation-plus-advection and diffusion pairing densities are integrable on the unit spacetime slab. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.pairing_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1253`).

**Theorem: Sum the frequency contributions.** The integrated mode-frequency contributions form a summable real series whose sum is the real value of the nonnegative frequency charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.freq_tsum_eq` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1260`).

**Theorem: Dominate each diffusion pairing.** A uniform constant bounds each absolute diffusion-pairing density by four times the stated sum of weighted velocity-mode and Laplacian-mode squares. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_term_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1295`).

**Theorem: Integrated diffusion modes are summable.** The series of integrated piece diffusion pairings is summable over the mode indices. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_family_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1343`).

**Theorem: Dominate rotation and advection.** A uniform nonnegative constant bounds each absolute rotation-plus-advection pairing by the weighted velocity-mode and frame-advection-mode squares. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_term_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1365`).

**Theorem: Summable absolute advection integrals.** The integrals of the absolute rotation-plus-advection mode pairings form a summable series. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_norm_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1464`).

**Theorem: Integrated advection modes are summable.** The series of integrated component-rotation plus frame-advection pairings is summable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_family_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1485`).

**Theorem: Sum all transport contributions.** The integrated frequency, rotation-plus-advection and diffusion contributions are summable, and the frequency sum equals the real nonnegative frequency charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.pairing_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1495`).

**Theorem: Decompose the integrated pairing.** The piece-weighted inner-field pairing equals the real frequency charge plus the rotation-and-advection series and the diffusion series. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.pairing_decomp` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1502`).

**Theorem: Velocity-mode squares are summable.** For almost every point of the stated measure space, the velocity-mode squares form a summable series. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.piece_vel_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1539`).

**Theorem: The required mode-amplitude squares sum.** For almost every spacetime point, the displayed gradient, vorticity and derivative amplitude-square series are summable. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.amp_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1569`).

**Theorem: Split advection across a piece edge.** The frame-advection mode is the sum of its within-piece and outside-piece interactions. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frameAdvection_mode_split` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1595`).

**Theorem: The edge charge bounds outer advection.** The amplitude of the outside-piece advection mode is at most the corresponding harmonic edge charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.outerMode_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1625`).

**Theorem: The velocity edge series is summable.** The velocity-mode amplitude times the harmonic edge charge involving model velocity and shifted perturbation-gradient amplitudes forms a summable series. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.edge_summable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1663`).

**Theorem: Bound the orbit frame speed.** The sum of squared coordinates of the orbit frame velocity is at most the squared frame-speed supremum. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.orbitFrame_sq_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1706`).

**Theorem: Bound finite within-piece advection.** The finite sum of within-piece advection-mode squares is at most the squared frame-speed supremum times the selected gradient-mode square sum. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.inner_finset_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1757`).

**Theorem: Control the within-piece interaction.** The selected velocity-amplitude and inner-advection-amplitude series is summable and is bounded by the frame-speed supremum times the piece gradient and velocity norms. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.innerMode_piece_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1806`).

**Theorem: Bound full advection on a piece.** For almost every spacetime point, the selected velocity-advection amplitude series is summable and is bounded by its within-piece norm product plus the harmonic edge charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.frame_piece_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1914`).

**Theorem: A lower bound for advection pairings.** For almost every spacetime point, the rotation-plus-advection pairing series is summable and its sum is bounded below by the negative advection loss. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_pointwise` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:1970`).

**Theorem: Exchange advection sums and integrals.** The advection pairing sum is integrable, and summing the modewise integrals gives the integral of the mode sum. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_swap` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2011`).

**Theorem: Integrate the advection loss.** The advection loss is integrable and its integral is bounded by the edge, component-rotation and within-piece advection charges. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_loss_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2034`).

**Theorem: The integrated advection lower bound.** The integrated rotation-plus-advection series is bounded below by the negative sum of its edge, rotation and within-piece advection charges. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.advection_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2118`).

**Theorem: Measurable spatial diffusion pairings.** The spatial integral of each piece diffusion pairing is almost everywhere strongly measurable in time on the unit period. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_term_measurable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2136`).

**Theorem: The diffusion gradient error integrates.** The piece weight-gradient norm times the gradient-mode and velocity-mode amplitudes is integrable on the period slab. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_weight_integrable` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2153`).

**Theorem: A lower bound for one diffusion mode.** A mode's imaginary diffusion pairing is bounded below by the negative integral of the selected weight-gradient, gradient-amplitude and velocity-amplitude product. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_mode_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2202`).

**Theorem: Sum the diffusion error charges.** The modewise diffusion error charges form a summable series whose sum is bounded by the real diffusion block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_series_le` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2265`).

**Theorem: The integrated diffusion lower bound.** The integrated diffusion-pairing series is bounded below by the negative real value of the diffusion block charge. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.sumSecondPartials_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2351`).

**Theorem: The velocity-piece transport bound.** The frequency charge minus the edge and negative block losses is bounded above by the piece-weighted inner-field pairing. Source: `Breakdown.Coercive.Internal.SmoothPieceMuTransport.transport_bound` (`Breakdown/Cert/CoerciveSmoothPieceMuTransport.lean:2365`).

### Breakdown.Cert.CoerciveSmoothPiecePairingSplit

Interchanges finite piece sums and mode integrals and identifies the full multiplier pairing with its base, curl-piece and velocity-piece parts.

**Paper context:** Appendix B, (B.14) and Proposition B.1: interpretation and splitting of the multiplier pairing.

**Theorem: Move radial damping out of a pairing.** Pairing the original velocity mode equals one plus the radius times the pairing with its radially damped mode. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.cdot_modeVel_scaled` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:19`).

**Theorem: Combine the two real weights.** The two real factors in the imaginary complex pairing can be combined into a single real weight. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.mul_weight` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:25`).

**Theorem: Use the inverse-radius scaled field.** The velocity pairing equals the mode sum formed from the inverse-radius scaled field and the compensating radial weight. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.muPairing_eq_scaled` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:30`).

**Definition: The combined piece pairing form.** The piece form adds all signed curl and velocity piece pairings and then sums their mode integrals. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.pieceForm` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:35`).

**Definition: The vorticity field.** The vorticity field is the curl of the spatial velocity gradient. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.curlField` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:43`).

**Theorem: Mode-piece sign bounded by one.** The absolute value of a mode-piece sign is at most one. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.abs_sgn_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:45`).

**Theorem: A sign preserves a uniform bound.** Multiplication by a mode-piece sign preserves the supplied uniform absolute bound on the spatial weight. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.sgnWeight_bound` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:49`).

**Theorem: A signed spatial weight is measurable.** Multiplying the measurable spatial weight by the fixed mode-piece sign gives a measurable function. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.sgnWeight_measurable` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:55`).

**Theorem: Sum the finitely many piece pairings.** The mode sum of the finite curl-piece and velocity-piece contributions equals the two finite sums of their modewise pairings. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.tsum_pieces` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:59`).

**Definition: The signed curl-piece weight.** The curl-piece weight multiplies its spatial weight by the mode-piece sign. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.epsWt` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:117`).

**Definition: The rescaled velocity-piece weight.** The velocity-piece weight multiplies its spatial weight and piece sign by one plus the spatial norm. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.muWt` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:120`).

**Theorem: Bound each curl-piece weight.** Every signed curl-piece weight is bounded in absolute value by the admissible curl-weight supremum. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.epsWt_bound` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:123`).

**Theorem: Signed curl-piece weight is measurable.** Under the stated hypotheses, the signed curl-piece weight is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.epsWt_measurable` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:130`).

**Theorem: Bound the rescaled velocity weights.** A common constant bounds every signed and radially rescaled velocity-piece weight in absolute value. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.muWt_bound` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:134`).

**Theorem: The rescaled piece weight is measurable.** Under the stated hypotheses, the rescaled velocity-piece weight is measurable. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.muWt_measurable` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:147`).

**Theorem: Write the piece form as mode sums.** The piece form is the finite sum of curl-mode pairings and rescaled velocity-mode pairings with their respective piece weights. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.pieceForm_eq` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:152`).

**Theorem: Pass to the limit in the piece form.** The piece form evaluated on the approximating test fields converges to the form with the prescribed curl and velocity limits. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.pieceForm_tendsto` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:176`).

**Theorem: Separate curl and velocity pieces.** The piece form equals the sum of its curl-piece pairings and velocity-piece pairings. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.mode_tsum_split` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:207`).

**Theorem: Expand the multiplier pairing.** The forcing-multiplier pairing equals the base Laplacian pairing plus the finite curl-piece and velocity-piece pairings. Source: `Breakdown.Coercive.Internal.SmoothPieceSplit.multiplier_pairing` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:223`).

**Theorem: Split the smooth piece pairing.** The smooth piece-multiplier pairing splits into its Laplacian term and finite sums of curl and velocity piece pairings. Source: `Breakdown.Coercive.piecePairingSplitSmoothHolds_of` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplit.lean:268`).

### Breakdown.Cert.CoerciveSmoothPiecePairingSplitDensity

Constructs periodic test-field approximations that converge in velocity and curl by spatial cutoff and solenoidal projection.

**Paper context:** Appendix B, (B.14) and Proposition B.1: interpretation and splitting of the multiplier pairing.

**Definition: A bump between radii one and two.** The fixed smooth bump uses inner radius one and outer radius two. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.unitBump` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:17`).

**Definition: An expanding spatial cutoff.** The cutoff evaluates the fixed bump on the spatial argument divided by the chosen radius. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cut` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:19`).

**Definition: The spatially cut-off field.** The cutoff field multiplies the supplied field by the expanding smooth spatial cutoff. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cutField` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:21`).

**Theorem: Smoothness of cutoff.** Under the stated hypotheses, the spatial cutoff is smooth. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cut_contDiff` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:23`).

**Theorem: Nonnegativity of cutoff.** The spatial cutoff is nonnegative under the stated hypotheses. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cut_nonneg` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:26`).

**Theorem: The cutoff is bounded above by one.** The spatial cutoff takes values at most one. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cut_le_one` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:28`).

**Theorem: The cutoff vanishes far away.** The cutoff at index $n$ vanishes outside radius $2(n+1)$. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cut_far` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:30`).

**Theorem: The cutoff is eventually locally one.** At every fixed spatial point, all sufficiently large cutoffs equal one on a neighbourhood of that point. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cut_eventually_one` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:39`).

**Theorem: Uniformly bounded cutoff gradients.** A common nonnegative constant bounds the gradient norm of every cutoff at every spatial point. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cut_fderiv_bound` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:57`).

**Theorem: C1 regularity of cut-off field.** Under the stated hypotheses, the cut-off field has continuous derivatives through order $1$. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cutField_contDiff` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:85`).

**Theorem: Time periodicity of cut-off field.** Under the stated hypotheses, the cut-off field has period one in time. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cutField_periodic` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:89`).

**Theorem: A uniformly supported cutoff field.** For each cutoff index, the cut-off field vanishes beyond one spatial radius uniformly in time. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cutField_far` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:94`).

**Theorem: Curl respects gradient differences.** The difference of two curl vectors is the curl vector of the matrix difference. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.curlVec_sub` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:100`).

**Theorem: Bound the square of a sum.** The square of a real sum is at most twice the sum of the two squares. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.sq_add_le_two` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:108`).

**Theorem: A three-point square bound.** The squared distance from the first vector to the third is at most twice the sum of the squared distances through the middle vector. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.norm_sub_sq_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:110`).

**Theorem: A period L2 triangle bound.** The squared period distance between the first and third fields is at most twice the sum of the two squared period distances through the intermediate field. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.periodLIntegral_triangle` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:115`).

**Theorem: Spatial truncation converges in L2.** The cut-off fields converge to the original field in the squared period $L^2$ integral. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.cutField_tendsto` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:140`).

**Theorem: Differentiate the cutoff error.** The derivative error from multiplying by the cutoff is the cutoff-minus-one times the original derivative plus the cutoff gradient times the field. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.fderiv_cutField_sub` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:170`).

**Theorem: The cut-off curls converge in L2.** The curls of the cut-off fields converge to the original curl in the squared period $L^2$ integral. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.curl_cutField_tendsto` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:177`).

**Theorem: Solenoidal parts preserve differences.** The difference of the two solenoidal parts is a solenoidal part of the difference of their original fields. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.solenoidal_sub` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:254`).

**Theorem: Solenoidal projection contracts distance.** The squared period $L^2$ distance between two solenoidal parts is at most the squared distance between their original fields. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.solenoidal_diff_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:277`).

**Theorem: Approximate the field and its curl.** There is a sequence of periodic test fields converging in period $L^2$ to the solenoidal part, with curls converging in period $L^2$ to the original smooth field's curl. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.curlGraphDensityL2` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitDensity.lean:303`).

### Breakdown.Cert.CoerciveSmoothPiecePairingSplitWeight

Rescales velocity by one plus the radius and supplies bounded piece weights and finite curl energies for the pairing split.

**Paper context:** Appendix B, (B.14) and Proposition B.1: interpretation and splitting of the multiplier pairing.

**Definition: Velocity with inverse radial weight.** The weighted field is the velocity divided by one plus the distance from the origin. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.scaledField` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:17`).

**Theorem: Rotate a scalar multiple.** A coordinate of the rotation of a scalar multiple equals the scalar times the rotated coordinate. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.axialRot_smul_coord` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:19`).

**Theorem: A radial weight commutes with modes.** Multiplying the field by the inverse radial weight multiplies its mode coefficient by the same weight. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.modeVel_scaled` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:23`).

**Theorem: Recover the unscaled velocity mode.** Multiplying a velocity mode of the inverse-radius scaled field by one plus the radius recovers the original velocity mode. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.modeVel_eq_scaled` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:41`).

**Theorem: Domination gives a finite integral.** The supplied pointwise domination by a finite nonnegative period integral makes the displayed period integral finite. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.periodLIntegral_lt_top_of_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:46`).

**Theorem: The scaled field lies in period L2.** The inverse-radius scaled smooth perturbation is a measurable, time-periodic field with finite period $L^2$ energy. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.scaledField_square` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:58`).

**Theorem: Squared matrix norm bound.** The sum of squared column norms is at most three times the squared operator norm. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.matSq_le_three_sq` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:73`).

**Theorem: Finite perturbation-gradient energy.** The sum of squared column norms of the perturbation gradient has finite period integral. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.perturbation_fderiv_sq` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:82`).

**Theorem: Alternating symbol bound.** The alternating symbol has absolute value at most one. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.abs_alternatingSymbol_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:89`).

**Theorem: Curl from the operator norm.** The curl norm is at most twenty-seven times the input operator norm. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.norm_curlVec_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:92`).

**Theorem: Bound curl by matrix energy.** The squared curl-vector norm is at most $2187$ times the sum of squared column norms of the gradient matrix. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.sq_norm_curlVec_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:122`).

**Theorem: Square-integrable derivatives give curl.** The stated field and derivative hypotheses make the curl a measurable, time-periodic field with finite period $L^2$ energy. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.curl_square_of_fderiv` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:128`).

**Theorem: A radial rescaling bound.** The supplied radial decay bound implies that one plus the radius times the function is at most twice the stated constant. Source: `Breakdown.Coercive.Internal.SmoothWeightSplit.one_add_norm_mul_le` (`Breakdown/Cert/CoerciveSmoothPiecePairingSplitWeight.lean:136`).

### Breakdown.Cert.CoerciveSmoothPressure

Proves modewise orthogonality of the solenoidal projection and uses reflection to split the smooth forcing while preserving each mode energy.

**Paper context:** Appendix B, Proposition B.1: the Leray-projected velocity pairing and control of its pressure correction.

**Theorem: Subtraction in the first argument.** The complex pairing distributes over subtraction in its first argument. Source: `Breakdown.Coercive.Internal.SmoothPressure.cdot_sub_left` (`Breakdown/Cert/CoerciveSmoothPressure.lean:15`).

**Theorem: Additivity in the second argument.** The complex pairing distributes over addition in its second argument. Source: `Breakdown.Coercive.Internal.SmoothPressure.cdot_add_right` (`Breakdown/Cert/CoerciveSmoothPressure.lean:21`).

**Theorem: Expand a three-vector square.** The squared norm after two subtractions equals the first difference's squared norm plus the last vector's squared norm and the two real cross terms. Source: `Breakdown.Coercive.Internal.SmoothPressure.cnormSq_sub_sub` (`Breakdown/Cert/CoerciveSmoothPressure.lean:27`).

**Theorem: Zero squared norm forces zero.** A complex vector with zero squared norm is the zero vector. Source: `Breakdown.Coercive.Internal.SmoothPressure.eq_zero_of_cnormSq_eq_zero` (`Breakdown/Cert/CoerciveSmoothPressure.lean:32`).

**Theorem: Pair two square-integrable fields.** The inner product of the two square-integrable fields is integrable on the displayed measure space. Source: `Breakdown.Coercive.Internal.SmoothPressure.integrable_inner` (`Breakdown/Cert/CoerciveSmoothPressure.lean:38`).

**Theorem: Parseval for a real field pairing.** The integrated real pairings of matching velocity modes sum to the real spacetime inner product of the two fields. Source: `Breakdown.Coercive.Internal.SmoothPressure.hasSum_re_cdot` (`Breakdown/Cert/CoerciveSmoothPressure.lean:57`).

**Theorem: Modes respect almost-everywhere sums.** If the fields agree almost everywhere with the stated sum, their velocity modes satisfy the corresponding addition identity almost everywhere on the period slab. Source: `Breakdown.Coercive.modeVel_add_ae` (`Breakdown/Cert/CoerciveSmoothPressure.lean:73`).

**Theorem: Split an almost-everywhere pairing.** The stated almost-everywhere field decomposition splits the integrated weighted mode pairing into its two component pairings. Source: `Breakdown.Coercive.modeTerm_add_of_ae` (`Breakdown/Cert/CoerciveSmoothPressure.lean:153`).

**Theorem: Compare sum and difference norms.** The squared norms of the sum and difference differ by four times the real part of the complex pairing. Source: `Breakdown.Coercive.Internal.SmoothPressure.cnormSq_add_eq` (`Breakdown/Cert/CoerciveSmoothPressure.lean:180`).

**Theorem: Orthogonality sums to zero by mode.** The mode pairings of the solenoidal test field with the projection remainder form a series summing to zero. Source: `Breakdown.Coercive.Internal.SmoothPressure.pairing_modes_zero` (`Breakdown/Cert/CoerciveSmoothPressure.lean:194`).

**Definition: A time-angular Fourier character.** The character is the complex exponential of the temporal and angular phase determined by the integer frequency pair. Source: `Breakdown.Coercive.Internal.SmoothPressure.torusWave` (`Breakdown/Cert/CoerciveSmoothPressure.lean:223`).

**Theorem: Continuity of time-angular Fourier phase.** Under the stated hypotheses, the time-angular Fourier phase is continuous. Source: `Breakdown.Coercive.Internal.SmoothPressure.continuous_torusWave` (`Breakdown/Cert/CoerciveSmoothPressure.lean:226`).

**Theorem: Torus waves have unit norm.** Every time-angle Fourier wave has complex norm one. Source: `Breakdown.Coercive.Internal.SmoothPressure.norm_torusWave` (`Breakdown/Cert/CoerciveSmoothPressure.lean:230`).

**Theorem: Integrate an angular Fourier wave.** An integer angular Fourier wave integrates to $2\pi$ at zero frequency and to zero otherwise. Source: `Breakdown.Coercive.Internal.SmoothPressure.integral_exp_circle` (`Breakdown/Cert/CoerciveSmoothPressure.lean:233`).

**Theorem: Integrate a temporal Fourier wave.** An integer temporal Fourier wave integrates to one over the unit period at zero frequency and to zero otherwise. Source: `Breakdown.Coercive.Internal.SmoothPressure.integral_exp_period` (`Breakdown/Cert/CoerciveSmoothPressure.lean:255`).

**Theorem: Separate time and angle phases.** The time-angle Fourier wave factors into its temporal phase and its angular exponential. Source: `Breakdown.Coercive.Internal.SmoothPressure.torusWave_split` (`Breakdown/Cert/CoerciveSmoothPressure.lean:279`).

**Theorem: The temporal part of a torus wave.** At angle zero, the torus wave is the temporal exponential at its integer temporal frequency. Source: `Breakdown.Coercive.Internal.SmoothPressure.torusWave_time` (`Breakdown/Cert/CoerciveSmoothPressure.lean:287`).

**Theorem: Angular integration selects zero mode.** Integrating a torus wave over a full angle leaves $2\pi$ times its time phase when its angular frequency is zero and gives zero otherwise. Source: `Breakdown.Coercive.Internal.SmoothPressure.integral_torusWave_inner` (`Breakdown/Cert/CoerciveSmoothPressure.lean:292`).

**Theorem: Time integration selects zero mode.** Integrating the time phase over the unit interval gives one when the temporal frequency is zero and zero otherwise. Source: `Breakdown.Coercive.Internal.SmoothPressure.integral_torusWave_time` (`Breakdown/Cert/CoerciveSmoothPressure.lean:298`).

**Theorem: Extract a real wave's two frequencies.** Multiplying a real wave by a negative extraction phase gives half the sum of its frequency-difference wave and its conjugate frequency-sum wave. Source: `Breakdown.Coercive.Internal.SmoothPressure.torusWave_mul_re` (`Breakdown/Cert/CoerciveSmoothPressure.lean:304`).

**Theorem: Extract a coefficient from a zero sum.** An absolutely summable real wave expansion that vanishes identically still has sum zero after multiplication by the extraction phase and angular integration. Source: `Breakdown.Coercive.Internal.SmoothPressure.hasSum_torus_inner` (`Breakdown/Cert/CoerciveSmoothPressure.lean:333`).

**Theorem: Angular extraction of a real wave.** The angular integral of a phase-weighted real wave retains exactly the two frequency combinations whose angular frequencies vanish. Source: `Breakdown.Coercive.Internal.SmoothPressure.integral_torus_inner_eq` (`Breakdown/Cert/CoerciveSmoothPressure.lean:361`).

**Theorem: Opposite real coefficients cancel.** In an absolutely summable real wave expansion that vanishes identically, the real parts of coefficients at opposite frequencies sum to zero. Source: `Breakdown.Coercive.Internal.SmoothPressure.torus_coeff_re` (`Breakdown/Cert/CoerciveSmoothPressure.lean:375`).

**Theorem: Rotate the zero vector.** Every axial rotation fixes the zero vector. Source: `Breakdown.Coercive.Internal.SmoothPressure.axialRot_zero_vec` (`Breakdown/Cert/CoerciveSmoothPressure.lean:444`).

**Theorem: The zero field has zero modes.** Every time-angular mode of the zero field is zero. Source: `Breakdown.Coercive.Internal.SmoothPressure.modeVel_zero` (`Breakdown/Cert/CoerciveSmoothPressure.lean:448`).

**Theorem: Scale the first pairing argument.** Multiplying the first vector by a complex scalar multiplies the complex pairing by that scalar. Source: `Breakdown.Coercive.Internal.SmoothPressure.cdot_mul_left` (`Breakdown/Cert/CoerciveSmoothPressure.lean:453`).

**Theorem: Conjugate both pairing arguments.** Conjugating both vectors conjugates their complex pairing. Source: `Breakdown.Coercive.Internal.SmoothPressure.cdot_conj` (`Breakdown/Cert/CoerciveSmoothPressure.lean:459`).

**Theorem: The complex mode pairing is integrable.** The complex pairing of the two matching velocity modes is integrable on the period slab. Source: `Breakdown.Coercive.Internal.SmoothPressure.integrable_cdot_modeVel` (`Breakdown/Cert/CoerciveSmoothPressure.lean:466`).

**Theorem: Summable absolute pairing integrals.** The norms of the integrated complex velocity-mode pairings form a summable series over the modes. Source: `Breakdown.Coercive.Internal.SmoothPressure.summable_norm_integral_cdot` (`Breakdown/Cert/CoerciveSmoothPressure.lean:482`).

**Theorem: Orthogonality holds in each mode.** Each integrated mode pairing of the solenoidal projection with its projection remainder vanishes. Source: `Breakdown.Coercive.Internal.SmoothPressure.mode_orthogonal` (`Breakdown/Cert/CoerciveSmoothPressure.lean:500`).

**Theorem: Reflection preserves each mode energy.** Reflection across the solenoidal part is measurable, time-periodic and square-integrable, and preserves the integrated squared norm of every velocity mode. Source: `Breakdown.Coercive.solenoidal_reflection_modes` (`Breakdown/Cert/CoerciveSmoothPressure.lean:561`).

**Theorem: The inner field annihilates gradients.** The period pairing of the smooth right-hand side minus twice the model-gradient action with a periodic test-potential gradient vanishes. Source: `Breakdown.Coercive.Internal.SmoothPressure.innerPart_sub_orthogonal` (`Breakdown/Cert/CoerciveSmoothPressure.lean:619`).

**Theorem: Decompose forcing by reflection.** The smooth forcing is almost everywhere the sum of the inner field and a reflection of the model-gradient action across its solenoidal part, with the component fields in period $L^2$. Source: `Breakdown.Coercive.solenoidal_split_smooth` (`Breakdown/Cert/CoerciveSmoothPressure.lean:642`).

### Breakdown.Cert.CoerciveSmoothSumSecondPartialsPairing

Establishes the cutoff weighted integration-by-parts identity for the antisymmetric pairing of two Laplacians.

**Paper context:** Appendix B, Proposition B.1: the weighted imaginary diffusion pairing in the velocity estimate.

**Definition: A bump between radii one and two.** The fixed smooth bump uses inner radius one and outer radius two. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.bump` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:16`).

**Definition: An expanding spatial cutoff.** The cutoff evaluates the fixed bump on the spatial argument divided by the chosen radius. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.cutoff` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:18`).

**Definition: The antisymmetric derivative flux.** The flux subtracts the pairing with the derivative of the second field from the pairing with the derivative of the first field. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.flux` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:20`).

**Theorem: The cutoff scale is positive.** The reciprocal scale $1/(n+1)$ is positive for every natural-number cutoff index. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.scale_pos` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:23`).

**Theorem: Unit coordinate vectors.** Each coordinate basis vector has norm one. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.norm_unitVector` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:25`).

**Theorem: C1 regularity of cutoff.** Under the stated hypotheses, the spatial cutoff has continuous derivatives through order $1$. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.cutoff_contDiff` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:28`).

**Theorem: Compact support of cutoff.** Under the stated hypotheses, the spatial cutoff has compact support. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.cutoff_hasCompactSupport` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:31`).

**Theorem: The cutoff is one in its inner ball.** The spatial cutoff equals one at every point satisfying the stated inner-radius condition. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.cutoff_eq_one` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:34`).

**Theorem: The cutoff has magnitude at most one.** The absolute value of the spatial cutoff is at most one. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.abs_cutoff_le` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:43`).

**Theorem: The cutoff eventually equals one.** At a fixed spatial point, the expanding cutoff eventually has value one. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.cutoff_eventually_one` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:48`).

**Theorem: The cutoff gradient vanishes inside.** The spatial derivative of the cutoff vanishes inside its radius-$n+1$ core. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.fderiv_cutoff_eq_zero` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:55`).

**Theorem: Cutoff derivatives eventually vanish.** At a fixed spatial point, the derivative of the expanding cutoff is eventually zero. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.fderiv_cutoff_eventually_zero` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:64`).

**Theorem: The bump gradient is bounded.** The fixed smooth bump has a globally bounded derivative norm. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.exists_fderiv_bump_bound` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:72`).

**Theorem: Differentiate the scaled cutoff.** The derivative of the cutoff is the bump derivative evaluated at the scaled point, multiplied by the scale $1/(n+1)$. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.hasFDerivAt_cutoff` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:76`).

**Theorem: Radial decay of the cutoff gradient.** The cutoff derivative norm is at most three times the bump derivative bound divided by one plus the radius. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.norm_fderiv_cutoff_le` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:88`).

**Theorem: Move a derivative by integration.** Under the stated support and regularity conditions, moving the directional derivative from the first real factor to the second negates their integral. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.integral_fderiv_mul_eq` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:110`).

**Theorem: A directional derivative is C1.** The derivative of the field in the fixed direction is continuously differentiable. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.contDiff_fderiv_apply` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:126`).

**Theorem: The antisymmetric flux is C1.** Under the stated hypotheses, the antisymmetric derivative flux has continuous derivatives through order $1$. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.flux_contDiff` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:130`).

**Theorem: Differentiate a directional derivative.** The derivative of the directional derivative is the second Fréchet derivative with the fixed direction inserted in the stated slot. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.hasFDerivAt_fderiv_apply` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:135`).

**Theorem: Differentiate the antisymmetric flux.** The coordinate derivative of the flux is the difference of the two second-derivative and field pairings, with the first-derivative cross terms cancelled. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.fderiv_flux_apply` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:142`).

**Theorem: The flux divergence is a Laplacian pair.** Summing the coordinate flux derivatives gives the difference of the Laplacian pairings of the two fields. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.sum_fderiv_flux` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:161`).

**Theorem: Bound the antisymmetric flux.** The absolute flux is at most the sum of each field's norm times the other field's derivative norm. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.abs_flux_le` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:167`).

**Theorem: Bound a coordinate derivative.** The absolute derivative in a coordinate unit direction is at most the operator norm of the full derivative. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.abs_fderiv_apply_le` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:180`).

**Theorem: Weighted flux integration by parts.** The cutoff-weighted flux divergence, weight-gradient flux and cutoff-gradient flux are integrable, and their integrals satisfy the stated two-term integration-by-parts identity. Source: `Breakdown.Coercive.SumSecondPartialsPairing.Internal.pairing_identity` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:184`).

**Theorem: Weighted Laplacian pairing identity.** The cutoff integration-by-parts limit supplies the weighted antisymmetric Laplacian pairing identity. Source: `Breakdown.Coercive.weightedSumSecondPartialsPairingHolds_proof` (`Breakdown/Cert/CoerciveSmoothSumSecondPartialsPairing.lean:238`).

### Breakdown.Cert.CoerciveSolenoidal

Constructs the periodic solenoidal part by orthogonal projection in period L2 and proves its norm and symmetry properties under the stated density interface.

**Paper context:** Appendix B, (B.14) and Proposition B.1: the divergence-free projection used for the multiplier and velocity pairing.

**Definition: Spacetime measure on one period.** The measure is Lebesgue measure restricted to the unit time interval, multiplied by spatial Lebesgue measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.periodMeasure` (`Breakdown/Cert/CoerciveSolenoidal.lean:14`).

**Definition: Square-integrable fields on one period.** The period space is the real Hilbert space of square-integrable spatial vector fields on the unit time slab. Source: `Breakdown.Coercive.Internal.SolenoidalPart.PeriodL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:17`).

**Definition: Put a physical field into period L2.** The conversion uses the field's $L^2$ equivalence class when it is square-integrable and returns zero otherwise. Source: `Breakdown.Coercive.Internal.SolenoidalPart.toL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:20`).

**Definition: Choose a measurable representative.** The representative is a measurable function chosen from the given $L^2$ equivalence class. Source: `Breakdown.Coercive.Internal.SolenoidalPart.reprL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:23`).

**Definition: Extend an L2 representative periodically.** The periodic field evaluates the chosen representative at the fractional part of time and the original spatial point. Source: `Breakdown.Coercive.Internal.SolenoidalPart.ofL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:25`).

**Theorem: The measure of one spacetime period.** The period measure is full spacetime volume restricted to the closed unit time slab. Source: `Breakdown.Coercive.Internal.SolenoidalPart.periodMeasure_eq` (`Breakdown/Cert/CoerciveSolenoidal.lean:27`).

**Theorem: The field is measurable on the period.** The joint field is almost everywhere strongly measurable for the unit-period measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.aestronglyMeasurable_period` (`Breakdown/Cert/CoerciveSolenoidal.lean:31`).

**Theorem: Read the period integral on the slab.** The iterated nonnegative period integral equals integration against the unit-time product measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.lintegral_period` (`Breakdown/Cert/CoerciveSolenoidal.lean:37`).

**Theorem: Finite period energy gives an L2 class.** The stated measurability and finite energy assumptions place the field in $L^2$ for the period measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.memLp_of` (`Breakdown/Cert/CoerciveSolenoidal.lean:42`).

**Theorem: An L2 field has finite period energy.** The field's squared-norm period integral is finite under its period-$L^2$ hypothesis. Source: `Breakdown.Coercive.Internal.SolenoidalPart.lt_top_of_memLp` (`Breakdown/Cert/CoerciveSolenoidal.lean:54`).

**Theorem: The L2 representative agrees a.e..** For a field satisfying the stated $L^2$ hypothesis, its $L^2$ class agrees almost everywhere on the period slab with the original field. Source: `Breakdown.Coercive.Internal.SolenoidalPart.coeFn_toL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:61`).

**Theorem: The period pairing is an L2 product.** The iterated period pairing of the two square-integrable fields equals the Hilbert-space inner product of their $L^2$ classes. Source: `Breakdown.Coercive.Internal.SolenoidalPart.pairing_eq_inner` (`Breakdown/Cert/CoerciveSolenoidal.lean:67`).

**Theorem: The period norm is the L2 norm.** The period norm of the square-integrable field equals the norm of its $L^2$ class. Source: `Breakdown.Coercive.Internal.SolenoidalPart.periodNorm_eq` (`Breakdown/Cert/CoerciveSolenoidal.lean:80`).

**Theorem: Measurability of fractional-time map.** Under the stated hypotheses, the fractional-time map is measurable. Source: `Breakdown.Coercive.Internal.SolenoidalPart.measurable_fractPair` (`Breakdown/Cert/CoerciveSolenoidal.lean:95`).

**Theorem: The periodic L2 field is measurable a.e..** Under the stated hypotheses, the periodic L2 representative is almost everywhere strongly measurable. Source: `Breakdown.Coercive.Internal.SolenoidalPart.aestronglyMeasurable_ofL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:98`).

**Theorem: Periodic L2 representative is periodic.** Under the stated hypotheses, the periodic L2 representative has period one in time. Source: `Breakdown.Coercive.Internal.SolenoidalPart.periodic_ofL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:102`).

**Theorem: The half-open slab has full measure.** Almost every point for the period measure has time coordinate in the half-open unit interval. Source: `Breakdown.Coercive.Internal.SolenoidalPart.ae_mem_Ico` (`Breakdown/Cert/CoerciveSolenoidal.lean:106`).

**Theorem: Periodise an L2 representative.** The chosen periodic field associated to an $L^2$ class agrees almost everywhere on the period slab with that class. Source: `Breakdown.Coercive.Internal.SolenoidalPart.ofL2_ae` (`Breakdown/Cert/CoerciveSolenoidal.lean:112`).

**Theorem: The periodised representative is in L2.** Under the stated hypotheses, the periodic L2 representative belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.memLp_ofL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:118`).

**Theorem: Recover the original L2 class.** Taking the $L^2$ class of the chosen periodic representative returns the original class. Source: `Breakdown.Coercive.Internal.SolenoidalPart.toL2_ofL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:122`).

**Theorem: Integer time shifts preserve a field.** Every integer time shift preserves a one-periodic field. Source: `Breakdown.Coercive.Internal.SolenoidalPart.periodic_int` (`Breakdown/Cert/CoerciveSolenoidal.lean:125`).

**Theorem: Extend a.e. equality to all time.** Two one-periodic fields equal almost everywhere on a unit time slab are equal almost everywhere in spacetime. Source: `Breakdown.Coercive.Internal.SolenoidalPart.ae_of_period` (`Breakdown/Cert/CoerciveSolenoidal.lean:131`).

**Theorem: A supported periodic field lies in L2.** The stated continuity, periodicity and bounded spatial support place the field in $L^2$ for the period measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.memLp_of_continuous` (`Breakdown/Cert/CoerciveSolenoidal.lean:153`).

**Theorem: Periodic test fields lie in L2.** Every periodic solenoidal test field belongs to $L^2$ for the period measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.memLp_testField` (`Breakdown/Cert/CoerciveSolenoidal.lean:176`).

**Definition: A potential's spatial gradient.** The potential-gradient field differentiates the potential in its spatial argument. Source: `Breakdown.Coercive.Internal.SolenoidalPart.gradOf` (`Breakdown/Cert/CoerciveSolenoidal.lean:181`).

**Theorem: Continuity of test-potential gradient.** Under the stated hypotheses, the test-potential gradient is continuous. Source: `Breakdown.Coercive.Internal.SolenoidalPart.continuous_gradOf` (`Breakdown/Cert/CoerciveSolenoidal.lean:183`).

**Theorem: The potential gradient vanishes outside.** A potential that vanishes beyond the stated radius also has zero spatial gradient beyond that radius. Source: `Breakdown.Coercive.Internal.SolenoidalPart.gradOf_zero` (`Breakdown/Cert/CoerciveSolenoidal.lean:190`).

**Theorem: The test-potential gradient is in L2.** Under the stated hypotheses, the test-potential gradient belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.Internal.SolenoidalPart.memLp_gradOf` (`Breakdown/Cert/CoerciveSolenoidal.lean:197`).

**Theorem: Smoothness of function X.** Under the stated hypotheses, the function $X$ is smooth. Source: `Breakdown.Coercive.Internal.SolenoidalPart.slice_contDiff` (`Breakdown/Cert/CoerciveSolenoidal.lean:202`).

**Theorem: A periodic test field gives test slices.** Each time slice of a periodic solenoidal test field is a spatial solenoidal test field. Source: `Breakdown.Coercive.Internal.SolenoidalPart.slice_isTestField` (`Breakdown/Cert/CoerciveSolenoidal.lean:206`).

**Theorem: Test fields are orthogonal to gradients.** The period pairing of a periodic solenoidal test field with a periodic test-potential gradient vanishes. Source: `Breakdown.Coercive.Internal.SolenoidalPart.pairing_test_grad` (`Breakdown/Cert/CoerciveSolenoidal.lean:213`).

**Definition: The closed solenoidal test-field span.** The subspace is the closure of the real linear span of periodic solenoidal test fields in period $L^2$. Source: `Breakdown.Coercive.Internal.SolenoidalPart.testSpan` (`Breakdown/Cert/CoerciveSolenoidal.lean:224`).

**Instance: Complete solenoidal test-field space.** The closed span of periodic solenoidal test fields is a complete normed space. Source: `anonymous instance` (`Breakdown/Cert/CoerciveSolenoidal.lean:227`). [Open this instance in the source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveSolenoidal.lean#L227).

**Theorem: The test span annihilates gradients.** Every vector in the closed span of periodic solenoidal test fields is orthogonal to every periodic test-potential gradient. Source: `Breakdown.Coercive.Internal.SolenoidalPart.inner_grad_eq_zero` (`Breakdown/Cert/CoerciveSolenoidal.lean:229`).

**Theorem: A test field belongs to its closed span.** The $L^2$ class of every periodic solenoidal test field belongs to the closed test-field span. Source: `Breakdown.Coercive.Internal.SolenoidalPart.test_mem` (`Breakdown/Cert/CoerciveSolenoidal.lean:242`).

**Theorem: Construct the solenoidal part.** The periodic representative of the orthogonal projection onto the closed test-field span is a solenoidal part of the original field. Source: `Breakdown.Coercive.Internal.SolenoidalPart.isSolenoidalPartOf_ofL2` (`Breakdown/Cert/CoerciveSolenoidal.lean:245`).

**Theorem: L2 classes preserve subtraction.** Passing two square-integrable fields to $L^2$ classes commutes with subtraction. Source: `Breakdown.Coercive.Internal.SolenoidalPart.toL2_sub` (`Breakdown/Cert/CoerciveSolenoidal.lean:262`).

**Theorem: Two orthogonalities force zero.** Under the gradient-solenoidal density interface, an $L^2$ vector orthogonal to all test gradients and all solenoidal test fields is zero. Source: `Breakdown.Coercive.Internal.SolenoidalPart.eq_zero_of_orthogonal` (`Breakdown/Cert/CoerciveSolenoidal.lean:272`).

**Theorem: The solenoidal part is unique a.e..** Under the gradient-solenoidal density interface, any two solenoidal parts of the same field agree almost everywhere. Source: `Breakdown.Coercive.Internal.SolenoidalPart.unique_part` (`Breakdown/Cert/CoerciveSolenoidal.lean:291`).

**Theorem: Projection and reflection norms.** The constructed solenoidal projection does not increase the period norm, and reflection across that projection preserves the norm. Source: `Breakdown.Coercive.Internal.SolenoidalPart.norms_part` (`Breakdown/Cert/CoerciveSolenoidal.lean:308`).

**Theorem: Shift the time integration window.** The integral of a one-periodic function is unchanged by shifting its unit-length time window. Source: `Breakdown.Coercive.Internal.SolenoidalPart.lintegral_shift` (`Breakdown/Cert/CoerciveSolenoidal.lean:339`).

**Theorem: Shift the time integration window.** The integral of a one-periodic function is unchanged by shifting its unit-length time window. Source: `Breakdown.Coercive.Internal.SolenoidalPart.integral_shift` (`Breakdown/Cert/CoerciveSolenoidal.lean:356`).

**Theorem: Diagonal entries give the trace.** The sum of a linear map's diagonal entries in the coordinate basis equals its trace. Source: `Breakdown.Coercive.Internal.SolenoidalPart.diag_sum_eq_trace` (`Breakdown/Cert/CoerciveSolenoidal.lean:373`).

**Theorem: Trace is invariant under conjugation.** Conjugating a linear map by the given linear isometry preserves the sum of its diagonal entries. Source: `Breakdown.Coercive.Internal.SolenoidalPart.diag_sum_conj` (`Breakdown/Cert/CoerciveSolenoidal.lean:378`).

**Theorem: Divergence transforms under an isometry.** The divergence of the isometric push-forward equals the original divergence evaluated at the inverse image point. Source: `Breakdown.Coercive.Internal.SolenoidalPart.divergenceAt_pushForward` (`Breakdown/Cert/CoerciveSolenoidal.lean:384`).

**Definition: Move a test field in time and space.** The moved test field shifts time, pulls back the spatial argument by the isometry and pushes forward the vector value. Source: `Breakdown.Coercive.Internal.SolenoidalPart.moveField` (`Breakdown/Cert/CoerciveSolenoidal.lean:396`).

**Definition: Move a scalar test potential.** The moved potential shifts time and pulls back its spatial argument by the isometry. Source: `Breakdown.Coercive.Internal.SolenoidalPart.movePotential` (`Breakdown/Cert/CoerciveSolenoidal.lean:399`).

**Theorem: Moving the field preserves smoothness.** The smooth joint field remains smooth after the specified time translation and inverse spatial isometry. Source: `Breakdown.Coercive.Internal.SolenoidalPart.contDiff_move` (`Breakdown/Cert/CoerciveSolenoidal.lean:402`).

**Theorem: Move a periodic solenoidal test field.** The defined combination of an isometry and time shift preserves periodic solenoidal test fields. Source: `Breakdown.Coercive.Internal.SolenoidalPart.isPeriodicTestField_move` (`Breakdown/Cert/CoerciveSolenoidal.lean:408`).

**Theorem: Move a periodic test potential.** The defined combination of an isometry and time shift preserves periodic test potentials. Source: `Breakdown.Coercive.Internal.SolenoidalPart.isPeriodicTestPotential_move` (`Breakdown/Cert/CoerciveSolenoidal.lean:424`).

**Theorem: Move an isometry across the pairing.** A change of variables transfers the time shift and spatial isometry from the first field to the second in the period pairing. Source: `Breakdown.Coercive.Internal.SolenoidalPart.pairing_move` (`Breakdown/Cert/CoerciveSolenoidal.lean:434`).

**Theorem: Solenoidal parts respect rigid changes.** A simultaneous time shift and isometric pullback of both fields preserves the solenoidal-part relation. Source: `Breakdown.Coercive.Internal.SolenoidalPart.isSolenoidalPartOf_move` (`Breakdown/Cert/CoerciveSolenoidal.lean:452`).

**Theorem: Close the solenoidal-mode interface.** The projection, uniqueness, norm and symmetry results supply the solenoidal-mode interface. Source: `Breakdown.Coercive.solenoidalModeHolds_of` (`Breakdown/Cert/CoerciveSolenoidal.lean:495`).

**The closed test span is complete.** Instance. The closure of the span of periodic test fields is a closed subspace of the period L² space, so it is complete. ([`instCompleteSpaceSubtypeAEEqFunProdRealSpacePeriodMeasureMemAddSubgroupPeriodL2SubmoduleTestSpan`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveSolenoidal.lean#L227))

### Breakdown.Cert.CoerciveSquareSum

Proves period Parseval identities for velocity, gradient and second-derivative modes, then polarises them to recover pairings.

**Paper context:** Appendix B, Proposition B.1 and the mode decomposition preceding (B.15): Parseval and polarisation for the coercive calculation.

**Theorem: Coordinate evaluation is continuous.** A fixed spatial coordinate is a continuous function of the vector. Source: `Breakdown.Coercive.continuous_coord` (`Breakdown/Cert/CoerciveSquareSum.lean:12`).

**Theorem: Rotation is jointly continuous.** The axially rotated vector depends continuously on both angle and input vector. Source: `Breakdown.Coercive.continuous_axialRot_pair` (`Breakdown/Cert/CoerciveSquareSum.lean:15`).

**Theorem: Shift and rotation preserve volume.** A time translation combined with an axial spatial rotation preserves spacetime volume. Source: `Breakdown.Coercive.measurePreserving_shiftRot` (`Breakdown/Cert/CoerciveSquareSum.lean:25`).

**Theorem: Null sets survive parameterised motion.** The parameterised time-shift and axial-rotation map pulls spacetime null sets back to null sets for the stated product measure. Source: `Breakdown.Coercive.quasiMeasurePreserving_shiftRot` (`Breakdown/Cert/CoerciveSquareSum.lean:37`).

**Theorem: Null sets survive iterated parameters.** The time-shift and axial-rotation map pulls spacetime null sets back to null sets for the nested product of the two parameter measures. Source: `Breakdown.Coercive.quasiMeasurePreserving_shiftRot_nested` (`Breakdown/Cert/CoerciveSquareSum.lean:58`).

**Theorem: The mode average is measurable a.e..** Under the stated hypotheses, the time-angular mode average is almost everywhere strongly measurable. Source: `Breakdown.Coercive.aestronglyMeasurable_modeAverage` (`Breakdown/Cert/CoerciveSquareSum.lean:66`).

**Theorem: Shift the time integration window.** The integral of a one-periodic function is unchanged by shifting its unit-length time window. Source: `Breakdown.Coercive.lintegral_periodic_shift` (`Breakdown/Cert/CoerciveSquareSum.lean:87`).

**Theorem: Compute matrix energy in any basis.** The sum of squared image norms of an orthonormal basis equals the sum of squared norms of the adjoint on the coordinate basis. Source: `Breakdown.Coercive.sum_norm_sq_orthonormalBasis` (`Breakdown/Cert/CoerciveSquareSum.lean:111`).

**Theorem: Matrix energy is rotation invariant.** Rotating the coordinate input basis preserves the sum of squared column norms of the linear map. Source: `Breakdown.Coercive.matSq_rot` (`Breakdown/Cert/CoerciveSquareSum.lean:123`).

**Theorem: The transformed field is measurable a.e..** The stated coordinate transform of the time-shifted and rotated field is almost everywhere strongly measurable for the joint spacetime-parameter measure. Source: `Breakdown.Coercive.aestronglyMeasurable_comp_shiftRot` (`Breakdown/Cert/CoerciveSquareSum.lean:133`).

**Theorem: The nested orbit field is measurable.** The stated coordinate transform of the shifted and rotated field is almost everywhere strongly measurable for the nested spacetime, time and angle measure. Source: `Breakdown.Coercive.aestronglyMeasurable_comp_shiftRot_nested` (`Breakdown/Cert/CoerciveSquareSum.lean:147`).

**Theorem: Shift and rotate a period integral.** The nonnegative period integral of a periodic scalar field is unchanged by a time shift and axial spatial rotation. Source: `Breakdown.Coercive.lintegral_shiftRot` (`Breakdown/Cert/CoerciveSquareSum.lean:161`).

**Theorem: Orbit square energy is measurable a.e..** The nonnegative embedding of the specified orbit square-energy function is almost everywhere measurable on the period-slab and time-angle product domain. Source: `Breakdown.Coercive.aemeasurable_rect` (`Breakdown/Cert/CoerciveSquareSum.lean:181`).

**Theorem: Integrate over the time-angle orbit.** The spacetime integral of the orbitwise time-angle integral is $2\pi$ times the original period integral. Source: `Breakdown.Coercive.lintegral_rect` (`Breakdown/Cert/CoerciveSquareSum.lean:200`).

**Theorem: Orbit integrals are finite a.e..** Finite period energy implies that the time-angle orbit integral is finite for almost every spacetime point on the period slab. Source: `Breakdown.Coercive.ae_rect_lt_top` (`Breakdown/Cert/CoerciveSquareSum.lean:222`).

**Theorem: Parseval for an invariant square norm.** The period integral of the stated coordinate square norm equals the sum of the integrated squared norms of its time-angular mode coefficients. Source: `Breakdown.Coercive.modeSquareSum_generic` (`Breakdown/Cert/CoerciveSquareSum.lean:233`).

**Theorem: Rotation preserves vector energy.** The sum of squared coordinates after axial rotation equals the original squared Euclidean norm. Source: `Breakdown.Coercive.sum_sq_axialRot_coord` (`Breakdown/Cert/CoerciveSquareSum.lean:350`).

**Theorem: A rotated coordinate is continuous.** The pulled-back vector coordinate depends continuously on the rotation angle and input vector. Source: `Breakdown.Coercive.continuous_rotCoord` (`Breakdown/Cert/CoerciveSquareSum.lean:356`).

**Theorem: A rotated gradient entry is continuous.** The pulled-back gradient entry depends continuously on the angle and input linear map. Source: `Breakdown.Coercive.continuous_rotGrad` (`Breakdown/Cert/CoerciveSquareSum.lean:363`).

**Theorem: A rotated Hessian entry is continuous.** The pulled-back second-derivative entry depends continuously on the angle and input bilinear map. Source: `Breakdown.Coercive.continuous_rotSecondDeriv` (`Breakdown/Cert/CoerciveSquareSum.lean:377`).

**Theorem: Rotation preserves gradient energy.** The sum of squared entries of the gradient in rotated input and output coordinates equals its original squared matrix norm. Source: `Breakdown.Coercive.sum_sq_rotGrad` (`Breakdown/Cert/CoerciveSquareSum.lean:396`).

**Theorem: Rotation preserves Hessian energy.** The sum of squared second-derivative entries in the rotated coordinates equals the original squared Hessian norm. Source: `Breakdown.Coercive.sum_sq_rotSecondDeriv` (`Breakdown/Cert/CoerciveSquareSum.lean:404`).

**Theorem: Parseval for velocity modes.** The period $L^2$ energy of a vector field equals the sum of the integrated squared velocity-mode norms. Source: `Breakdown.Coercive.velSquareSum` (`Breakdown/Cert/CoerciveSquareSum.lean:430`).

**Theorem: Parseval for gradient modes.** The period squared matrix energy equals the sum of the integrated squared gradient-mode norms. Source: `Breakdown.Coercive.gradSquareSum` (`Breakdown/Cert/CoerciveSquareSum.lean:439`).

**Theorem: Parseval for second-derivative modes.** The period squared Hessian energy equals the sum of the integrated squared second-derivative-mode norms. Source: `Breakdown.Coercive.secondDerivSquareSum` (`Breakdown/Cert/CoerciveSquareSum.lean:450`).

**Definition: Spacetime measure on one period.** The measure is Lebesgue measure restricted to the unit time interval, multiplied by spatial Lebesgue measure. Source: `Breakdown.Coercive.slabMeasure` (`Breakdown/Cert/CoerciveSquareSum.lean:462`).

**Definition: Time-angular integration measure.** The rectangle measure covers one unit of time and one full angular turn. Source: `Breakdown.Coercive.rectMeasure` (`Breakdown/Cert/CoerciveSquareSum.lean:465`).

**Theorem: Restricting to one time period.** The product measure on one time period is absolutely continuous with respect to full spacetime volume. Source: `Breakdown.Coercive.slab_ac` (`Breakdown/Cert/CoerciveSquareSum.lean:468`).

**Theorem: Read the period integral on the slab.** The iterated nonnegative period integral equals integration against the unit-time product measure. Source: `Breakdown.Coercive.period_eq_slab` (`Breakdown/Cert/CoerciveSquareSum.lean:471`).

**Theorem: Finite energy gives slab integrability.** The stated nonnegative function is integrable for the unit-slab measure under the finite period-integral hypothesis. Source: `Breakdown.Coercive.integrable_slab` (`Breakdown/Cert/CoerciveSquareSum.lean:476`).

**Theorem: A finite period integral from L1.** The nonnegative period integral is finite under the stated slab-integrability hypothesis. Source: `Breakdown.Coercive.period_lt_top_of_integrable` (`Breakdown/Cert/CoerciveSquareSum.lean:482`).

**Theorem: Recover the real slab integral.** For the stated nonnegative integrable field, its real slab integral equals the real value of its nonnegative period integral. Source: `Breakdown.Coercive.integral_slab` (`Breakdown/Cert/CoerciveSquareSum.lean:488`).

**Theorem: A finite norm integral gives L1.** The stated measurability and finite norm integral imply integrability of the displayed function. Source: `Breakdown.Coercive.integrable_of_sq_lintegral` (`Breakdown/Cert/CoerciveSquareSum.lean:494`).

**Theorem: Phase multiplication preserves L1.** Multiplying the real integrable time-angle function by its unit complex Fourier phase gives an integrable complex function on the rectangle. Source: `Breakdown.Coercive.integrable_rect_phase` (`Breakdown/Cert/CoerciveSquareSum.lean:503`).

**Theorem: Mode averages preserve addition.** The mode average of a sum is the sum of the mode averages. Source: `Breakdown.Coercive.modeAverage_add` (`Breakdown/Cert/CoerciveSquareSum.lean:515`).

**Theorem: Mode averages preserve subtraction.** The mode average of a difference is the difference of the mode averages. Source: `Breakdown.Coercive.modeAverage_sub` (`Breakdown/Cert/CoerciveSquareSum.lean:532`).

**Theorem: A velocity mode is an orbit average.** Each velocity-mode coordinate is the Fourier average of the corresponding coordinate of the pulled-back time-angle orbit. Source: `Breakdown.Coercive.modeVel_apply` (`Breakdown/Cert/CoerciveSquareSum.lean:549`).

**Theorem: Axial rotation preserves addition.** Axial rotation maps a vector sum to the sum of the rotated vectors. Source: `Breakdown.Coercive.axialRot_add` (`Breakdown/Cert/CoerciveSquareSum.lean:553`).

**Theorem: Axial rotation preserves differences.** Axial rotation maps a vector difference to the difference of the rotated vectors. Source: `Breakdown.Coercive.axialRot_sub` (`Breakdown/Cert/CoerciveSquareSum.lean:558`).

**Theorem: Modes preserve field sums.** Taking a time-angular mode commutes with addition of the displayed fields. Source: `Breakdown.Coercive.modeVel_add` (`Breakdown/Cert/CoerciveSquareSum.lean:563`).

**Theorem: Modes preserve field differences.** Taking a time-angular mode commutes with subtraction of the displayed fields. Source: `Breakdown.Coercive.modeVel_sub` (`Breakdown/Cert/CoerciveSquareSum.lean:573`).

**Theorem: Polarisation of the complex pairing.** The real part of the complex pairing is one quarter of the difference between the squared sum and difference norms. Source: `Breakdown.Coercive.re_cdot_eq` (`Breakdown/Cert/CoerciveSquareSum.lean:583`).

**Theorem: Real polarisation identity.** The real inner product is one quarter of the difference between the squared sum and difference norms. Source: `Breakdown.Coercive.inner_eq_quarter` (`Breakdown/Cert/CoerciveSquareSum.lean:590`).

**Theorem: Squared norm of a sum.** The squared norm of a sum is at most twice the sum of the squared norms. Source: `Breakdown.Coercive.norm_add_sq_le` (`Breakdown/Cert/CoerciveSquareSum.lean:594`).

**Theorem: Bound the squared difference.** The squared norm of a vector difference is at most twice the sum of the two squared norms. Source: `Breakdown.Coercive.norm_sub_sq_le` (`Breakdown/Cert/CoerciveSquareSum.lean:597`).

**Theorem: Velocity-mode energy is measurable a.e..** Under the stated hypotheses, the squared complex norm of the velocity mode is almost everywhere strongly measurable. Source: `Breakdown.Coercive.aestronglyMeasurable_cnormSq_modeVel` (`Breakdown/Cert/CoerciveSquareSum.lean:600`).

**Theorem: Orbit coordinates are integrable a.e..** For almost every spacetime point on the period slab, each pulled-back orbit coordinate is integrable over the time-angle rectangle. Source: `Breakdown.Coercive.ae_integrable_comp` (`Breakdown/Cert/CoerciveSquareSum.lean:613`).

**Theorem: Integrable mode energies sum correctly.** Each velocity-mode square is integrable, and the series of its slab integrals sums to the original field's real period energy. Source: `Breakdown.Coercive.modeVel_facts` (`Breakdown/Cert/CoerciveSquareSum.lean:633`).

**Theorem: Parseval for a bilinear period pairing.** The integrated real pairings of matching velocity modes form a series summing to the original fields' real period pairing. Source: `Breakdown.Coercive.polarSquareSum` (`Breakdown/Cert/CoerciveSquareSum.lean:655`).

**Theorem: Close the mode square-sum interface.** The established mode-energy and polarisation identities supply the mode square-sum interface. Source: `Breakdown.Coercive.modeSquareSumHolds_of` (`Breakdown/Cert/CoerciveSquareSum.lean:737`).

### Breakdown.Cert.CoerciveStretch

Bounds the stretching form in rotating coordinates and reduces its time-angle integral to modewise charges by Parseval.

**Paper context:** Appendix B, (B.18) and (B.25): the stretching density and its modewise bound; the source uses the coefficient sqrt(2)+1/2.

**Definition: The mixed stretching form.** The mixed stretching form combines model-vorticity-gradient couplings with velocity and perturbation-gradient coordinates. Source: `Breakdown.Coercive.StretchInternal.bilin` (`Breakdown/Cert/CoerciveStretch.lean:20`).

**Definition: A matrix-vector coordinate.** The matrix-vector coordinate is the sum of the row entries times the vector coordinates. Source: `Breakdown.Coercive.StretchInternal.matVec` (`Breakdown/Cert/CoerciveStretch.lean:25`).

**Definition: Cross-product coordinates.** The cross-product coordinates contract the vector with the three-dimensional alternating symbol. Source: `Breakdown.Coercive.StretchInternal.crossVec` (`Breakdown/Cert/CoerciveStretch.lean:27`).

**Definition: Kernel of the mixed stretching form.** The kernel combines the two alternating-symbol contractions that multiply the perturbation-gradient entries. Source: `Breakdown.Coercive.StretchInternal.kernel` (`Breakdown/Cert/CoerciveStretch.lean:29`).

**Theorem: The stretching kernel contracts a matrix.** The mixed stretching form equals the entrywise contraction of its kernel with the final matrix argument. Source: `Breakdown.Coercive.StretchInternal.bilin_eq_sum` (`Breakdown/Cert/CoerciveStretch.lean:32`).

**Theorem: The cross-product matrix energy.** The sum of squared entries of the vector's cross-product matrix is twice the vector's squared Euclidean norm. Source: `Breakdown.Coercive.StretchInternal.crossVec_sq_sum` (`Breakdown/Cert/CoerciveStretch.lean:47`).

**Theorem: Recover an order from squared values.** If the upper comparison value is nonnegative, the stated comparison of squares implies the same order between the original values. Source: `Breakdown.Coercive.StretchInternal.le_of_sq_le_sq_of_nonneg` (`Breakdown/Cert/CoerciveStretch.lean:53`).

**Theorem: Matrix Cauchy–Schwarz.** The square of the entrywise matrix pairing is at most the product of the two entrywise square sums. Source: `Breakdown.Coercive.StretchInternal.sum_sq_prod_le` (`Breakdown/Cert/CoerciveStretch.lean:58`).

**Theorem: Vector Cauchy–Schwarz.** The square of the coordinate pairing is at most the product of the two coordinate square sums. Source: `Breakdown.Coercive.StretchInternal.sum_sq_le` (`Breakdown/Cert/CoerciveStretch.lean:65`).

**Theorem: Bound the mixed stretching form.** For a trace-free coefficient matrix with operator bound $K$, the mixed stretching form is bounded by $(\sqrt2+1/2)K$ times the vector norm and the matrix square-sum norm. Source: `Breakdown.Coercive.StretchInternal.bilin_abs_le` (`Breakdown/Cert/CoerciveStretch.lean:94`).

**Theorem: Add the stretching coefficient matrices.** The mixed stretching form is additive in its coefficient-matrix argument. Source: `Breakdown.Coercive.StretchInternal.bilin_add` (`Breakdown/Cert/CoerciveStretch.lean:129`).

**Theorem: Curl from the alternating symbol.** Each curl-vector coordinate is the contraction of the gradient entries with the alternating symbol. Source: `Breakdown.Coercive.StretchInternal.curlVec_apply` (`Breakdown/Cert/CoerciveStretch.lean:134`).

**Theorem: Split the stretching density.** The stretching density is the negative symmetric-gradient quadratic form in curl plus the mixed form involving the model vorticity gradient, velocity and perturbation gradient. Source: `Breakdown.Coercive.StretchInternal.stretchForm_eq` (`Breakdown/Cert/CoerciveStretch.lean:138`).

**Theorem: Bound the coordinate matrix action.** The coordinate square sum of a matrix-vector product is at most the squared operator norm times the input coordinate square sum. Source: `Breakdown.Coercive.StretchInternal.matVec_le_opNorm` (`Breakdown/Cert/CoerciveStretch.lean:147`).

**Theorem: Bound the negative stretching density.** The assumed strain and vorticity-gradient bounds control negative stretching by a curl-square term, the retained mean mixed form and a wave-gradient norm product. Source: `Breakdown.Coercive.StretchInternal.neg_stretchForm_le` (`Breakdown/Cert/CoerciveStretch.lean:165`).

**Definition: The mixed form on complex modes.** The complex-mode form adds the mixed stretching form evaluated on the real parts and on the imaginary parts. Source: `Breakdown.Coercive.StretchInternal.modeBilin` (`Breakdown/Cert/CoerciveStretch.lean:188`).

**Definition: The mean vorticity-gradient matrix.** The matrix entry differentiates one component of the mean field's vorticity along one coordinate direction. Source: `Breakdown.Coercive.StretchInternal.meanVortCoord` (`Breakdown/Cert/CoerciveStretch.lean:191`).

**Definition: One stretching charge in mode space.** The fibre term combines the mean and wave strain bound, the mixed mean-vorticity coupling and the balanced wave-vorticity-gradient charge. Source: `Breakdown.Coercive.StretchInternal.fibreTerm` (`Breakdown/Cert/CoerciveStretch.lean:194`).

**Theorem: Split a complex vector's energy.** The complex-vector squared norm is the sum of the real-coordinate and imaginary-coordinate square sums. Source: `Breakdown.Coercive.StretchInternal.cnormSq_eq_vec` (`Breakdown/Cert/CoerciveStretch.lean:201`).

**Theorem: Split a complex matrix's energy.** The complex-matrix squared norm is the sum of the real-entry and imaginary-entry square sums. Source: `Breakdown.Coercive.StretchInternal.cnormSq_eq_mat` (`Breakdown/Cert/CoerciveStretch.lean:206`).

**Theorem: Two-term Cauchy–Schwarz bound.** The displayed paired two-term expression is bounded by the combined nonnegative square-root factors. Source: `Breakdown.Coercive.StretchInternal.two_term_le` (`Breakdown/Cert/CoerciveStretch.lean:211`).

**Theorem: Bound the complex mixed form.** For a trace-free coefficient matrix with operator bound $K$, the modewise mixed form is bounded by $(\sqrt2+1/2)K$ times the two complex square-sum norms. Source: `Breakdown.Coercive.StretchInternal.modeBilin_abs_le` (`Breakdown/Cert/CoerciveStretch.lean:222`).

**Theorem: The fibre term fits the stretch charge.** The mean-vorticity gradient bound and trace condition make each fibre term at most the corresponding mode stretching charge. Source: `Breakdown.Coercive.StretchInternal.fibreTerm_le_charge` (`Breakdown/Cert/CoerciveStretch.lean:240`).

**Theorem: Embed a dominated real series bound.** A real quantity bounded by $2\pi$ times a summable series is bounded after nonnegative embedding by $2\pi$ times the series of the dominating nonnegative embeddings. Source: `Breakdown.Coercive.StretchInternal.ofReal_le_of_tsum_le` (`Breakdown/Cert/CoerciveStretch.lean:257`).

**Definition: Curl as a continuous linear map.** This bundles the matrix-to-curl operation as a continuous linear map. Source: `Breakdown.Coercive.StretchInternal.curlCLM` (`Breakdown/Cert/CoerciveStretch.lean:279`).

**Theorem: Evaluate the linear curl map.** The continuous linear curl map returns the curl vector of its matrix argument. Source: `Breakdown.Coercive.StretchInternal.curlCLM_apply` (`Breakdown/Cert/CoerciveStretch.lean:283`).

**Theorem: The divergence of curl vanishes.** The sum of the three coordinate derivatives of the curl is zero under the stated second-order regularity hypothesis. Source: `Breakdown.Coercive.StretchInternal.vortTrace_eq_zero` (`Breakdown/Cert/CoerciveStretch.lean:287`).

**Theorem: Regularity survives bounded integration.** Integrating over the fixed bounded parameter intervals preserves the displayed order of continuous differentiability. Source: `Breakdown.Coercive.StretchInternal.contDiff_intervalIntegral_param` (`Breakdown/Cert/CoerciveStretch.lean:312`).

**Theorem: A component of a C2 field is C2.** Each real coordinate of the stated twice continuously differentiable field is twice continuously differentiable. Source: `Breakdown.Coercive.StretchInternal.contDiff_component` (`Breakdown/Cert/CoerciveStretch.lean:352`).

**Theorem: C2 regularity of rotated field or vector.** Under the stated hypotheses, the rotated field or vector has continuous derivatives through order $2$. Source: `Breakdown.Coercive.StretchInternal.axialRot_comp` (`Breakdown/Cert/CoerciveStretch.lean:357`).

**Theorem: C2 regularity of mean model field.** Under the stated hypotheses, the mean model field has continuous derivatives through order $2$. Source: `Breakdown.Coercive.StretchInternal.meanField_contDiff` (`Breakdown/Cert/CoerciveStretch.lean:368`).

**Theorem: The mean vorticity gradient is traceless.** The three diagonal entries of the mean-field vorticity gradient sum to zero. Source: `Breakdown.Coercive.StretchInternal.meanVortCoord_trace` (`Breakdown/Cert/CoerciveStretch.lean:395`).

**Definition: Velocity along a time-angular orbit.** The fibre velocity is one coordinate of the field pulled back by time shift and axial rotation. Source: `Breakdown.Coercive.StretchInternal.fibVel` (`Breakdown/Cert/CoerciveStretch.lean:400`).

**Definition: Gradient along a time-angular orbit.** The fibre gradient rotates the input and output coordinates of the gradient along the time-angular orbit. Source: `Breakdown.Coercive.StretchInternal.fibGrad` (`Breakdown/Cert/CoerciveStretch.lean:403`).

**Definition: Curl from matrix coordinates.** The coordinate curl contracts the matrix entries with the three-dimensional alternating symbol. Source: `Breakdown.Coercive.StretchInternal.curlMat` (`Breakdown/Cert/CoerciveStretch.lean:406`).

**Definition: The stretching bound on an orbit.** The orbit bound collects strain, mixed mean-vorticity and balanced wave-gradient charges in physical coordinates. Source: `Breakdown.Coercive.StretchInternal.fibreBound` (`Breakdown/Cert/CoerciveStretch.lean:409`).

**Definition: The axial rotation matrix.** The rotation-matrix entry is the indicated coordinate of a rotated coordinate unit vector. Source: `Breakdown.Coercive.StretchInternal.rm` (`Breakdown/Cert/CoerciveStretch.lean:418`).

**Theorem: The axial rotation matrix.** The coordinate rotation matrix has the standard planar sine-cosine block and fixes the third coordinate. Source: `Breakdown.Coercive.StretchInternal.rm_eq` (`Breakdown/Cert/CoerciveStretch.lean:420`).

**Definition: Rotate both matrix indices.** The conjugated matrix is the original matrix multiplied on both sides by the axial rotation and its transpose. Source: `Breakdown.Coercive.StretchInternal.conjM` (`Breakdown/Cert/CoerciveStretch.lean:424`).

**Definition: Rotate a coordinate vector.** The coordinate rotation multiplies the vector by the axial rotation matrix. Source: `Breakdown.Coercive.StretchInternal.rotVec` (`Breakdown/Cert/CoerciveStretch.lean:427`).

**Definition: Apply the transposed rotation.** The transposed rotation contracts the vector with the columns of the axial rotation matrix. Source: `Breakdown.Coercive.StretchInternal.rotT` (`Breakdown/Cert/CoerciveStretch.lean:429`).

**Theorem: Curl commutes with matrix rotation.** The curl of the rotated matrix is the rotated curl of the original matrix. Source: `Breakdown.Coercive.StretchInternal.curlMat_conjM` (`Breakdown/Cert/CoerciveStretch.lean:431`).

**Theorem: Rotation preserves a vector square sum.** The sum of squared coordinates is unchanged by the coordinate rotation matrix. Source: `Breakdown.Coercive.StretchInternal.sq_rotVec` (`Breakdown/Cert/CoerciveStretch.lean:436`).

**Theorem: Transpose rotation preserves squares.** The transpose rotation matrix preserves the sum of squared vector coordinates. Source: `Breakdown.Coercive.StretchInternal.sq_rotT` (`Breakdown/Cert/CoerciveStretch.lean:441`).

**Theorem: Matrix rotation preserves entry energy.** Conjugation by the coordinate rotation matrix preserves the sum of squared matrix entries. Source: `Breakdown.Coercive.StretchInternal.sq_conjM` (`Breakdown/Cert/CoerciveStretch.lean:446`).

**Theorem: Rotate a quadratic form's argument.** The quadratic form of the conjugated matrix at a vector equals the original matrix's quadratic form at the transpose-rotated vector. Source: `Breakdown.Coercive.StretchInternal.quad_conjM` (`Breakdown/Cert/CoerciveStretch.lean:452`).

**Theorem: The mixed form is rotation invariant.** Simultaneously rotating the vector and conjugating both matrices leaves the mixed stretching form unchanged. Source: `Breakdown.Coercive.StretchInternal.bilin_conjM` (`Breakdown/Cert/CoerciveStretch.lean:458`).

**Theorem: Reconstruct the original matrix entries.** Conjugating the matrix expressed in pulled-back rotated coordinates recovers the original linear-map entries. Source: `Breakdown.Coercive.StretchInternal.clm_coord_conj` (`Breakdown/Cert/CoerciveStretch.lean:464`).

**Theorem: Reconstruct the original vector.** Rotating the pulled-back vector coordinates recovers the original vector coordinates. Source: `Breakdown.Coercive.StretchInternal.vec_coord_rot` (`Breakdown/Cert/CoerciveStretch.lean:470`).

**Definition: Axial rotation as a continuous map.** The continuous linear map is the linear-isometric axial rotation in operator form. Source: `Breakdown.Coercive.StretchInternal.rotCLM` (`Breakdown/Cert/CoerciveStretch.lean:475`).

**Theorem: Evaluate the linear rotation map.** The continuous linear rotation map agrees with the axial rotation of the vector. Source: `Breakdown.Coercive.StretchInternal.rotCLM_apply` (`Breakdown/Cert/CoerciveStretch.lean:478`).

**Theorem: Differentiate an equivariant field.** For the stated axially equivariant field, the derivative at a rotated point is the conjugated derivative at the original point. Source: `Breakdown.Coercive.StretchInternal.fderiv_equivariant` (`Breakdown/Cert/CoerciveStretch.lean:480`).

**Definition: Matrix coordinates of an operator.** The matrix entries are the coordinates of the operator applied to coordinate unit vectors. Source: `Breakdown.Coercive.StretchInternal.coordMat` (`Breakdown/Cert/CoerciveStretch.lean:499`).

**Theorem: The two curl formulas agree.** The continuous-linear-map curl equals the coordinate-matrix curl of that map. Source: `Breakdown.Coercive.StretchInternal.curlVec_eq_curlMat` (`Breakdown/Cert/CoerciveStretch.lean:501`).

**Theorem: The two rotation formulas agree.** Axial rotation of a spatial vector agrees coordinatewise with multiplication by the coordinate rotation matrix. Source: `Breakdown.Coercive.StretchInternal.axialRot_eq_rotVec` (`Breakdown/Cert/CoerciveStretch.lean:505`).

**Theorem: The half-open orbit box has full measure.** Almost every point for the time-angle box measure lies in the stated half-open time and angle intervals. Source: `Breakdown.Coercive.StretchInternal.box_ae_mem` (`Breakdown/Cert/CoerciveStretch.lean:508`).

**Theorem: Integrability of function f.** Under the stated hypotheses, the function $f$ is integrable. Source: `Breakdown.Coercive.StretchInternal.integrable_box_of_continuous` (`Breakdown/Cert/CoerciveStretch.lean:515`).

**Theorem: The mean field is axially equivariant.** Evaluating the mean model field at a rotated point rotates its value by the same angle. Source: `Breakdown.Coercive.StretchInternal.meanField_rot` (`Breakdown/Cert/CoerciveStretch.lean:523`).

**Theorem: Rotate the mean-field gradient.** The mean-field gradient at a rotated point is the conjugate of its gradient at the original point. Source: `Breakdown.Coercive.StretchInternal.meanGrad_rot` (`Breakdown/Cert/CoerciveStretch.lean:538`).

**Theorem: The curl of a C2 field is differentiable.** The stated second-order regularity of the field makes the curl of its derivative differentiable. Source: `Breakdown.Coercive.StretchInternal.differentiable_curl_fderiv` (`Breakdown/Cert/CoerciveStretch.lean:545`).

**Theorem: The mean curl is axially equivariant.** The curl of the mean model field at a rotated point is the rotation of its curl at the original point. Source: `Breakdown.Coercive.StretchInternal.meanCurl_rot` (`Breakdown/Cert/CoerciveStretch.lean:555`).

**Theorem: Rotate the mean vorticity gradient.** The mean-field vorticity-gradient matrix at a rotated point is the conjugated matrix at the original point. Source: `Breakdown.Coercive.StretchInternal.meanVortCoord_rot` (`Breakdown/Cert/CoerciveStretch.lean:564`).

**Theorem: The Hessian gives the curl derivative.** The defined contraction of the second derivative equals the corresponding coordinate derivative of the field's curl. Source: `Breakdown.Coercive.StretchInternal.vortGrad_eq` (`Breakdown/Cert/CoerciveStretch.lean:571`).

**Theorem: A quadratic form in coordinates.** The symmetric-part quadratic form at the coordinate-expanded vector equals the stated entrywise quadratic expression. Source: `Breakdown.Coercive.StretchInternal.symPartForm_coord` (`Breakdown/Cert/CoerciveStretch.lean:585`).

**Theorem: Euclidean norm in coordinates.** The squared Euclidean norm is the sum of the squared real coordinates. Source: `Breakdown.Coercive.StretchInternal.norm_sq_coord` (`Breakdown/Cert/CoerciveStretch.lean:590`).

**Theorem: Absorb a product with a positive weight.** For a positive weight, a product is at most half the weighted first square plus the reciprocally weighted second square. Source: `Breakdown.Coercive.StretchInternal.mul_le_half_sq_add` (`Breakdown/Cert/CoerciveStretch.lean:594`).

**Theorem: Bound stretching along each orbit.** The negative stretching density at each rotated point is bounded by the constructed time-angle fibre bound under the stated model and positive-length assumptions. Source: `Breakdown.Coercive.StretchInternal.fibre_pointwise` (`Breakdown/Cert/CoerciveStretch.lean:601`).

**Theorem: Rotation-matrix entries are continuous.** Each entry of the coordinate rotation matrix depends continuously on its angle. Source: `Breakdown.Coercive.StretchInternal.continuous_rm` (`Breakdown/Cert/CoerciveStretch.lean:698`).

**Theorem: Each rotation entry has magnitude ≤1.** Every entry of the coordinate rotation matrix has absolute value at most one. Source: `Breakdown.Coercive.StretchInternal.abs_rm_le` (`Breakdown/Cert/CoerciveStretch.lean:701`).

**Theorem: Expand the pulled-back fibre velocity.** The fibre velocity is the inverse rotation matrix applied to the field at the rotated spatial point. Source: `Breakdown.Coercive.StretchInternal.fibVel_eq` (`Breakdown/Cert/CoerciveStretch.lean:705`).

**Theorem: Expand the pulled-back fibre gradient.** The fibre gradient is the original gradient at the rotated point with inverse output rotation and forward input rotation. Source: `Breakdown.Coercive.StretchInternal.fibGrad_eq` (`Breakdown/Cert/CoerciveStretch.lean:710`).

**Theorem: A bounded coefficient preserves L2.** Multiplying the $L^2$ time-angle function by the stated bounded measurable coefficient preserves membership in $L^2$. Source: `Breakdown.Coercive.StretchInternal.memLp_coeff_mul` (`Breakdown/Cert/CoerciveStretch.lean:717`).

**Theorem: A vector coordinate belongs to L2.** The selected coordinate of the stated vector-valued time-angle field belongs to $L^2$. Source: `Breakdown.Coercive.StretchInternal.memLp_coord` (`Breakdown/Cert/CoerciveStretch.lean:724`).

**Theorem: The fibre velocity coordinate is in L2.** Under the stated hypotheses, the rotated velocity coordinate belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.StretchInternal.memLp_fibVel` (`Breakdown/Cert/CoerciveStretch.lean:730`).

**Theorem: The fibre gradient entry is in L2.** Under the stated hypotheses, the rotated gradient coordinate belongs to $L^2$ for the displayed measure. Source: `Breakdown.Coercive.StretchInternal.memLp_fibGrad` (`Breakdown/Cert/CoerciveStretch.lean:743`).

**Theorem: The fibre curl coordinate belongs to L2.** Each curl coordinate of the pulled-back fibre gradient belongs to $L^2$ on the time-angle box. Source: `Breakdown.Coercive.StretchInternal.memLp_fibCurl` (`Breakdown/Cert/CoerciveStretch.lean:760`).

**Theorem: Velocity modes from fibre coordinates.** A velocity-mode coordinate at base time zero is the Fourier average of the corresponding pulled-back fibre velocity coordinate. Source: `Breakdown.Coercive.StretchInternal.modeVel_eq_fib` (`Breakdown/Cert/CoerciveStretch.lean:766`).

**Theorem: Gradient modes from fibre coordinates.** A gradient-mode entry at base time zero is the Fourier average of the corresponding pulled-back fibre gradient entry. Source: `Breakdown.Coercive.StretchInternal.modeGrad_eq_fib` (`Breakdown/Cert/CoerciveStretch.lean:770`).

**Theorem: Curl modes from the fibre gradient.** The curl of a gradient mode is the Fourier average of the curl of the pulled-back fibre gradient. Source: `Breakdown.Coercive.StretchInternal.curlMode_eq_fib` (`Breakdown/Cert/CoerciveStretch.lean:776`).

**Theorem: Norm squared through conjugation.** A complex number's squared norm is the real part of its product with its conjugate. Source: `Breakdown.Coercive.StretchInternal.norm_sq_eq_re` (`Breakdown/Cert/CoerciveStretch.lean:793`).

**Theorem: Parseval for a weighted bilinear form.** The coefficient-weighted real pairings of matching Fourier modes sum to the normalised time-angle integral of the original bilinear form. Source: `Breakdown.Coercive.StretchInternal.hasSum_bil` (`Breakdown/Cert/CoerciveStretch.lean:797`).

**Theorem: Parseval for a finite coordinate family.** The sum of squared Fourier-mode norms over the finite coordinate family sums to its normalised time-angle square integral. Source: `Breakdown.Coercive.StretchInternal.hasSum_sqsum` (`Breakdown/Cert/CoerciveStretch.lean:821`).

**Definition: Coefficients of the mixed form.** The coefficient is the mixed-form kernel evaluated on a coordinate unit input. Source: `Breakdown.Coercive.StretchInternal.bc` (`Breakdown/Cert/CoerciveStretch.lean:833`).

**Theorem: Expand the mixed form's coefficients.** The mixed stretching form is the finite coefficient-weighted sum of velocity coordinates times gradient entries. Source: `Breakdown.Coercive.StretchInternal.bilin_coeff` (`Breakdown/Cert/CoerciveStretch.lean:836`).

**Theorem: Expand the complex mixed coefficients.** The modewise mixed stretching form is the coefficient-weighted sum of real parts of velocity modes times conjugate gradient modes. Source: `Breakdown.Coercive.StretchInternal.modeBilin_coeff` (`Breakdown/Cert/CoerciveStretch.lean:846`).

**Theorem: Parseval for the stretching fibre bound.** For almost every spatial point, the fibre bound is time-angle integrable and its normalised integral is the sum of the fibre terms. Source: `Breakdown.Coercive.StretchInternal.fibre_squareSum` (`Breakdown/Cert/CoerciveStretch.lean:855`).

**Theorem: Reduce stretching to a mode sum.** For almost every spatial point, the fibre terms are summable and $2\pi$ times their sum bounds the negative time-angle integral of stretching. Source: `Breakdown.Coercive.StretchInternal.fibre_reduction` (`Breakdown/Cert/CoerciveStretch.lean:961`).

**Theorem: Bound stretching by mode charges.** The fibrewise Parseval reduction and stretching bounds supply the mean-stretching interface. Source: `Breakdown.Coercive.stretchMeanBoundHolds_proof_of` (`Breakdown/Cert/CoerciveStretch.lean:992`).

### Breakdown.Cert.CoerciveStretchFibre

The spatial stretching estimate is first organized along time-angle fibres. This file proves the null-set, measurability and quadratic bounds needed to integrate those rotated fibres. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Rotation preserves null fibres** · theorem. `quasiMeasurePreserving_fibreMap`: The time-angle rotation map pulls back null sets to null sets under the axial-rotation hypothesis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchFibre.lean#L15).

**Square-integrable rotated fibres** · theorem. `ae_memLp_fibre`: Joint measurability and local square-integrability give square-integrable time-angle fibres for almost every spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchFibre.lean#L43).

**Square-integrable velocity fibres** · theorem. `ae_memLp_fibre_vel`: The perturbation's local square-integrability gives square-integrable rotated velocity fibres almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchFibre.lean#L114).

**Square-integrable gradient fibres** · theorem. `ae_memLp_fibre_grad`: Each gradient column has square-integrable rotated time-angle fibres almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchFibre.lean#L122).

### Breakdown.Cert.CoerciveStretchIntegrable

Before a Fourier estimate can be integrated, the physical stretching expression must be integrable. These bounds connect derivative decay and perturbation energy to that requirement. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Restricting a joint derivative** · theorem. `partial_fderiv_eq`: The spatial derivative of a slice is the joint derivative composed with the spatial-coordinate inclusion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L15).

**Continuity of the spatial derivative** · theorem. `continuous_partial_fderiv`: The spatial derivative varies continuously with time and position under the joint differentiability hypothesis. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L20).

**Continuous slice derivatives** · theorem. `Breakdown.Cert.CoerciveStretchIntegrable.continuous_fderiv_slice`: The first spatial derivative varies continuously with the time-space point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L30).

**Continuous second slice derivatives** · theorem. `continuous_fderiv2_slice`: The second spatial derivative varies continuously with time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L35).

**Operator norm from matrix energy** · theorem. `opNorm_sq_le_matSq`: The squared operator norm is at most three times the sum of squared matrix-column norms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L53).

**Time-angle box membership** · theorem. `box_ae_mem'`: Almost every point for the box measure lies in the closed time-angle rectangle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L77).

**Stretching on one rotated fibre** · definition. `fibreStretch`: The fibre stretching form evaluates the velocity-gradient pair after axial rotation at a fixed spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L85).

**Continuous fibre stretching** · theorem. `continuous_fibreStretch`: The fibre stretching form is continuous in its time-angle and velocity-gradient inputs. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L89).

**Curl respects scalar multiplication** · theorem. `curlVec_smul`: Multiplying a matrix by a real scalar multiplies its curl vector by the same scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L109).

**Quadratic scaling of stretching** · theorem. `fibreStretch_smul`: Scaling the velocity-gradient pair scales the fibre stretching form by the square of that scalar. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L122).

**A quadratic fibre bound** · theorem. `fibreStretch_bound`: On the time-angle box, the absolute fibre stretching form has a uniform bound by the squared norm of its vector-matrix input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L141).

**Integrable fibre stretching** · theorem. `fibre_stretch_integrable`: The stretching form is integrable over the time-angle box for almost every spatial point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchIntegrable.lean#L167).

### Breakdown.Cert.CoerciveStretchTorus

This file transfers the stretching form from a time-angle rectangle to the compact two-torus. Its period and measure identities make the Fourier-side argument apply to the physical integral. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Closed and half-open box measures** · theorem. `box_eq`: The product of the two closed-interval restrictions agrees with the box measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L15).

**A real sum from nonnegative terms** · theorem. `hasSum_of_ennreal`: The nonnegative extended-real summation identity yields the corresponding real-valued sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L22).

**Parseval on the time-angle box** · theorem. `hasSum_sq`: The squared mode coefficients sum to the normalized square integral over the time-angle box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L36).

**Integrable Fourier integrands** · theorem. `integrable_exp_mul`: Multiplying the real fibre function by the unit-modulus Fourier factor preserves integrability on the box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L61).

**Mode average as a box integral** · theorem. `modeAverage_eq_box`: A mode average is the time-angle box integral with the Fourier factor and normalization by two pi. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L68).

**Linearity of mode averages** · theorem. `modeAverage_lin`: Mode averaging respects addition and real scalar multiplication. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L75).

**Polarizing a complex product** · theorem. `re_mul_conj`: The real part of a complex product with a conjugate is the difference of two squared norms divided by four. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L93).

**Parseval for two real fibres** · theorem. `torus_hasSum_mul`: Products of paired mode coefficients sum to the normalized integral of the two real fibre functions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStretchTorus.lean#L100).

### Breakdown.Cert.CoerciveTestDensity

The coercivity proof needs tests dense in the relevant divergence-free Hilbert space. This file states the test-density interfaces and the exact closure statements used downstream. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Gradient and solenoidal separation** · interface proposition. `GradSolenoidalDensityHolds`: This proposition requires a periodic square-integrable field annihilating both gradient and solenoidal tests to vanish almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensity.lean#L12).

Proved by `Breakdown.Coercive.gradSolenoidalDensityHolds_proof`.

**Density in velocity and curl** · interface proposition. `CurlGraphDensityHolds`: This proposition requires periodic solenoidal test fields approximating a solenoidal component together with the original field's curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensity.lean#L20).

Proved by `Breakdown.Coercive.curlGraphDensityHolds_proof`.

### Breakdown.Cert.CoerciveTestDensityCurl

Curl-generated smooth tests give a concrete route to density. This file develops their derivative identities, compact support and orthogonality properties. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Coercive.Internal.CurlGraphDensity`.**

**Approximation in velocity and curl** · theorem. `exists_solenoidalPart_approx`: There is a sequence of periodic solenoidal tests converging to the solenoidal component and to the original curl in squared integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L15).

**Congruence of period integrals** · theorem. `periodLIntegral_congr`: Pointwise equality of integrands preserves the nonnegative integral over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L25).

**Finite periodic square integral** · theorem. `lt_top_of_memLp`: Square-integrability for the period measure makes the nonnegative periodic square integral finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L38).

**Square-integrability from support** · theorem. `Breakdown.Cert.CoerciveTestDensityCurl.memLp_of_continuous`: A continuous field with a uniform compact spatial support is square-integrable over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L46).

**A derivative in the spatial direction** · theorem. `Breakdown.Cert.CoerciveTestDensityCurl.slice_fderiv_apply`: Applying a slice derivative equals applying the joint derivative to a vector with zero time component. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L74).

**Continuous spatial gradients** · theorem. `gradient_continuous`: The potential's spatial gradient varies continuously in time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L83).

**The gradient vanishes off support** · theorem. `gradient_vanish`: The spatial gradient vanishes outside the radius where the smooth potential is identically zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L96).

**Pairing a difference of fields** · theorem. `pairing_sub`: The period pairing of a difference is the difference of the two period pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L105).

**Unique solenoidal component** · theorem. `solenoidalPart_unique`: Two solenoidal components of the same field agree almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L128).

**Source namespace `Breakdown.Coercive`.**

**Prove density in velocity and curl** · theorem. `curlGraphDensityHolds_proof`: The solenoidal approximation construction proves the velocity-and-curl density interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurl.lean#L148).

### Breakdown.Cert.CoerciveTestDensityCurlApprox

This file assembles cutoff and smoothing estimates into approximation by admissible curl tests. The approximation is the input to the closed-span density argument. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Coercive.Internal.CurlGraphMollify`.**

**Smoothing converges in square norm** · theorem. `moll_tendsto_of_seq`: The smoothed field converges to the field in periodic squared integral using its approximating test sequence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApprox.lean#L17).

**Source namespace `Breakdown.Coercive`.**

**Construct the curl approximation** · theorem. `exists_solenoidalPart_approx_core`: Smoothing the solenoidal approximation produces periodic tests converging both in velocity and in curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApprox.lean#L57).

### Breakdown.Cert.CoerciveTestDensityCurlApproxBase

The curl approximation begins with cutoffs, mollifiers and a period-measure L² representation. This file fixes those objects and their basic support and regularity properties. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A shrinking spatial bump** · definition. `bump`: The spatial bump has inner radius 1/(k + 2) and outer radius 1/(k + 1). [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L14).

**The normalized smoothing kernel** · definition. `kern`: The spatial bump is normalized by its volume integral to define the smoothing kernel. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L18).

**Spatial smoothing by convolution** · definition. `moll`: The smoothed field is obtained by convolving each spatial time slice with the normalized kernel. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L20).

**A single period-space integral** · theorem. `periodLIntegral_eq_lintegral`: The iterated nonnegative period integral equals integration against the product period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L23).

**Almost-everywhere period congruence** · theorem. `periodLIntegral_congr_ae`: Integrands equal almost everywhere for the period measure have equal nonnegative period integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L29).

**A squared triangle estimate** · theorem. `periodLIntegral_tri`: The squared period distance through an intermediate field is bounded by twice each of the two squared distances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L39).

**Square-integrability from support** · theorem. `Breakdown.Cert.CoerciveTestDensityCurlApproxBase.memLp_of_continuous`: A continuous field with a uniform compact spatial support is square-integrable over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L71).

**Symmetry of squared period distance** · theorem. `periodLIntegral_sub_comm`: Exchanging two fields leaves their periodic squared difference unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L100).

**Reciprocal indices tend to zero** · theorem. `tendsto_inv_succ`: The extended nonnegative reciprocals of successive positive integers tend to zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBase.lean#L105).

### Breakdown.Cert.CoerciveTestDensityCurlApproxBound

The cutoff approximation requires quantitative control on its derivative errors. These local bounds supply integrable majorants and show that the unwanted terms vanish. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Coercive.Internal.CurlGraphMollify.BoundInternal`.**

**Weighted Cauchy-Schwarz** · theorem. `sq_lintegral_mul_le`: The square of a weighted nonnegative integral is bounded by the weight's integral times the weighted square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L17).

**A convolution square bound** · theorem. `lintegral_conv_sq_le`: The squared integral of a convolution is bounded by the kernel's squared integral norm times the field's square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L44).

**Two readings of squared norm** · theorem. `ofReal_sq_norm`: The extended-real image of a squared norm equals the square of its extended norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L84).

**The kernel is continuous** · theorem. `kern_continuous`: The normalized smoothing kernel is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L87).

**The kernel has compact support** · theorem. `kern_compact`: The normalized smoothing kernel has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L89).

**The kernel is smooth** · theorem. `kern_smooth`: The normalized smoothing kernel is infinitely differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L91).

**The kernel has total mass one** · theorem. `lintegral_kern`: The nonnegative integral of the kernel's norm equals one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L93).

**The smoothing integral** · theorem. `moll_apply`: Spatial smoothing evaluates to the integral of the kernel times the translated field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L102).

**Subtracting two smoothed slices** · theorem. `moll_sub_slice`: The difference of two smoothed slices is the kernel integral of the difference of their translated fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L106).

**Smoothing contracts square distance** · theorem. `slice_sq_le`: Smoothing does not increase the spatial squared distance between two slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L117).

**Curl from column differences** · theorem. `norm_curlVec_sub_le`: The difference of curl vectors is bounded by a fixed multiple of the sum of matrix-column differences. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L128).

**Squaring a three-term sum** · theorem. `sq_sum_three_le`: The squared sum of three real terms is at most three times their sum of squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L157).

**A derivative of the smoothing kernel** · definition. `dker`: The derivative kernel is the directional derivative of the smoothing kernel along one coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L161).

**The derivative kernel is continuous** · theorem. `dker_continuous`: The directional derivative of the smoothing kernel is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L163).

**Compact derivative-kernel support** · theorem. `dker_compact`: The directional derivative of the smoothing kernel has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L166).

**An integrable derivative kernel** · theorem. `lintegral_dker_lt_top`: The nonnegative integral of the derivative kernel's norm is finite. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L170).

**Differentiate the smoothing kernel** · theorem. `fderiv_moll_apply`: A spatial derivative of a smoothed slice is the convolution with the corresponding derivative kernel. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L173).

**Derivative of a smoothed difference** · theorem. `dker_sub_slice`: The difference of two smoothed derivatives is the derivative-kernel integral of the translated field difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L185).

**A square bound for smoothed curl** · theorem. `curl_slice_sq_le`: The squared distance between smoothed curls is bounded by derivative-kernel integrals times the original squared slice distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L197).

**Source namespace `Breakdown.Coercive.Internal.CurlGraphMollify`.**

**Periodic smoothing contraction** · theorem. `moll_sub_le`: Spatial smoothing does not increase the periodic squared distance between two fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L244).

**A bound for smoothed curl differences** · theorem. `curl_moll_sub_le`: For each smoothing scale, a finite constant bounds periodic squared curl differences by periodic squared field differences. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxBound.lean#L254).

### Breakdown.Cert.CoerciveTestDensityCurlApproxMollify

Spatial smoothing is used to replace rough compactly supported fields by smooth ones. The convergence and curl identities here keep that replacement compatible with the test class. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Curl as a continuous linear map** · theorem. `exists_curl_clm`: The matrix-to-curl operation is represented by a continuous linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L14).

**Trace as a continuous linear map** · theorem. `exists_div_clm`: The sum of diagonal matrix entries is represented by a continuous linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L27).

**Smoothness of the spatial kernel** · theorem. `kern_contDiff`: The normalized smoothing kernel is infinitely differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L35).

**Compact support of the kernel** · theorem. `kern_hasCompactSupport`: The normalized smoothing kernel has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L37).

**Local integrability of the kernel** · theorem. `kern_locallyIntegrable`: The normalized smoothing kernel is locally integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L39).

**The kernel vanishes outside its ball** · theorem. `kern_eq_zero`: The smoothing kernel vanishes at every spatial point whose norm is at least one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L42).

**Support of a smoothed field** · theorem. `moll_vanish`: The smoothed field vanishes beyond the original support radius enlarged by the kernel radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L52).

**Slice derivatives from joint ones** · theorem. `slice_fderiv_eq`: The slice derivative is the joint derivative composed with inclusion of the spatial coordinates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L65).

**Continuous slice derivative field** · theorem. `continuous_slice_fderiv`: The field of spatial slice derivatives is continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L74).

**Continuous slice curls** · theorem. `continuous_slice_curl`: The curl of each spatial slice varies continuously with time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L84).

**Measurability of smooth curls** · theorem. `aestronglyMeasurable_curl_of_contDiff`: The spatial curl of a sufficiently differentiable joint field is almost everywhere strongly measurable for the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L91).

**Smoothing preserves periodic tests** · theorem. `isPeriodicTestField_moll`: Smoothing a periodic solenoidal test field again gives a periodic solenoidal test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L96).

**Translation preserves null sets** · theorem. `quasiMeasurePreserving_shear`: The product-space subtraction map pulls period-measure null sets back to null sets. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L136).

**Measurability of convolution** · theorem. `aestronglyMeasurable_conv_param`: The spatial convolution depending on time is almost everywhere strongly measurable for the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L149).

**Measurability of smoothed fields** · theorem. `aestronglyMeasurable_moll`: The smoothed field is almost everywhere strongly measurable on one time period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L164).

**Square-integrable time slices** · theorem. `slice_memLp'`: Almost every time slice of a period-square-integrable field is spatially square-integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L169).

**Measurability of smoothed curls** · theorem. `aestronglyMeasurable_curl_moll`: The spatial curl of the smoothed field is almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L176).

**Uniform approximation by smoothing** · theorem. `moll_uniform`: At sufficiently fine scales, smoothing approximates a periodic test field uniformly over one period and all space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L193).

**A periodic smoothing-error bound** · theorem. `moll_bound`: The periodic squared smoothing error is bounded by the uniform error squared times the enlarged support-ball volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L229).

**Smoothing converges for test fields** · theorem. `moll_tendsto_of_continuous`: Smoothing a continuous periodic test field converges in periodic squared integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L254).

**Scalar multiplication after precompose** · theorem. `precompR_lsmul_apply`: Precomposing the scalar-multiplication map gives ordinary scalar multiplication on the resulting input. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L273).

**Curl commutes with smoothing** · theorem. `curl_moll_eq`: The curl of a smoothed field equals the smoothing of its curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L278).

**Smoothed curls converge** · theorem. `curl_moll_tendsto`: The curls of the smoothed fields converge to the original curl in periodic squared integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxMollify.lean#L298).

### Breakdown.Cert.CoerciveTestDensityCurlApproxOrthogonal

Density is proved through the orthogonal complement of the curl-test span. This file turns orthogonality to approximating curls into the required vanishing conclusion. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**A translated kernel potential** · definition. `testPot`: The test potential multiplies a translated reversed kernel by one coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L14).

**Curl of the kernel potential** · definition. `testCurl`: The test field is the curl of the translated kernel potential. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L16).

**Smoothness of the kernel** · theorem. `contDiff_kern`: The normalized spatial kernel is infinitely differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L18).

**The kernel is compactly supported** · theorem. `hasCompactSupport_kern`: The normalized spatial kernel has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L20).

**Smoothness of the test potential** · theorem. `contDiff_testPot`: The translated kernel potential is infinitely differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L22).

**Compact support of the potential** · theorem. `hasCompactSupport_testPot`: The translated kernel potential has compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L25).

**The kernel curl is a test field** · theorem. `isTestField_testCurl`: The curl of the translated kernel potential is a smooth compactly supported solenoidal test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L31).

**Derivative of the kernel potential** · theorem. `fderiv_testPot`: Differentiating the reversed translated kernel introduces a minus sign in the directional derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L35).

**One curl coordinate as a linear map** · definition. `curlComp`: A curl coordinate is the alternating sum of matrix entries packaged as a continuous linear functional. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L45).

**Reading a curl coordinate** · theorem. `curlVec_apply`: Applying the curl-coordinate functional gives the corresponding coordinate of the curl vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L49).

**Expand the kernel-curl pairing** · theorem. `inner_testCurl`: Pairing a vector with the kernel test curl expands into alternating-symbol weighted derivative terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L52).

**A curl coordinate as a pairing** · theorem. `curl_conv_apply`: A coordinate of the smoothed curl equals the integral pairing with the kernel test curl. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L58).

**Solenoidal pairings on time slices** · theorem. `slice_orth`: Almost every time slice of a solenoidal component has the same pairing against a spatial test field as the original field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L75).

**Continuity of a convolution curl** · theorem. `continuous_curl_conv`: The curl of the spatial convolution is continuous in position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L95).

**Smoothing retains the original curl** · theorem. `curl_moll_solenoidal_part`: The smoothed solenoidal component and the smoothed original field have equal curls almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxOrthogonal.lean#L111).

### Breakdown.Cert.CoerciveTestDensityCurlApproxProjection

The density proof moves between physical integrals and projected Hilbert-space tests. This file proves that the period L² pairings and the test projection have the required compatibility. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Differentiability of spatial slices** · theorem. `Breakdown.Cert.CoerciveTestDensityCurlApproxProjection.slice_contDiff`: Joint differentiability implies the corresponding differentiability of each fixed-time spatial slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L14).

**A spatial slice derivative** · theorem. `slice_fderiv`: The derivative of a fixed-time spatial slice is obtained by inserting a zero time component into the joint derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L19).

**Support contained in a ball** · theorem. `hasCompactSupport_of_bound`: Vanishing beyond a fixed radius gives compact support. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L26).

**The zero periodic test field** · theorem. `isPeriodicTestField_zero`: The zero field satisfies the periodic solenoidal test-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L31).

**Adding periodic test fields** · theorem. `isPeriodicTestField_add`: The sum of two periodic solenoidal test fields is again such a test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L34).

**Scaling periodic test fields** · theorem. `isPeriodicTestField_smul`: A real multiple of a periodic solenoidal test field remains a periodic solenoidal test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L52).

**Periodic tests are square integrable** · theorem. `memLp_of_test`: A periodic solenoidal test field is square-integrable for the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L59).

**Identify a square-integrable field** · theorem. `toL2_eq_of_ae`: An almost-everywhere representative of an L² element gives that same element under the field-to-L² conversion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L63).

**The space of periodic test fields** · definition. `testSubmodule`: The L² classes represented by periodic solenoidal test fields form a real submodule. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L68).

**Physical pairing as an inner product** · theorem. `Breakdown.Cert.CoerciveTestDensityCurlApproxProjection.pairing_eq_inner`: The integral pairing of the physical fields equals the inner product of their L² representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L86).

**Differentiate a coordinate** · theorem. `coord_fderiv`: Differentiating one vector coordinate equals taking that coordinate of the vector derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L100).

**Gradient pairing in coordinates** · theorem. `inner_gradient`: The pairing with a scalar gradient is the sum of coordinatewise directional-derivative pairings. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L106).

**Tests annihilate gradients** · theorem. `integral_inner_gradient`: A solenoidal spatial test field has zero integral pairing with a smooth compactly supported scalar gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L114).

**Continuity of the potential gradient** · theorem. `gradient_continuous'`: The potential's spatial gradient is jointly continuous in time and space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L157).

**Compact support of the gradient** · theorem. `gradient_bound`: The potential gradient vanishes outside the uniform spatial support radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L172).

**The L² norm as a square integral** · theorem. `Breakdown.Cert.CoerciveTestDensityCurlApproxProjection.lintegral_sq_eq`: The nonnegative integral of the representative's squared norm equals the squared L² norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L182).

**Approximate the solenoidal projection** · theorem. `exists_solenoidal_part_seq`: The solenoidal component is the periodic-square-integral limit of periodic solenoidal test fields. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityCurlApproxProjection.lean#L191).

### Breakdown.Cert.CoerciveTestDensityProof

The component density lemmas are assembled into the public test-density property. The result permits identities initially proved against smooth tests to identify the abstract operators. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Coercive.Internal.TestDensityProof`.**

**Measure on one time period** · abbreviation. `periodMeasure`: The period measure is the product of Lebesgue measure restricted to the unit time interval with spatial volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L15).

**A field's period L² class** · definition. `toL2`: A period-square-integrable field is sent to its L² class, with zero used when the integrability test fails. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L19).

**The L² class represents the field** · theorem. `coeFn_toL2`: Under square-integrability, the chosen representative of the period L² class agrees almost everywhere with the original field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L22).

**Period measure as a restriction** · theorem. `periodMeasure_eq`: The product period measure equals full time-space volume restricted to the unit-time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L28).

**Restricting field measurability** · theorem. `aestronglyMeasurable_period`: A jointly almost everywhere strongly measurable field stays so for the period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L32).

**A field in period L²** · theorem. `memLp_of`: The finite periodic square integral and measurability hypotheses put the field in period L². [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L38).

**Integer shifts preserve a period** · theorem. `periodic_int`: A one-periodic field is unchanged by every integer time shift. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L50).

**Extend zero across all periods** · theorem. `ae_of_period`: A periodic field vanishing almost everywhere on one period vanishes almost everywhere on all time-space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L55).

**Periodic extension of a bump** · definition. `periodicExt`: The compactly supported temporal bump is extended periodically by summing its integer translates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L82).

**Periodicity of the extension** · theorem. `periodicExt_add_one`: Adding one to time leaves the periodized temporal bump unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L84).

**A radius containing the support** · theorem. `exists_norm_bound`: A compactly supported spatial field vanishes beyond some radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L93).

**Locally finite translated supports** · theorem. `locallyFinite_translates`: The supports of the integer translates of the temporal bump form a locally finite family. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L101).

**Smoothness of the periodic extension** · theorem. `periodicExt_contDiff`: The periodized temporal bump is infinitely differentiable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L126).

**The extension on its base interval** · theorem. `periodicExt_eq`: Within the designated base interval, periodization agrees with the original temporal bump. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L134).

**Divergence respects scaling** · theorem. `divergenceAt_smul`: A constant real multiple of a vector field has the correspondingly scaled divergence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L148).

**A separated periodic test field** · theorem. `isPeriodicTestField_prod`: Multiplying a spatial solenoidal test by the periodized temporal bump gives a periodic solenoidal test field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L155).

**Gradient of a scaled potential** · theorem. `gradientAt_const_mul`: The gradient of a constant multiple of a scalar potential is the same multiple of its gradient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L164).

**A separated periodic potential** · theorem. `isPeriodicTestPotential_prod`: The product of a periodized temporal bump and a spatial test potential is a periodic test potential. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L172).

**Temporal tests detect zero** · theorem. `ae_zero_of_periodic_tests`: Vanishing against all permitted periodic temporal tests forces a time function to vanish almost everywhere on one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L179).

**A constant-in-time L² field** · theorem. `memLp_const_time`: A spatially square-integrable field defines a square-integrable field on the unit time strip. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L197).

**Integrable slice pairings** · theorem. `integrableOn_slicePairing`: The pairing of the time-dependent field with a fixed spatial L² test is integrable over one period. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L210).

**A common null-set for orthogonality** · theorem. `ae_forall_inner_zero`: Pointwise-in-test almost-everywhere orthogonality extends to simultaneous orthogonality over the separable test family. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L220).

**The physical L² pairing formula** · theorem. `inner_toLp_eq`: The inner product of two spatial L² classes is their integral physical pairing. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L233).

**Zero slices give a zero period field** · theorem. `ae_period_of_slices`: Almost-everywhere vanishing of the spatial slices implies almost-everywhere vanishing for the product period measure. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L241).

**A Fourier-weighted pairing vanishes** · theorem. `inner_zero_of_ssp_negSsp`: Orthogonality to the projected negative Laplacians of smooth tests implies orthogonality to every square-root Laplacian value in the second-order graph domain. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L263).

**Vanishing on frequency annuli** · theorem. `annulus_zero_of_negSsp`: Orthogonality to projected negative Laplacians of smooth tests forces the frequency representative to vanish almost everywhere on each positive-radius annulus. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L296).

**Fourier tests determine zero** · theorem. `eq_zero_of_negSsp_inner`: A homogeneous-space element orthogonal to the projected negative Laplacians of every admissible smooth test is zero. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L376).

**Select one real vector coordinate** · definition. `selectCLM`: The coordinate-selection map puts one chosen real coordinate into the first coordinate direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L398).

**L² fields have L² time slices** · theorem. `slice_memLp`: A period-square-integrable field has spatially square-integrable slices for almost every time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L401).

**Test gradients are square integrable** · theorem. `gradient_memLp`: The gradient of a spatial test potential belongs to spatial L². [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L408).

**A selected coordinate pairing** · theorem. `select_pairing`: The coordinate-selected field has zero integral pairing with the negative Laplacian of each scalar smooth test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L422).

**Integrable pairings of L² fields** · theorem. `integrable_inner_of_memLp'`: The pointwise inner product of two spatial L² fields is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L452).

**Differentiate a curl field** · theorem. `pd_curlField`: A directional derivative of curl expands as the corresponding sum of second directional derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L459).

**The double-curl algebra** · theorem. `curl_curl_algebra`: The alternating-symbol expansion of a double curl separates the Laplacian and gradient-of-divergence terms. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L471).

**Expand the gradient of divergence** · theorem. `gradient_divergence`: The gradient of divergence is the coordinate sum of the indicated second partial derivatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L480).

**The curl-curl Laplacian identity** · theorem. `negSsp_curl_curl`: The negative Laplacian of a smooth vector test equals its double curl minus the gradient of its divergence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L494).

**Annihilate the Laplacian test family** · theorem. `negSsp_pairing`: Orthogonality to gradient fields and solenoidal smooth tests forces zero pairing with the negative Laplacian of each smooth test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L506).

**Select one complex coordinate** · definition. `selectC`: The complex coordinate-selection map puts the chosen coordinate into the first coordinate direction. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L536).

**Coordinate selection complexifies** · theorem. `complexifyVec_select`: Complexifying after real coordinate selection equals complex coordinate selection after complexification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L539).

**Select a complexified L² coordinate** · theorem. `complexify_toLp_select`: Complexification commutes with the L² action of the coordinate-selection map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L544).

**Fourier transform commutes with maps** · theorem. `transform_comp_clm`: The Fourier transform commutes with a continuous linear map on the value space. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L562).

**Fourier maps on L² commute** · theorem. `freqTrR_compLpL`: The real L² Fourier transform commutes with the induced value-space linear map. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L573).

**A coordinate is nonzero almost surely** · theorem. `ae_ne_zero_coord`: The second coordinate of a spatial frequency is nonzero almost everywhere for volume. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L609).

**A longitudinal coordinate vanishes** · theorem. `coord_zero_of_longitudinal`: The given longitudinal relations and nonzero frequency coordinate force the selected vector coordinate to vanish. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L621).

**Coordinate selections detect zero** · theorem. `ae_zero_of_select`: Vanishing of every selected coordinate forces the physical vector field to vanish almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L645).

**Gradient and curl tests separate** · theorem. `slice_zero`: A spatial field annihilating the relevant gradient and solenoidal tests vanishes almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L682).

**Source namespace `Breakdown.Coercive`.**

**Prove joint test separation** · theorem. `gradSolenoidalDensityHolds_proof`: The slice argument proves that gradient and solenoidal periodic tests jointly determine a square-integrable field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTestDensityProof.lean#L696).

### Breakdown.Cert.CoerciveTorus

The periodic coercivity argument uses Fourier analysis on time and axial angle together. This file provides the torus transforms, coefficient identities and norm formulas needed for that comparison. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Source namespace `Breakdown.Coercive.TorusInternal`.**

**An angular Fourier coefficient** · definition. `sliceCoeff`: The slice coefficient is the angular Fourier coefficient at a fixed time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTorus.lean#L14).

**The interval Parseval identity** · theorem. `tsum_ofReal_sq_transformCoeffOn`: The extended-real sum of squared interval Fourier coefficients equals the normalized square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTorus.lean#L17).

**Iterated Fourier coefficients** · theorem. `modeAverage_eq`: A two-frequency mode average is the temporal Fourier coefficient of the angular coefficient. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTorus.lean#L32).

**Source namespace `Breakdown.Coercive`.**

**Prove torus Parseval** · theorem. `torusSquareSumHolds_proof`: Iterated interval Parseval proves the square-sum identity for time-angle modes. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveTorus.lean#L59).

### Breakdown.Cert.CompactPerturbation

The linearized inverse needs an abstract Fredholm ingredient: an injective compact perturbation of an isomorphism is again an isomorphism. This file proves that result for Banach spaces, including a sum of two compact perturbations. §7.7: coercivity and the linearized inverse, with analytic support lemmas

**Invert an injective compact perturbation** · theorem. `isUnit_one_add_of_isCompactOperator_of_injective`: An injective identity-plus-compact operator is invertible. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CompactPerturbation.lean#L7).

**A compact perturbation is an isomorphism** · theorem. `exists_equiv_of_injective_compact_perturbation`: An injective compact perturbation of a continuous linear equivalence is again a continuous linear equivalence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CompactPerturbation.lean#L27).

**Invert two compact perturbations** · theorem. `exists_equiv_of_injective_sum_compact_perturbation`: Adding the two compact perturbations to a continuous linear equivalence remains invertible when the sum is injective. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CompactPerturbation.lean#L48).

### Breakdown.Cert.Convection

The linearized convection field must become a bounded operator between the graph and forcing spaces. These definitions and estimates construct that operator from a smooth decaying profile. §§7.6–7.7: profile terms and the linearized operator

**Source namespace `Breakdown.Cert.Internal.Convection`.**

**Smooth decaying convection data** · structure. `IsCoefficient`: The coefficient condition requires joint twice differentiable periodic data with inverse-radius velocity decay and inverse-square gradient decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L18).

**The cubic norm of the decay weight** · definition. `weightCube`: The constant is the L³ norm of the inverse-square radial decay weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L24).

**The convection slice constant** · definition. `sliceConst`: The slice constant combines the coefficient bound, three gradient columns and the velocity embedding norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L26).

**The physical convection field** · definition. `readingConvection`: The physical convection field adds the perturbation gradient applied to the profile and the profile gradient applied to the perturbation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L28).

**The profile is a valid coefficient** · theorem. `isCoefficient_profile`: The certificate's approximate profile satisfies the smooth periodic decay conditions used for convection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L32).

**Measurable operator application** · theorem. `apply_aesm`: Applying an almost everywhere strongly measurable operator-valued field to a measurable vector field preserves that measurability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L43).

**Measurability of convection** · theorem. `Breakdown.Cert.Convection.aesm_readingConvection`: The physical convection field is jointly almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L50).

**The Hölder exponents three and six** · theorem. `exponentTriple_three_six`: The exponents three and six form a Hölder triple with target exponent two. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L60).

**A gradient column is bounded** · theorem. `norm_partialX_le`: The norm of a single gradient column is bounded by the homogeneous energy norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L70).

**The decay bound is nonnegative** · theorem. `Breakdown.Cert.Convection.coefficient_nonneg`: The coefficient hypotheses force the decay constant to be nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L78).

**Differentiability of spatial slices** · theorem. `Breakdown.Cert.Convection.slice_contDiff`: Joint differentiability implies the corresponding differentiability of each fixed-time spatial slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L83).

**The decay weight lies in L³** · theorem. `weight_memLp`: The inverse-square radial decay weight belongs to spatial L³. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L87).

**The transported-gradient bound** · theorem. `first_term`: For an admissible coefficient with decay constant D, each transported gradient column lies in L² with norm at most D times the perturbation norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L98).

**The profile-gradient bound** · theorem. `second_term`: The profile derivative applied to the perturbation velocity lies in L² with its Hölder and embedding bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L121).

**The convection slice bound** · theorem. `Breakdown.Cert.Convection.slice_bound`: The convection slice belongs to L² with norm bounded by the slice constant times the perturbation energy norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L165).

**Expand a vector in coordinates** · theorem. `eq_sum_unitVector`: A spatial vector is the sum of its three coordinate multiples of the unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L198).

**Expand a linear-map application** · theorem. `apply_eq_sum_unitVector`: Applying a linear map to a vector is the sum of the vector coordinates times the images of the unit vectors. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L202).

**Identify the convection formula** · theorem. `slice_pointwise`: The physical velocity-gradient expression equals the slice convection expression. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L207).

**Locally integrable gradient columns** · theorem. `locallyIntegrable_apply_unitVector`: Applying the gradient field to a coordinate vector gives a locally integrable spatial field. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L216).

**Weak gradients identify columns** · theorem. `partialX_ae_of_weakGradient`: A weak gradient's coordinate column agrees almost everywhere with the corresponding homogeneous-space partial derivative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L223).

**Physical and abstract convection agree** · theorem. `readingConvection_slice`: Almost every time slice of physical convection agrees almost everywhere in space with the abstract slice convection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L236).

**A nonnegative slice bound** · theorem. `Breakdown.Cert.Convection.sliceConst_nonneg`: The convection slice constant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L247).

**Squared norm in extended reals** · theorem. `ofReal_norm_sq_eq`: The extended-real image of the squared ordinary norm equals the squared extended norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L255).

**The L² norm as a nonnegative integral** · theorem. `Breakdown.Cert.Convection.ofReal_norm_sq_Lp`: The squared L² norm equals the nonnegative integral of the representative's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L259).

**Gradient norm over the time circle** · theorem. `ofReal_norm_sq_gradCLM`: The squared gradient-curve norm is the integral of the squared gradient-part norms over the time circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L265).

**An integrated slice bound** · theorem. `Breakdown.Cert.Convection.lintegral_slice_le`: The nonnegative square integral of a slice is bounded by the squared slice constant times its squared energy norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L276).

**A period convection bound** · theorem. `Breakdown.Cert.Convection.periodLIntegral_le`: The physical convection field's periodic square integral is bounded by the squared slice constant times the squared gradient-curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L292).

**A circle representative returns** · theorem. `Breakdown.Cert.Convection.coe_circleRep`: Projecting the chosen real representative back to the time circle gives the original point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L317).

**Equal circle points give equal values** · theorem. `eq_of_coe_eq`: A periodic function takes equal values at real times with the same image in the time circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L320).

**Transport an almost-everywhere fact** · theorem. `ae_circle_of_ae`: The relevant real-time almost-everywhere relation descends to the chosen representatives on the time circle. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L328).

**The usual one-periodicity predicate** · theorem. `periodic_of_isTimePeriodic`: The field's time-periodicity hypothesis supplies ordinary period-one periodicity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L335).

**Convection is periodic** · theorem. `Breakdown.Cert.Convection.periodic_readingConvection`: The physical convection field is periodic in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L338).

**L² conversion respects equality** · theorem. `toLpOrZero_congr`: Almost-everywhere equal functions give the same L²-or-zero conversion. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L345).

**Recover an existing L² class** · theorem. `toLpOrZero_of_ae`: Converting an almost-everywhere representative of an L² element recovers that element. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L354).

**Square-integrable L²-valued curves** · abbreviation. `CurveSpace`: The curve space consists of square-integrable maps from the time circle to spatial L². [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L360).

**A curve represents convection slices** · proposition definition. `IsSliceCurve`: This proposition says that a time-circle L²-valued curve represents the physical convection slices almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L362).

**A bounded convection curve exists** · theorem. `Breakdown.Cert.Convection.exists_sliceCurve`: The convection slices admit an L²-valued time-circle representative with the slice-constant norm bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L366).

**The convection curve is unique** · theorem. `sliceCurve_unique`: Two curves representing the same convection slices are equal. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L390).

**Convection is additive in the field** · theorem. `sliceConvection_add`: Slice convection takes a sum of perturbations to the sum of their slice convections almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L396).

**Convection respects real scaling** · theorem. `sliceConvection_smul`: Slice convection commutes with real scaling of the perturbation almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L403).

**Add convection representatives** · theorem. `isSliceCurve_add`: Adding two representing curves represents the sum of the corresponding perturbations. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L410).

**Scale a convection representative** · theorem. `isSliceCurve_smul`: Scaling a representing curve represents the scaled perturbation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L422).

**The convection curve is a linear map** · theorem. `Breakdown.Cert.Convection.exists_sliceCurveCLM`: The convection representatives assemble into a continuous linear map with a bound through the gradient-curve norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L433).

**Project the convection representative** · theorem. `convectionSpec_of_curve`: Projecting the L²-valued convection curve onto solenoidal fields gives the required convection operator specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L448).

**The specification fixes convection** · theorem. `convection_eq_of_spec`: Any continuous linear map satisfying the convection specification equals the selected convection operator. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L456).

**Convert physical convection to HH** · theorem. `Breakdown.Cert.Convection.physToHH_eq_convection`: The conversion of the physical convection field to the time-circle Hilbert space equals the abstract convection operator applied to the perturbation. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L466).

**Source namespace `Breakdown.Cert`.**

**Construct the convection operator** · theorem. `convectionHolds_of`: The coefficient and field-reading construction proves the convection interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Convection.lean#L490).

### Breakdown.Cert.ConvectionCompact

This file proves that convection becomes compact after applying the free inverse. Local compactness is combined with a uniform spatial tail estimate to control the whole-space operator. §§7.6–7.7: profile terms and the linearized operator

**Source namespace `Breakdown.Cert.Internal.ConvectionCompact`.**

**Cauchy subsequences give compactness** · theorem. `isCompactOperator_of_fundamental_subseq`: A linear operator is compact when images of bounded sequences admit the required Cauchy subsequences. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L15).

**A square estimate gives a norm bound** · theorem. `le_two_mul_of_sq_add`: The stated quadratic inequality bounds the gradient norm by twice the input norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L44).

**Bound the free inverse gradient** · theorem. `norm_gradCLM_freeInv_le`: Under the free-inverse property and positive period, the gradient-curve norm of the selected free inverse is at most twice the forcing norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L49).

**Combine the small error terms** · theorem. `final_arith`: The selected error budgets make the final real bound strictly smaller than the requested tolerance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L53).

**Sum three strict error bounds** · theorem. `sum_fin_three_lt`: Three terms each below the common tolerance have sum below three times that tolerance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L66).

**A Cauchy image subsequence** · theorem. `abstract_fundamental`: The local convergence and tail hypotheses make the selected operator images a Cauchy sequence. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L70).

**Cauchy convection images exist** · theorem. `fundamental_image`: A bounded forcing sequence has a subsequence whose free-inverse convection images are Cauchy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L83).

**Source namespace `Breakdown.Cert`.**

**Convection after inversion is compact** · theorem. `convectionCompactHolds_of`: The local compactness and tail estimates prove compactness of convection composed with the free inverse. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionCompact.lean#L105).

### Breakdown.Cert.ConvectionContinuity

The linearized operator must vary continuously with the certificate parameter. These coefficient and tail estimates convert profile continuity into convection continuity in operator norm. §§7.6–7.7: profile terms and the linearized operator

**Source namespace `Breakdown.Cert.Internal.ConvectionContinuity`.**

**The radial tail weight** · definition. `tailWeight`: The tail weight is the inverse three-halves power of one plus the spatial radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L17).

**The tail weight is positive** · theorem. `tailWeight_pos`: The inverse three-halves radial tail weight is strictly positive. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L19).

**The tail decay weight lies in L³** · theorem. `Breakdown.Cert.ConvectionContinuity.tailWeight_memLp`: The inverse three-halves radial tail weight belongs to spatial L³. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L22).

**The L³ tail-weight constant** · definition. `tailCube`: The tail constant is the real-valued L³ norm of the inverse three-halves radial weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L33).

**A nonnegative tail constant** · theorem. `tailCube_nonneg`: The L³ norm used as the tail constant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L35).

**A bound for coefficient transport** · theorem. `first_part`: A continuous coefficient bounded by a nonnegative constant A times a perturbation derivative lies in L² with norm at most A times the perturbation norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L37).

**A weighted profile-gradient bound** · theorem. `second_part`: Applying the profile derivative to the perturbation velocity gives an L² bound through the weighted tail constant. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L55).

**Convection with two coefficient bounds** · theorem. `slice_bound_general`: Separate velocity and derivative coefficient bounds give an L² bound for the complete convection slice. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L95).

**Subtract convection coefficients** · theorem. `sliceConvection_sub`: The convection slice of the coefficient difference is the difference of the two convection slices. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L129).

**Projection respects subtraction** · theorem. `solField_sub`: The solenoidal L² conversion of a difference equals the difference of the solenoidal conversions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L137).

**Bound solenoidal projection** · theorem. `norm_solField_le`: The norm after solenoidal conversion is bounded by the projection norm times the supplied L² bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L144).

**The selected convection specification** · theorem. `Breakdown.Cert.ConvectionContinuity.convection_spec`: Assuming convection existence, valid certificate data and an admissible parameter, the selected convection operator satisfies the physical slice specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L152).

**The representative lies in one period** · theorem. `circleRep_mem`: The chosen real representative of a time-circle point belongs to the half-open unit interval. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L160).

**Bound a change in convection** · theorem. `Breakdown.Cert.ConvectionContinuity.norm_sub_apply_le`: The difference between two parameterized convection operators applied to one perturbation is bounded by their coefficient differences. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L165).

**Uniform bounds far from the origin** · theorem. `tail_bounds`: Outside a sufficiently large radius, coefficient and derivative tails are both smaller than their chosen weighted tolerances. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L204).

**Continuous profile and derivative data** · theorem. `Breakdown.Cert.ConvectionContinuity.joint_continuous`: The profile and its spatial derivative depend jointly continuously on the certificate parameter, time and position. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L222).

**Nearby parameters give close profiles** · theorem. `Breakdown.Cert.ConvectionContinuity.eventually_close`: Parameters sufficiently near the base parameter give uniform profile closeness and weighted derivative closeness on the parameter box. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L233).

**Continuity from difference bounds** · theorem. `continuousOn_of_norm_sub`: Local bounds on norm differences establish continuity of the operator-valued map on its domain. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L300).

**Choose a strictly smaller error** · theorem. `small_factor_lt`: The chosen small coefficient times the fixed nonnegative bound is strictly below the desired positive tolerance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L310).

**The comparison constant is nonnegative** · theorem. `constant_nonneg`: The product of projection, decay-weight and gradient-operator norms defining the comparison constant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L321).

**A convection operator-norm bound** · theorem. `Breakdown.Cert.ConvectionContinuity.op_bound`: Coefficient closeness controls the operator norm of the difference between the corresponding convection maps. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L326).

**Convection varies locally continuously** · theorem. `Breakdown.Cert.ConvectionContinuity.convection_close`: Every positive tolerance admits a parameter neighborhood where the convection operators are within that tolerance in operator norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L348).

**Source namespace `Breakdown.Cert`.**

**Prove continuity of convection** · theorem. `convectionContinuityHolds_of`: Uniform coefficient comparison and tail control prove the convection-continuity interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionContinuity.lean#L363).

### Breakdown.Cert.ConvectionTail

The whole-space compactness proof needs a tail that can be made uniformly small. This file supplies radial integrability and decay bounds for the convection terms outside large balls. §§7.6–7.7: profile terms and the linearized operator

**Source namespace `Breakdown.Cert.Internal.ConvectionTail`.**

**The L³ norm of the tail weight** · definition. `tailWeight`: The exterior estimate uses the real L³ norm of the inverse three-halves radial weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L20).

**The exterior convection constant** · definition. `tailConst`: The exterior constant combines the profile transport and profile-gradient square estimates. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L22).

**The tail decay weight lies in L³** · theorem. `Breakdown.Cert.ConvectionTail.tailWeight_memLp`: The inverse three-halves radial tail weight belongs to spatial L³. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L24).

**A nonnegative tail-weight norm** · theorem. `tailWeight_nonneg`: The real-valued norm of the radial tail weight is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L35).

**A nonnegative exterior constant** · theorem. `tailConst_nonneg`: The combined exterior convection constant is nonnegative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L37).

**Square the exterior decay factor** · theorem. `sq_half_rpow`: Squaring the inverse-square-root factor gives the inverse first power of one plus the radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L41).

**Separate exterior derivative decay** · theorem. `fderiv_tail_le`: Outside a ball, the profile derivative is bounded by a radius-decay factor times the integrable radial tail weight. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L47).

**An exterior L² derivative bound** · theorem. `eLpNorm_fderiv_tail`: The profile derivative acting on velocity has an exterior L² bound with inverse-square-root radius decay. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L68).

**The exterior derivative square bound** · theorem. `second_tail`: The exterior square integral of the profile-gradient term decays like the inverse of one plus the radius. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L107).

**A spatial L² square integral** · theorem. `ofReal_integral_sq`: The nonnegative spatial square integral of an L² representative equals its squared L² norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L138).

**Gradient energy from its columns** · theorem. `sum_partial_integral`: The sum of the spatial square integrals of the three partial derivatives equals the squared homogeneous energy norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L143).

**Measurable derivative energy** · theorem. `aemeasurable_partial_sq`: The squared norm of a homogeneous-space partial derivative is almost everywhere measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L150).

**Bound a weighted vector sum** · theorem. `sum_smul_sq_le`: The square of a three-term weighted vector sum is bounded by three times the squared coefficient norm times the column energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L155).

**Combine the exterior square bounds** · theorem. `tail_real`: The two component estimates give the displayed exterior quadratic bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L175).

**Expand slice convection** · theorem. `sliceConvection_apply`: Slice convection is the sum of profile-weighted gradient columns and the profile derivative applied to velocity. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L189).

**Pointwise exterior convection control** · theorem. `tail_pointwise`: Outside the chosen ball, the convection square is bounded by weighted gradient-column squares and the profile-gradient contribution. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L193).

**An exterior convection estimate** · theorem. `slice_tail`: The exterior square integral of slice convection is at most the exterior constant divided by one plus the radius times the energy square. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L216).

**Combine the interior square bounds** · theorem. `ball_real`: The nonnegative component bounds give a square bound of six times the squared coefficient bound times the sum of velocity-square and gradient energy. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L256).

**Pointwise interior convection control** · theorem. `ball_pointwise`: The convection square is bounded by the decay constant squared times the local velocity and gradient-column squares. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L267).

**An interior convection estimate** · theorem. `slice_ball`: The convection square integral on a ball is bounded by the local velocity and gradient-column square integrals. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L290).

**Separate interior and exterior energy** · theorem. `slice_split`: The full convection square integral splits into a local velocity-gradient bound and a radius-decaying energy remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L316).

**Projection decreases square energy** · theorem. `enorm_solField_sq_le`: The squared extended norm of the solenoidal field is bounded by the physical field's nonnegative square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L328).

**The L² distance integral** · theorem. `lintegral_sub_sq`: The nonnegative integral of a representative difference squared equals the squared L² distance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L343).

**Integrate an almost-everywhere bound** · theorem. `lp_norm_le_of_ae`: An almost-everywhere bound for the squared representative norm controls the squared L² norm after integration. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L352).

**Convection difference as slice energy** · theorem. `conv_le`: The squared norm of a convection difference is bounded by the periodic square integral of the corresponding slice difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L360).

**Control the time-integrated energy** · theorem. `time_integral_le`: The slice bound integrates to a constant times the squared difference of gradient curves. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L385).

**Measurability of local square energy** · theorem. `aemeasurable_ball`: Integrating the squared field over a spatial ball gives an almost everywhere measurable time function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L410).

**Local velocity energy from X** · theorem. `ball_velocity_le`: On a fixed ball, a finite constant bounds a velocity representative's square integral by the squared homogeneous energy norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L425).

**Local column energy from X** · theorem. `column_ball_le`: A gradient-column representative's square integral on a ball is bounded by the homogeneous energy norm squared. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L462).

**The chosen physical representative** · theorem. `reading_spec`: The selected physical reading satisfies the representation conditions for its abstract curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L474).

**Subtract representatives after mapping** · theorem. `coe_map_sub_ae`: A linear map applied to an L² difference agrees almost everywhere with the difference of its mapped representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L482).

**Represent a mapped difference** · theorem. `sub_ae_of_ae`: Subtracting the two physical representatives gives an almost-everywhere representative of the mapped abstract difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L489).

**Physical differences represent X data** · theorem. `reading_diff`: Almost every time slice of the velocity and gradient differences represents the corresponding differences of homogeneous-space data. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L497).

**Take square roots of the energy bound** · theorem. `real_final`: The real quadratic estimate gives a sum of square-root local terms and a tail term. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L510).

**A bound through nonnegative integrals** · theorem. `final_bound`: The nonnegative integral bound converts to an ordinary norm bound involving square roots of local energies. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L534).

**Separate the energy integrals** · theorem. `integral_split`: The nonnegative integral of the sum separates into the weighted local integrals and the tail integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L554).

**Local and tail convection control** · theorem. `core_bound`: A convection difference is bounded by local velocity-gradient norms plus a radius-decaying multiple of the gradient-curve difference. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L562).

**Choose a radius for a small tail** · theorem. `sqrt_tail_le`: The explicit radius choice makes the square-root tail factor at most the requested tolerance. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L615).

**Source namespace `Breakdown.Cert.Internal.ConvectionCompact`.**

**Make the convection tail small** · theorem. `local_tail_bound`: For every positive tolerance, a radius and local constant bound convection differences by local physical norms plus a small gradient remainder. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ConvectionTail.lean#L630).

### Breakdown.Cert.Data

Certificate profiles, defects, actuators and pinning rows are converted into Hilbert-space data. The public data property records their physical pairings and quantitative norm bounds. §7: certificate data and the similarity-profile construction

**Source namespace `Breakdown.Cert.Internal.Data`.**

**Represent a finite L² sum** · theorem. `coeFn_finset_sum`: The representative of a finite sum of L² classes agrees almost everywhere with the sum of their representatives. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L16).

**The L² norm as a nonnegative integral** · theorem. `Breakdown.Cert.Data.ofReal_norm_sq_Lp`: The squared L² norm equals the nonnegative integral of the representative's squared norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L28).

**A circle representative returns** · theorem. `Breakdown.Cert.Data.coe_circleRep`: Projecting the chosen real representative back to the time circle gives the original point. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L37).

**Read time as its fractional part** · theorem. `Breakdown.Cert.Data.circleRep_coe`: The chosen representative of a real time modulo one is its fractional part. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L40).

**Representatives in the base interval** · theorem. `circleRep_coe_of_mem`: A real time in the half-open unit interval is its own chosen time-circle representative. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L45).

**A representative differs by an integer** · theorem. `circleRep_coe_sub`: The chosen representative is obtained from the real time by subtracting the corresponding integer. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L49).

**Adding one preserves representatives** · theorem. `circleRep_coe_add_one`: Adding one to real time leaves its chosen time-circle representative unchanged. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L53).

**Measurability after folding time** · theorem. `aestronglyMeasurable_fold`: Folding real time to the chosen unit-period representative preserves almost-everywhere strong measurability. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L56).

**Differentiate a parameterized field** · theorem. `contDiff_fderiv_param`: For a jointly C^m field with n + 1 ≤ m, the spatial derivative is jointly C^n. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L70).

**Continuity of the smooth residual** · theorem. `continuous_defect_smooth`: The smooth similarity-equation residual and the pressure gradient are jointly continuous. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L77).

**Measurability of the residual** · theorem. `aestronglyMeasurable_defect`: The complete physical defect field is jointly almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L110).

**The residual is time periodic** · theorem. `defect_periodic`: The complete physical defect field is periodic in time. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L121).

**The projection norm is at most one** · theorem. `norm_solProj_op`: The solenoidal orthogonal projection has operator norm at most one. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L136).

**Recover a time-circle L² curve** · theorem. `circleLpOrZero_eq`: The time-circle L²-or-zero conversion recovers the existing curve represented by the input function. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L139).

**Physical conversion through projection** · theorem. `physToHH_eq`: Converting the physical field to the time-circle Hilbert space is its L²-valued curve followed by solenoidal projection. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L145).

**The period energy of a representative** · theorem. `periodLIntegral_eq_of_curve`: The physical field's nonnegative periodic square integral equals the squared norm of its representing time-circle curve. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L166).

**Bound physical-to-Hilbert conversion** · theorem. `norm_physToHH_sq_le`: The squared norm of the converted physical field is bounded by its periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L180).

**The actuator is a finite linear sum** · theorem. `actuatorH_apply`: The abstract actuator combines the converted actuator fields with the supplied real coefficients. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L197).

**Pin values as gradient pairings** · theorem. `pinSlice_eq_inner`: The physical pin value equals the sum of inner products with the three gradient columns. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L201).

**An inner product after a curve map** · theorem. `inner_compLpL_eq`: The curve-space inner product with a mapped gradient equals the time integral of its slice inner products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L217).

**Integrable gradient slice pairings** · theorem. `integrable_inner_slice`: The time-circle slice pairing used for the pin map is integrable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L224).

**The continuous linear pin map** · definition. `pinCLM`: The pin map collects the gradient-column inner products into the finite coordinate vector. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L231).

**Evaluate the pin map** · theorem. `pinCLM_apply`: A coordinate of the pin map is the sum of the corresponding three gradient-column inner products. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L235).

**The constructed pin map is valid** · theorem. `pinSpec_pinCLM`: If the L² curves represent the physical pinning columns almost everywhere, their continuous linear pin map satisfies the physical pin specification. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L240).

**The residual is an admissible field** · theorem. `Breakdown.Cert.Data.defect_field`: The certificate's defect field satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L252).

**Finite actuator energy** · theorem. `Breakdown.Cert.Data.actuator_fin`: Each actuator field has finite nonnegative periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L261).

**Admissible actuator fields** · theorem. `Breakdown.Cert.Data.actuator_field`: Each actuator field satisfies the periodic-field conditions. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L266).

**Measurability of folded pins** · theorem. `Breakdown.Cert.Data.pin_fold_meas`: The pin field evaluated at the chosen time representative is jointly almost everywhere strongly measurable. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L270).

**Folding preserves pin energy** · theorem. `Breakdown.Cert.Data.pin_fold_period`: Folding the time variable preserves the pin field's periodic matrix square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L274).

**Finite folded pin-column energy** · theorem. `Breakdown.Cert.Data.pin_fold_fin`: Each folded pin column has finite periodic square integral. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L282).

**L² curves representing pin columns** · theorem. `Breakdown.Cert.Data.exists_pin_curve`: Each pin column has a time-circle L²-valued representative agreeing with the folded physical column almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L291).

**A pin map exists** · theorem. `Breakdown.Cert.Data.exists_pinSpec`: For admissible certificate data, a continuous linear map satisfying the physical pin specification exists. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L302).

**The abstract pin is the physical pin** · theorem. `Breakdown.Cert.Data.pinMap_eq`: Evaluating the abstract pin map on a curve equals the pin value of its physical gradient reading. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L307).

**The residual obeys its bound** · theorem. `Breakdown.Cert.Data.defect_norm`: The norm of the abstract defect is at most the certificate's defect bound. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L330).

**Represent the actuator combination** · theorem. `actuator_sum_curve`: The finite linear combination of actuator curves represents the corresponding physical actuator sum almost everywhere. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L338).

**A linear map preserves finite sums** · theorem. `clm_sum`: A linear map commutes with the finite scalar-weighted sum. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L357).

**The induced L² map preserves sums** · theorem. `compLpL_sum`: The induced time-circle L² map commutes with finite scalar-weighted sums. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L362).

**The physical actuator pairing** · theorem. `Breakdown.Cert.Data.actuator_pairing`: Pairing the abstract actuator against a test equals the integral pairing of the physical actuator sum against that test. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L368).

**Bound the actuator map** · theorem. `Breakdown.Cert.Data.actuator_norm_le`: The actuator norm is at most the certificate's actuator bound times the Euclidean coefficient norm. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L390).

**Source namespace `Breakdown.Cert`.**

**Construct the analytic data interfaces** · theorem. `dataHolds_of`: The physical defect, actuator and pin constructions prove the analytic data interface. [Source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Data.lean#L419).
<!-- /passage:front -->

