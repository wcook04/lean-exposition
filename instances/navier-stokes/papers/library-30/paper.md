
<!-- passage:front -->
# Library guide 30: definitions the readable files restate

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) **30**

*A plain title and a sentence for each library declaration that the readable statement files also state, at `ad53419de079eb8f95f60313473374624a348546`. Prepared with AI assistance. The authors have not reviewed it.*

The declarations below are stated twice by the authors: in the library and in the readable statement files that Comparator compares. Each sentence is ours, from our annotation of the same-named declaration in [the statement files](../navier-stokes-statement-files/paper.md) or [the cell reference](../navier-stokes-cell-reference/paper.md), and the link opens the library's own declaration.

### Breakdown.Cert.CoerciveStatement (also in the readable files)

**A priori perturbation estimate.** Proposition. Energy estimate with unit force weight and a ball L² remainder. ([`CoerciveClause`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L10))

**Rotation about the vertical axis.** Definition. This is the rotation Rφ about the third coordinate axis used in the mode average (B.12). Lean writes it in the Cartesian basis, so no cylindrical-coordinate choice is needed on the axis. ([`axialRot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L191))

**Alternating symbol for curl.** Definition. This gives the three-dimensional alternating symbol used to form the curls in (B.14) and (B.18). It uses zero-based coordinate indices and is zero when two indices coincide. ([`alternatingSymbol`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L195))

**Time and angle Fourier coefficient.** Definition. This extracts a joint time-angle Fourier coefficient with normalization 1/(2π) and the conjugate exponential used in (B.12). ([`modeAverage`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L198))

**Gradient mode in the rotating frame.** Definition. This extends (B.12) to the gradient tensor by rotating its input and output indices. ([`modeGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L205))

**Second derivative mode.** Definition. This applies the rotating Fourier average to the second spatial derivative tensor appearing in (B.16). Its three indices are the output component and the two differentiation directions. ([`modeSecondDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L210))

**Squared component norm.** Definition. This sums the squared moduli of a finite complex array. It gives the Euclidean and Frobenius squared norms of the velocity, gradient and second derivative modes in (B.16). ([`cnormSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L216))

**Curl of a gradient mode.** Definition. This contracts the Fourier gradient array with the alternating symbol to form the curl mode in (B.14) and (B.16). ([`curlOfGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L218))

**Gradient of a curl mode.** Definition. This contracts the second derivative mode to obtain the derivative of the curl used in (B.16). Its output pair records the curl component and its differentiation direction. ([`curlGradOfSecondDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L221))

**Invariance under axial rotations.** Proposition. This states that a scalar coefficient is unchanged by every rotation about the y₃ axis. It expresses the rotational invariance required of the weights and auxiliary functions in Appendix B.2. ([`IsAxisymmetric`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L226))

**Frequency in a rotating frame.** Definition. This is the frequency 2πn/P + kν(y), corresponding to Ωp in (B.15) after the paper’s harmonic reindexing. ([`shiftedFrequency`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L228))

**Mean time-angle mode.** Definition. This reconstructs the real vector field in the zero time-angle mode. The earlier multiplier estimates separate this mean from the nonzero waves when bounding the coefficients related to (B.16). ([`meanField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L231))

**Transport in a rotating frame.** Definition. This is the mean field plus the similarity drift y/2, measured relative to a rotating frame. ([`relativeVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L234))

**Curl from a spatial derivative.** Definition. This turns a real derivative map into the curl vector used in (B.18). The derivative direction is the argument of G and the vector component is selected afterwards. ([`curlVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L237))

**Derivative of vorticity.** Definition. This contracts a second derivative tensor to obtain one component of ∇curl W in (B.18). The first explicit index selects the curl component and the second selects the differentiation direction. ([`vortGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L240))

**Bounds for the mean and the waves.** Structure. Field Breakdown.FlowBounds.meanStretch: Upper quadratic-form bound for the symmetric derivative of the mean field. ([`FlowBounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L253))

**Weights assigned to mode classes.** Structure. Field Breakdown.ModeWeights.waves: Finite set of nonzero harmonics used for the oscillatory reference profile. ([`ModeWeights`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L266))

**Magnitude of the curl weight.** Definition. This is the absolute value of the signed curl weight for the class of a mode. It is the nonnegative magnitude entering the earlier coefficient estimates related to (B.16). ([`eps`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L288))

**Magnitude of the velocity weight.** Definition. This is the absolute value of the signed velocity weight for the class of a mode. It enters the frequency seminorm and the earlier coefficient estimates related to (B.16). ([`mu`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L290))

**Class frequency in its rotating frame.** Definition. This applies the shifted frequency to the rotation rate assigned to a mode’s class. It corresponds to the frequency in (B.15), with direct frequency coordinates and the earlier spatially varying rate. ([`dop`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L292))

**Gradient size of the curl weight.** Definition. This measures the spatial derivative of the signed curl weight. It supplies the gradient-of-weight losses that enter the multiplier norm and the coefficients described after (B.16). ([`epsGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L294))

**Gradient size of the velocity weight.** Definition. This measures the spatial derivative of the signed velocity weight. It enters the mixed derivative loss in the earlier version of the quadratic form associated with (B.16). ([`muGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L296))

**Neighbouring curl-weight bound.** Definition. This takes the largest curl-weight magnitude among modes joined to the given mode by a listed reference-profile wave. It bounds the mode couplings discussed after (B.16). ([`epsNb`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L298))

**Neighbouring velocity-weight bound.** Definition. This takes the largest velocity-weight magnitude among modes joined to the given mode by a listed reference-profile wave. ([`muNb`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L301))

**Indicator of a condition.** Definition. This encodes a logical condition as the real number zero or one. The coefficient formulas use it to charge an error budget only when the corresponding weight or coupling is active. ([`ind`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L305))

**Curl-gradient energy already assigned.** Definition. This adds the shares spent on the active curl weight and on its neighbouring modes. Subtracting it from one reduces the curl-gradient coefficient corresponding to I′₂ in (B.16). ([`shareHat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L307))

**Operator norm of a scalar Hessian.** Definition. This is the operator norm of the second Fréchet derivative of a scalar conversion weight. It appears in the conversion losses for D and Z described explicitly below (B.16). ([`secondDerivNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L310))

**Curl coefficient before conversion.** Definition. This is the earlier curl-energy coefficient before subtracting Z: it starts at 1/4, gains from the rotating-frame frequency, and pays for transport and wave couplings. ([`coefA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L312))

**Gradient coefficient after conversion.** Definition. This is the earlier coefficient of the squared gradient mode after the Z conversion and subtraction of c times the energy weight. ([`coefAA`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L319))

**Velocity-weight coupling penalty.** Definition. This records Young-inequality losses caused by the mean derivative and the nonzero waves in the earlier velocity multiplier. ([`penalty`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L323))

**Velocity coefficient after losses.** Definition. This is the earlier coefficient of the squared velocity mode in the quadratic lower bound. Its positive rotating-frame contribution is reduced by rotation, wave, Z-Hessian and Young-inequality losses. ([`coefB`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L328))

**Mixed gradient-velocity loss.** Definition. This is the coefficient of the mixed gradient-velocity term in the earlier class-weight density. ([`coefC`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L333))

**Earlier quadratic form for one mode.** Definition. Curl, gradient and velocity coefficients, with an additional mixed loss. ([`modeDensity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L336))

**Earlier density evaluated on a mode.** Definition. This substitutes the actual Fourier-mode amplitudes of v, G and H into the earlier quadratic form. It is the integrand corresponding to one Iι before the separate stretching term is added. ([`modeTerm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L341))

**Earlier frequency seminorm squared.** Definition. This integrates the squared velocity modes against the magnitude of the signed velocity weight and the rotating-frame frequency. ([`frequencySeminormSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L348))

**Admissible class-based weights.** Structure. Field Breakdown.ModeWeights.IsAdmissible.share1_pos: The first error share is positive wherever the curl weight or its derivative is active. ([`IsAdmissible`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L358))

**Spatial derivative of the profile.** Definition. This provides the spatial derivative of W used in the Fourier gradient modes and the stretching form. ([`gradField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L427))

**Spatial second derivative of the profile.** Definition. This supplies the iterated spatial derivative of W used in ∇curl W. It belongs to the strong C² route; the extended weak route keeps a separate weak Hessian for the piecewise-polynomial profile. ([`secondDerivField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L430))

**Quadratic form of the symmetric part.** Definition. This evaluates u·Gu, which equals the quadratic form of the symmetric part of G over the reals. The mean and wave bounds use it to control the stretching term J. ([`symPartForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L433))

**Validity of the mean and wave bounds.** Structure. Field Breakdown.FlowBounds.IsValid.waveVortGrad_ge: Bound the difference between total and mean vorticity derivatives at every rotated point. ([`IsValid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L435))

**Periodic divergence-free test fields.** Proposition. These are the smooth divergence-free test fields of period one with a common compact spatial support used in (B.14). The time variable remains periodic, so compactness is required only in space. ([`IsPeriodicTestField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L456))

**Periodic scalar test potentials.** Proposition. These are smooth scalar potentials of period one with a common compact spatial support. Testing the multiplier against their gradients expresses the Hdiv condition that accompanies (B.14). ([`IsPeriodicTestPotential`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L460))

**Complex vector pairing.** Definition. This is the Hermitian component pairing in the mode terms of (B.14), linear in the first argument and conjugate-linear in the second. ([`cdot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L464))

**Multiplier for class-based weights.** Proposition. This identifies an L², period-one, divergence-free field by its pairings with smooth test fields, as in (B.14). The signed weights are attached directly to classes in this earlier version of the construction. ([`IsMultiplierField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L472))

**Positive part of the earlier density.** Definition. This sums the positive parts of the earlier mode terms and adds the positive part of J. Its integral is the earlier route’s version of I⁺ in the convention following (B.18). ([`densityPos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L486))

**Negative part of the earlier density.** Definition. This sums the negative parts of the earlier mode terms and adds the negative part of J. Finiteness of its integral is the essential assumption for combining the two signed bounds in Lemma B.2. ([`densityNeg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L491))

**Norm constant for the multiplier.** Definition. This is the square-root constant cM in Proposition B.1 with the energy share c left abstract. Setting c = 3/50 turns the first factor into the printed 50/3 coefficient. ([`multiplierConstant`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L497))

**Pairing remaining after energy costs.** Definition. This is the left-hand side of the multiplier lower bound (B.20), with the earlier class-weight seminorm and an abstract coefficient c. ([`multiplierGap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L500))

**Cost of the earlier stretching bound.** Definition. This is the modewise cost used to control the time-angle mean of the stretching term in the earlier mean/wave route. ([`stretchCharge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L548))

**One curl-multiplier piece.** Structure. Field Breakdown.EpsPiece.frame: The scalar frame rotation rate νp for the current certificate parameter. ([`EpsPiece`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L586))

**One velocity-multiplier piece.** Structure. Field Breakdown.MuPiece.speed: Bound for the full reference transport velocity in this rotating frame. ([`MuPiece`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L600))

**Bounds for the reference harmonics.** Structure. Field Breakdown.HarmonicBounds.harmonics: Finite set containing zero, conjugate partners and every reference-profile harmonic. ([`HarmonicBounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L609))

**Finite families of multiplier pieces.** Structure. Field Breakdown.PieceWeights.classOf: Assign each direct frequency pair to the class of its D and Z weights. ([`PieceWeights`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L618))

**Membership up to mode negation.** Proposition. This tests whether a mode belongs to Np or to its negative. The coefficients in (B.16) use it to decide which modes receive a piece’s frequency gain and local losses. ([`inPiece`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L632))

**Couplings entering a mode piece.** Definition. This sums the reference-mode majorants whose frequency shift carries the current mode into Np. It makes explicit one of the neighbour-coupling sums described after (B.16). ([`fwdSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L635))

**Couplings leaving a mode piece.** Definition. For a chosen mode, this sums reference-mode majorants when subtracting the reference harmonic leaves Np. The piece coefficients use it to allocate losses at modes inside the piece. ([`backSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L639))

**Total reference-gradient majorant.** Definition. This adds the majorants for all listed gradient modes of the reference profile. The velocity-piece coefficient uses this total when dividing derivative couplings into inward and outward losses. ([`harmonicSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L650))

**Derivative size of a piece weight.** Definition. This is the derivative norm of a scalar piece weight. It enters the gradient budget in (B.19) and the transport losses described below (B.16). ([`wtGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L657))

**Positive mass of the mode density.** Definition. This is the pointwise sum whose integral is I⁺ after (B.18). It adds the positive part of each Iι and the positive part of J, retaining the value infinity when needed. ([`densityPos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L735))

**Negative mass of the mode density.** Definition. This is the pointwise sum whose integral is I⁻ after (B.18). Finiteness of its integral is the analytic condition that makes the signed lower bound and the cancellation in Lemma B.2 valid. ([`densityNeg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L740))

**Admissible piecewise multiplier weights.** Structure. Field Breakdown.PieceWeights.IsAdmissible.harmonics_span: The listed real Fourier modes reconstruct the reference profile at every point and time. ([`IsAdmissible`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/CoerciveStatement.lean#L752))

### Breakdown.Cert.ExtendedCoerciveDefs (also in the readable files)

**Squared Hessian size.** Definition. This is the sum of squares of all spatial Hessian entries, used to measure convergence of the smooth approximations. ([`secondDerivSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L12))

**Base part of the mode density.** Definition. This is the part of Iι in (B.16) before the λ and μ corrections are added. It allows an arbitrary coercivity constant c; the paper displays c=3/50. ([`baseDensity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L15))

**Velocity-mode amplitude.** Definition. This is the Euclidean magnitude of the velocity mode v̂ι from (B.12). It supplies the order-zero argument in the mode quadratic form (B.16). ([`velAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L21))

**Gradient-mode amplitude.** Definition. This is the Euclidean magnitude of the matrix mode representing ∇v̂ι. It is the order-one derivative amplitude used by (B.16) and the harmonic interaction bounds. ([`gradAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L24))

**Vorticity-mode amplitude.** Definition. This contracts the gradient mode to its curl and takes its magnitude. It is the primed order-one amplitude in Iι and the main amplitude in the λ multiplier gains. ([`vortAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L27))

**Hessian-mode amplitude.** Definition. This is the Euclidean magnitude of all entries of the second-derivative mode. It supplies the unprimed order-two term in Iι. ([`secondDerivAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L30))

**Vorticity-gradient amplitude.** Definition. This takes the curl contraction of a second-derivative mode and measures all entries of the resulting gradient. It is the primed order-two amplitude in Iι. ([`vortGradAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L33))

**Insert the five mode amplitudes.** Definition. This evaluates a scalar quadratic-form expression on the five derivative amplitudes used in (B.16). ([`modeVals`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L36))

**Signed split of the multiplier bound.** Proposition. The signed sum of gains, remainders, block error and stretching is bounded above by the multiplier gap. ([`IsSplitLowerBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L41))

**Interactions across a mode set.** Definition. This sums harmonic interactions that leave a selected set Nₚ or its negative. These are the cross-mode errors in the λ and μ estimates described after (B.20). ([`edgeSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L51))

**Mode-set square-sum norm.** Definition. This takes the ℓ² size of an amplitude sequence on Nₚ together with −Nₚ. It is used when the cross-mode errors of Proposition B.1 are bounded in blocks. ([`pieceNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L55))

**Transport speed in a rotating frame.** Definition. This is the time-and-angle supremum of the transport velocity Wᵣ+y/2−νₚe_z×y. It gives the transport bound entering the errors in (B.16). ([`frameSpeedSup`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L58))

**Vorticity bound over time and angle.** Definition. This is the real supremum of the vorticity of the reference profile over time and axial angle. It supplies a coefficient in the λ block errors. ([`vortSup`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L62))

**Vorticity-gradient bound.** Definition. This is the real supremum of the operator norm of ∇curl Wᵣ over time and axial angle. The weak-Hessian route replaces this classical derivative by vortGradSupWith. ([`vortGradSup`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L65))

**Positive vorticity-mode gain.** Definition. This is λₚ|Ωₚ(ι)| times the squared vorticity-mode amplitude on Nₚ∪−Nₚ. It is the positive contribution of a λ piece to the primed order-one coefficient in (B.16). ([`pieceEpsPos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L69))

**Vorticity cross-mode errors.** Definition. This records the negative interaction terms from one λ piece when reference-profile harmonics connect its modes to modes outside the piece. ([`pieceEpsRestMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L74))

**Vorticity block errors.** Definition. This bounds the remaining λ-piece terms by products of square-sum norms over its modes. ([`pieceEpsBlock`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L83))

**Positive velocity-mode gain.** Definition. This is (1−cμ)μₚ|Ωₚ(ι)| times the squared velocity-mode amplitude. The fraction cμ of the same frequency seminorm is reserved on the left of (B.20). ([`pieceMuPos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L97))

**Velocity cross-mode errors.** Definition. This bounds the cross-mode transport and stretching terms for a μ piece. ([`pieceMuRestMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L103))

**Velocity block errors.** Definition. This collects the μ-piece transport, weight-gradient and frame-rotation errors using the mode-set norms. ([`pieceMuBlock`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L112))

**Sum of the positive piece gains.** Definition. This adds the λ and μ positive frequency gains for one mode. It is the nonnegative part kept separate while the remaining terms in (B.16) are estimated. ([`piecePos`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L119))

**Base density and mode remainders.** Definition. This combines the base quadratic density with all λ and μ cross-mode remainders for one mode. ([`pieceRest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L123))

**Sum of the block errors.** Definition. This adds the block errors over the finite λ and μ piece families. It completes the intermediate split used to prove the density lower bound in Proposition B.1. ([`pieceBlock`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L129))

**Time derivative and similarity drift.** Definition. This is S⁻¹∂θv+v/2+(y·∇)v/2, the time-and-drift part of T_S. The Laplacian is handled separately, so this field corresponds to T_Sv+∆v. ([`transportPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L134))

**Smooth fields for approximation.** Structure. Field Breakdown.Coercive.IsSmoothPerturbation.transport_finite: The combined time-and-drift term and all its spatial derivatives have finite squared period integral. ([`IsSmoothPerturbation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L137))

**Convergence of smooth approximations.** Proposition. Every member of the sequence lies in the smooth approximation class. ([`IsSmoothApproximation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L152))

**Every perturbation can be approximated.** Proposition. This is the proposition that every weak perturbation admits the smooth approximation just specified. It packages the density step invoked in the proof of Proposition B.1. ([`SmoothApproximationHolds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L165))

**Reference field with a weak Hessian.** Structure. Field Breakdown.CoerciveWeak.IsWeakSecondDerivState.secondDeriv_measurable: The supplied Hessian is strongly measurable up to a null set in space-time. ([`IsWeakSecondDerivState`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L175))

**Vorticity gradient from a Hessian.** Definition. This contracts a supplied Hessian into a linear map representing ∇curl Wᵣ. It provides the operator-norm input used in the weak version of the reference-profile bounds. ([`vortGradMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L210))

**Weak vorticity-gradient bound.** Definition. This takes the time-and-angle supremum of the operator norm obtained by contracting the supplied Hessian. ([`vortGradSupWith`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L346))

**Weak vorticity cross-mode errors.** Definition. This is the λ-piece cross-mode remainder with the supplied weak Hessian used for the vorticity-gradient mode. ([`pieceEpsRestModeWith`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L349))

**Weak vorticity block errors.** Definition. This is the λ-piece block remainder with vortGradSupWith supplying the weak vorticity-gradient bound. ([`pieceEpsBlockWith`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L367))

**Weak base density and remainders.** Definition. This combines the base density with weak-Hessian λ mode errors and the unchanged μ mode errors. It is the per-mode remainder in the weak density-passage argument. ([`pieceRestWith`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L383))

**Sum of the weak block errors.** Definition. This sums all λ block errors with the supplied weak Hessian and all μ block errors. It is the block part of the signed split used after approximation. ([`pieceBlockWith`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L391))

**Pass the density bound to a limit.** Proposition. This is the approximation step that carries the smooth multiplier estimate to a weak perturbation. ([`PieceDensityPassageWeakHolds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L409))

**Absorb the remainder products.** Proposition. This packages the Young-inequality step that distributes the cross-mode and block errors into the final coefficients Iι. ([`PieceAbsorbStepWeakHolds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedCoerciveDefs.lean#L429))

### Breakdown.Cert.ExtendedStatement (also in the readable files)

**An extended certificate exists.** Proposition. This existentially packages a parameter dimension, a complete data record and all extended certificate conditions. ([`ExtendedCertificateHypothesis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/ExtendedStatement.lean#L227))

### Breakdown.Cert.Statement (also in the readable files)

**Gradient matrix pairing.** Definition. This is the Frobenius inner product of two derivative matrices written through their coordinate columns. It supplies the weak diffusion pairing and the pinning functional ℓᵢ. ([`matInner`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L14))

**Trace of the weak Hessian.** Definition. Tracing the two spatial input directions of H gives the vector Laplacian represented by the supplied weak Hessian. ([`secondDerivTrace`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L17))

**Integral restricted to a spatial ball.** Definition. The earlier certificate also measures squared forcing on a closed ball during one normalized period. This local-ball quantity has no finite-row counterpart in the paper’s definition of [F]. ([`periodBallLIntegral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L23))

**Local period-averaged L² norm.** Definition. This is the earlier certificate’s L² norm over one period and a spatial ball. Its coefficient enters the older coercivity and residual-size estimates alongside the full H norm. ([`periodBallNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L29))

**Euclidean norm of coefficients.** Definition. This is the Euclidean norm of a finite multiplier or pin vector, used as |β| and |ℓ(v)| in Section 7. The index size is the certificate’s multiplier dimension. ([`vecNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L32))

**Normalized time periodicity.** Proposition. This is period one in θ=s/S, the common convention for the approximate fields, perturbations and forcings in Section 7. ([`IsTimePeriodic`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L34))

**Unrestricted space-time test.** Proposition. These smooth compactly supported vector tests encode the weak transport derivative before pressure is removed. ([`IsSpaceTimeTestVector`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L36))

**Stationary test field for the form.** Structure. Field Breakdown.IsProfileField.divergence_free: The stationary field is divergence-free almost everywhere through the trace of G. ([`IsProfileField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L79))

**Approximate profile residual.** Definition. Assemble the rescaled self-similar residual with approximate force and pressure. ([`defectField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L99))

**Data for the earlier certificate.** Structure. Field Breakdown.CertificateData.coerciveTotal: c_L bounds the zero-pin inverse after combining full and localized forcing coefficients. ([`CertificateData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L106))

**Rectangular parameter set.** Definition. The earlier certificate uses the coordinate interval between centre minus radius and centre plus radius. This replaces the paper’s mixed coordinate-box and ellipsoid geometry with a translated rectangle. ([`box`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L139))

**Conditions of the earlier certificate.** Structure. Field Breakdown.IsCertificate.nontrivial: At every parameter, the approximate gradient energy is strictly larger than the greatest allowed cancellation energy. ([`IsCertificate`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L142))

**An earlier certificate exists.** Proposition. Require existence of data together with a proof of the entire older certificate predicate. ([`CertificateHypothesis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Cert/Statement.lean#L217))

### Breakdown.CertCell.StatementDefs (also in the readable files)

**Real complex quadratic form.** Definition. Takes the real part of the conjugate matrix pairing. It uses the same convention as the local Hermitian forms. ([`quadForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L873))

**Real matrix on complex coordinates.** Definition. Casts every real matrix entry to complex numbers before taking the real quadratic form. This is not an entrywise absolute-value bound. ([`realQuadForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L879))

**Meridian point at angle zero.** Definition. Embeds a meridian point in space at angle zero, where the reduced mode densities are evaluated. ([`planePoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L917))

**Gradient mode on the meridian plane.** Definition. Reads the corresponding gradient mode as a pair-indexed complex array, retaining the order of output and derivative indices. ([`labelGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L922))

**Spatial reflection symmetry.** Definition. Implements rotation by π about the first Cartesian axis, sending (y₁,y₂,y₃) to (y₁,−y₂,−y₃). ([`flipPoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L926))

**Moving cylindrical frame.** Definition. Lists the radial, angular and axial vectors in component order. Matrix fields use the same order for both indices. ([`frameUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L931))

**Angle of a Cartesian point.** Definition. Uses the complex argument of y₁+i y₂. Its branch convention is harmless only together with the periodic harmonic and axis regularity conditions. ([`pointAngle`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L933))

**Radius and signed height.** Definition. Returns (r,z), before the negative-height branch reflects z to the stored upper half-plane. ([`pointPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L935))

**Zero polynomial representation.** Definition. Represents the zero function with degree zero and a zero coefficient. Higher-degree zero arrays are different data with the same evaluated function. ([`zero`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L949))

**Closed meridian quadrant.** Definition. The mesh is described in the nonnegative r,z quadrant, including the axis and the symmetry plane. ([`closedHalfPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L966))

**Meridian complement of the cells.** Definition. Subtracts the cell union from the closed quadrant. Later estimates restrict the corresponding integrals to the open quarter-plane. ([`exterior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L970))

**Reflected vector coefficient.** Definition. Uses the component's reflection sign and the flipped label on negative height, while keeping upper-plane coefficients unchanged. ([`planeValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1007))

**Reflected matrix coefficient.** Definition. The reflection sign is the product of the two frame signs, reversing the entries with exactly one radial index. ([`planeValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1026))

**Polynomial models of the profile.** Structure. Collects the four model fields and an approximation to the inverse period. These are approximants with independent error bounds, not exact derivatives by construction. ([`ModelPolys`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1044))

**Open meridian quarter-plane.** Definition. The analytic integrals use r>0 and z>0. The finite rectangles include their boundaries, whose contribution is handled by measure-zero statements. ([`halfPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1105))

**Mode density on the quarter-plane.** Definition. Evaluates the full mode form using the parameter's period, weights and bounds at time zero and angle zero. It is the reduced Iι density, before multiplication by r. ([`labelDensity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1111))

**Five coefficients of a mode form.** Structure. The five real entries correspond respectively to I₂, I₂′, I₀₁, I₁ and I₀ in (B.16). Their signs are imposed by later inequalities. ([`ModeCoefficients`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1127))

**Pure angular phase.** Definition. Uses only the spatial integer nκ and angle. The time phase has already been separated when this helper is used. ([`azimuthPhase`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1186))

**Rectangle above the symmetry plane.** Definition. Builds the closed rectangle [ρ₁,ρ₂]×[0,h] used for trace-credit estimates. The definition does not require positive width or height. ([`patch`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1188))

**Nonmean stretching bounds.** Structure. Stores angular modes of the strain and supplied second-derivative data, their bounds, and positive splitting parameters. The actual operator inequalities are in IsCrossWaveEntry. ([`CrossWaveEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1206))

**Diagonal on selected pivots.** Definition. Places the supplied slack only on pivot coordinates, with zeros elsewhere. ([`pivotDiagonal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1282))

**Pivot diagonal in complex form.** Definition. Casts the real pivot diagonal to complex coefficients without changing its support. ([`complexDiagonal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1290))

**Embed real global coordinates.** Definition. Casts the global real vector into complex coordinates before applying a complex node's coordinate matrix. ([`ofRealVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1298))

**Negative columns at one node.** Definition. Places a global column in this node's matrix exactly when its recorded node matches; all other entries are zero. ([`nodeColumns`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1343))

**Data for a real node enclosure.** Structure. Stores the approximate input and base matrices, pivot values, positive scaling weights, error radii and positive factor columns. Symmetry and inequalities belong to PassesRealNodeEnclosure. ([`RealNodeData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1348))

**Real or complex node certificate.** Proposition. A node may satisfy either enclosure branch, with branch-specific data and error matrices. A checker must preserve the existential witness and the disjunction. ([`PassesNodeEnclosure`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1440))

**Scale every polynomial coefficient.** Definition. Keeps the stored degree and multiplies every complex coefficient by the same scalar, including the real-versus-imaginary row factor. ([`scale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1467))

**Scalar weight in two half charts.** Structure. Stores separate upper and lower spline functions and a natural decay exponent. Each half is evaluated in nonnegative chart height. ([`ChartScalar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1543))

**Evaluate a decaying scalar weight.** Definition. Multiplies the selected half-chart spline's real part by (1−σ)^decay and uses the upper chart on the symmetry plane. ([`eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1550))

**Reflect a scalar weight.** Definition. Swaps upper and lower splines while keeping the decay exponent. The symmetry conditions later compare this reflected data with its partner. ([`mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1555))

**Polynomial joins of a chosen order.** Structure. Requires a valid tensor mesh and exact identities of derivatives through the selected order at every internal knot. The two directions have separate interval guards. ([`SplineJoins`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1559))

**Joins across cells and the plane.** Structure. Combines joins on both halves, a shared radial knot list and signed derivative matching at η=0. The factor (−1)^o accounts for reflection of the lower chart. ([`IsJoinedScalar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1568))

**Common constant near the origin.** Proposition. Requires a positive cutoff that is a stored upper radial knot and one complex constant for all pieces below it on both halves. These outer requirements remain mandatory even if an inner index range were empty. ([`IsConstantCore`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1576))

**Constant boundary value at radius zero.** Proposition. Requires one common complex value at the first radial face of all upper and lower height pieces. It fixes values at the origin boundary, not every derivative there. ([`IsFlatAtOrigin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1582))

**Nonnegative values on both charts.** Proposition. Requires the real parts of both spline evaluations to be nonnegative at every point of the unit square. Coefficient positivity is a possible sufficient proof route, not the literal predicate. ([`HasNonnegValues`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1586))

**Piecewise constant auxiliary weight.** Structure. Stores real tables on a common tensor mesh and an integer decay power. Negative powers are allowed by the data type, unlike ChartScalar's natural exponent. ([`StepDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1590))

**Reflected step weight.** Definition. Reflection exchanges the upper and lower tables while retaining their common mesh and decay exponent. ([`mirror`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1610))

**Decode one λ-piece.** Definition. The constructor evaluates each stored scalar in the chart and adds the supplied rotation rate and transport-bound function. ([`epsPiece`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1659))

**Decode one μ-piece.** Definition. The constructor evaluates the stored μ-weight and auxiliary steps while preserving its harmonic set and scalar η. ([`muPiece`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1673))

**Decode all multiplier weights.** Definition. The class map and constants are retained, while the scalar records become the function-valued PieceWeights used by the coercive form. ([`pieces`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1682))

**Reflection of scalar weights.** Structure. The supplied permutations of λ- and μ-indices implement reflection, and the class weights agree after both label and spatial reflection. ([`IsFlipClosedValues`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1724))

**Regularity of each forcing field.** Structure. The fields bᵢ carry explicit measurability, weak-gradient and period-one conditions. Mode support is stated away from the axis, while the two discrete symmetries hold almost everywhere. ([`ActuatorShapeFacts`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1744))

**Forcing modes avoid multiplier sets.** Structure. A single j_* rectangle contains each forcing-field label, and every label in that rectangle must avoid every λ- and μ-piece on K. ([`IsActuatorInstance`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1759))

**Identify the cell pin fields.** Structure. The analytic pin field is exactly the polynomial field decoded from the cells, and each cell representation has the required conjugate closure. ([`IsPinInstance`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1773))

**Validity of the decoded instance.** Structure. Rows, weights, forcing fields, pin fields and the symmetry set are linked to one CellLayerData object here. ([`IsInstanceEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1790))

**Reflect a chart polynomial.** Definition. Substitution leaves σ unchanged and replaces η by −η; any overall odd sign is applied by reflectSpline. ([`reflectPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1854))

**Equality on active spline pieces.** Structure. Agreement requires identical meshes and equal polynomials on every active cell. It does not require equality of the total piece functions at unused indices. ([`SplineAgrees`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1862))

**One harmonic's amplitude data.** Structure. The radial and polar entries encode A and B when ι₁≠0; stream, swirl and axisCoef encode S, T and γ when ι₁=0. The unused branch remains present in the record. ([`KeyAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1866))

**Conjugate amplitude data.** Definition. Conjugation acts on all four splines and γ, while the origin and decay exponents remain fixed. ([`conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1877))

**Reflected amplitude data.** Definition. A is even under η-reflection and B, S and T are odd; the stored γ and exponents are retained. ([`reflect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1880))

**One-dimensional jet axis.** Structure. The interpolation depth D controls endpoint derivatives through order D−1; bubbleCount supplies the additional interval coefficients. ([`JetAxis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1891))

**Polynomial of one jet coordinate.** Definition. A coordinate contributes only to its adjacent nodal interval or its own bubble interval, and out-of-range derivative or bubble orders contribute zero. ([`dofPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1914))

**Symmetric height partition.** Proposition. Negating and reversing the breakpoint list must reproduce the same list, which allows reflection to stay on one stored height mesh. ([`IsSymmetricAxis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1944))

**Embed a radial polynomial.** Definition. The univariate polynomial is evaluated at the first variable of the bivariate polynomial ring. ([`embedFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1951))

**Embed a height polynomial.** Definition. The univariate polynomial is evaluated at the second variable of the bivariate polynomial ring. ([`embedSecond`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1953))

**Origin profile g.** Structure. The function g is a polynomial up to σg and a constant afterwards; its normalization supplies the controlled linear term at y=0. ([`OriginProfile`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1972))

**Evaluate the origin profile.** Definition. The polynomial branch includes the joining point σg. Conditions on its derivatives supply agreement with the constant tail. ([`eval`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L1977))

**Polar vanishing factor.** Definition. The factor 1−η² appears in the stream-function divergence identity and vanishes at both ends of the height chart. ([`polarFactor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2012))

**Double polar vanishing factor.** Definition. The factor (1−η²)² supplies the stronger axis vanishing of the nonzero-azimuthal branch in (B.7). ([`axisFactor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2014))

**Real part as a linear map.** Definition. The coordinatewise real part is packaged as a real continuous linear map so that it can be composed with derivative maps. ([`realPartVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2056))

**Reference and forcing shape data.** Structure. The reference profile has its own shape parameters, while every forcing field may use a different length and radial phase with a recorded support edge. ([`GivenShapeEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2151))

**Jet data for one harmonic.** Structure. The four amplitude splines are held in jet coordinates, while γ and the two vanishing/decay exponents are stored directly. ([`JetKeyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2276))

**Decode one harmonic's jets.** Definition. Each jet spline is converted to cell polynomials; γ and the exponent data are copied unchanged. ([`toAmp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2285))

**Jet depth for spline regularity.** Structure. The radial and height axes have their prescribed full domains, and each depth exceeds the required joining order by at least one. ([`IsJetClass`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2297))

**Consistent representative jets.** Structure. A nonzero-azimuthal conjugate-reflection-fixed key has symmetric axes and the required conjugate parities. ([`IsGivenJetData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2303))

**Function-valued harmonic bounds.** Definition. The finite support is retained and each scalar chart datum becomes the corresponding function in HarmonicBounds. ([`bounds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2378))

**Identify the decoded enclosures.** Structure. These are equalities of complete bound records and functions on the parameter set, rather than numerical upper-bound tests at selected points. ([`IsBoundValuesEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2416))

**Budget for unresolved polynomial tails.** Structure. The record separates Hessian and curl-gradient floors from lower-order absorption, potential and leakage charges, which are combined in Holds. ([`TailBudget`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2458))

**Gradient charge after curl gain.** Definition. Any curl absorption not covered by the curl-gradient spectral gain is charged twice to the gradient, using |curl u|²≤2|∇u|². ([`gradCharge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2476))

**Six coefficients of the tail form.** Structure. The five squared-derivative coefficients and one cross coefficient represent the f₂, f′₂, f′₁, f₁, f₀ and f₀₁ quantities used before (B.29). ([`PointCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2484))

**Stretching and extra charges.** Structure. The three bounds s₁,s₂,s₃ and the positive scale h feed the stretching loss; a′₁,a₁,a₀ and c_* describe the additional unresolved-mode charges. ([`EntryCharges`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2509))

**Apply charges at one point.** Definition. The point-dependent charge functions are evaluated first and then passed to the explicit coefficient update. ([`charged`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2528))

**The four harmonic envelopes.** Definition. The index order is velocity, velocity gradient, vorticity and vorticity gradient, matching the four envelopes used in the multiplier errors. ([`ampOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2536))

**Membership as a scalar.** Definition. The Boolean indicator is interpreted exactly as 0 or 1 in the coefficient formulas. ([`bit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2538))

**Uniform five-term lower coefficients.** Definition. The mode-set bounds become a PointCoef record; its initial cross coefficient is zero, before the stretching charges are added. ([`lowCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2602))

**Validity on a full mode region.** Structure. The class and membership assertions hold for every lattice label in the set, and the coupling bounds hold throughout the geometric region. Resolved-mode enumeration alone does not discharge this predicate. ([`IsValidOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2610))

**Distance in the meridian plane.** Definition. The radius √(r²+z²) is the full spatial distance |y| in cylindrical coordinates, not the cylindrical radius r. ([`planeRadius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2646))

**Exterior beyond a radial graph.** Definition. The exterior is the part of the open quarter-plane lying strictly beyond the direction-dependent radius. ([`planeRayRegion`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2648))

**Exterior of a positive square.** Definition. A point belongs when either r or z exceeds the supplied edge, still restricted to r>0 and z>0. ([`planeSquareExterior`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2650))

**Angular Hardy constant.** Definition. The admissible radial-exterior constant is 1/4+(k−1)₊², combining radial Hardy and angular derivative gains. ([`rayInverseSquareConst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2658))

**Spatial second derivative.** Definition. The Hessian is an iterated Fréchet derivative, whose trace supplies the Laplacian in the residual formula. ([`secondDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2711))

**Derivative in normalized time.** Definition. The derivative is in the period-one variable θ; the reciprocal physical period is supplied separately by adjointTransport. ([`timeDerivative`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2720))

**Norm bounds for the potentials.** Structure. The numbers bound Gⱼ, ∇Uⱼ, Fⱼ and the remaining dual norm separately, before they are combined in (B.53). ([`PotentialNumbers`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2740))

**Rotation about the vertical axis.** Definition. The coordinate formula supplies the exact rotations under which each amplitude has one azimuthal wave number. ([`axisRotation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2762))

**Pin potentials and generators.** Structure. The potential fields encode Φₗ and the solenoidal generators encode Φ̃ₗ, whose difference is charged separately in (B.53). ([`PinData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2787))

**Residual of one fitted direction.** Definition. The directional correction combines adjoint advection by the fitted field with the negative time derivative weighted by the reciprocal-period rate. ([`fittedResidual`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2825))

**Reference-form norm data.** Structure. The two stored numbers are s_- and the L³ norm bound on the reference gradient used for c′₃ in (B.48). ([`ModelFormNumbers`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2916))

**Replace the origin profile.** Definition. The constructor allows W⁰ and each tangent Wⁱ to have their own g while retaining the common chart and phase. ([`withOrigin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2978))

**Second derivative of affine fields.** Definition. The Hessian uses the same centre and tangent decomposition and the same parameter-dependent phase as the field itself. ([`affineSecondDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2984))

**Radial step profile χ.** Structure. The piecewise polynomial χ is stored by a breakpoint list and a total function from interval indices to polynomials. ([`StepProfile`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L2989))

**Parameter-dependent profile data.** Structure. The record stores one common chart/phase, the radial step and rates, and separate centre/tangent harmonic data and origin profiles. ([`ProfileShapeEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3011))

**Finite pressure harmonic data.** Structure. The key set uses the same time/angular/radial phases as the vector-field representation, with scalar amplitudes. ([`PressureFieldData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3058))

**Centre and tangent pressure data.** Structure. The centre pressure and each tangent pressure have fixed harmonic coefficients; their common radial phase still changes with α. ([`PressureShapeEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3087))

**Shape data for the adjoints.** Structure. All active adjoints share one chart/phase record, with a separate finite harmonic field for each index. ([`AdjointShapeEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3102))

**Normalized time derivative.** Definition. This derivative is taken before the reciprocal period is inserted in the residual coefficients of (B.57). ([`timeDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3121))

**Centre field used by the expansion.** Definition. The centre coefficient is evaluated with the original phase f and centre origin profile, appropriate to the ball where f_* vanishes. ([`centreCoefficient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3159))

**Linear field used by the expansion.** Definition. The tangent coefficient uses its own origin profile, the original phase and the corresponding pressure and force tangent. ([`linearCoefficient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3163))

**Cylindrical point for knot tests.** Definition. The map keeps signed z and nonnegative cylindrical radius, so reflection of knots must be handled explicitly. ([`planeOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3247))

**Radius of a planar knot point.** Definition. This is √(r²+z²), used to recognise compactified-radius spheres in the meridian plane. ([`planeNorm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3276))

**Conical partition knots.** Definition. Each height breakpoint η contributes the cone equation z=η√(r²+z²). ([`coneKnots`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3281))

**Underlying unscaled jet axis.** Definition. The breakpoints, depth and number of bubbles are retained while scaling and normalisation data are forgotten. ([`base`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3334))

**Rectangle and trace-credit data.** Structure. The rectangle Π carries real test functions and a positive test-form candidate, together with a real trace map and a complex credit matrix on selected trace coordinates. ([`CreditPatch`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3442))

**Region of a credit rectangle.** Definition. The patch uses the radial interval from inner to outer and the height interval from zero to height, adjacent to the reflection plane. ([`region`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3465))

**Layout for selected angular modes.** Proposition. The generic fractional-cell layout predicate is specialised through auxiliary data with no actuator or global-row coordinates; only its order and resolved angular modes are prescribed here. ([`IsHarmonicLayout`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3529))

**Lower-order coefficient form.** Definition. The curl, gradient and velocity terms act on a complex 3×3 gradient and a complex three-vector, before Hessian terms are added. ([`coefPairValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3545))

**Penalty for polynomial model error.** Definition. The penalty combines curl, gradient and velocity squares with the three box-error coefficients. ([`boxPenalty`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3566))

**Penalty for pairing model error.** Definition. The second penalty has the same three quadratic channels but different coefficients, reserved for the stretching/pairing estimates. ([`boxPairPenalty`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3569))

**Lower-order tail absorption.** Definition. The three stored absorption coefficients charge curl, gradient and velocity squares when controlling the omitted polynomial tail. ([`absorbValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3572))

**Vorticity of the reference field.** Definition. The vorticity is curl W formed from the spatial Fréchet derivative at each normalized time. ([`vorticityOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3623))

**Strain of the reference field.** Definition. The strain is the symmetric part (∇W+(∇W)ᵀ)/2 of the real linear derivative map. ([`strainOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3626))

**Vorticity gradient from the Hessian.** Definition. The contraction of the prescribed Hessian supplies ∇curl W, allowing the weak reference Hessian convention to be used. ([`vorticityGradOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3629))

**High polynomial-orthogonal pieces.** Structure. The four high pieces represent velocity, vorticity, strain and vorticity gradient and are later required to have vanishing low polynomial moments. ([`CellModelHigh`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3633))

**Long angular-frequency pieces.** Structure. The four long pieces carry an angular cutoff and their own error bounds; their low angular modes are excluded by IsCellModelSplit. ([`CellModelLong`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3639))

**Full polynomial model decomposition.** Structure. Each of the four fields is split into model, high, long and residual parts. Orthogonality, angular gaps, symmetry, measurability and nonnegative error budgets are separate obligations. ([`IsCellModelSplit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3652))

**Evaluate a vector test polynomial.** Definition. The three CellPoly components are evaluated using the cell's coordinate convention before row integrals are formed. ([`testValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3688))

**Test moment on one face segment.** Definition. The face-moment routine receives the scalar test and both meridian derivatives, with its non-pressure convention selected explicitly. ([`sideTestMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3705))

**Tensor product cell basis value.** Definition. A radial and a vertical real orthonormal polynomial are multiplied and embedded in ℂ for use in complex row integrals. ([`basisValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3708))

**Coordinate in the dilation drift.** Definition. The cylindrical components of y are r,0,z; this helper inserts the corresponding component in the similarity-drift row. ([`frameWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3710))

**Constants for model-error penalties.** Structure. The record stores the source and length weights, strain slack, per-label row weights and an orthogonal-tail weight used in the error accounting. ([`BoxConstants`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3793))

**Uniform reciprocal-period enclosure.** Proposition. reciprocal-period-not-period: Enclose 1/S(α) against periodInverse uniformly over K. An interval for S or a centre-point period error is not this bound unless it is converted with a proved positive-period enclosure. ([`IsPeriodModel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3814))

**Consistency of local calculus data.** Structure. The conditions combine layouts and uniform leaf bounds with model decomposition and trace placement. Pressure segmentation is required before the extra prohibition of radial pressure traces on the axis. ([`CellCalculusConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3876))

**Identify trace-credit coordinates.** Structure. Every credit coordinate matches the patch's physical harmonic and the correct plane-side moment, and the whole rectangle lies in the mesh. ([`CreditEvalConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3951))

**Surrogate forcing-gradient pairings.** Structure. The radial-weighted squared forcing-gradient error, summed over all slack labels and forcing indices, fits the cell budget. ([`IsPairSurrogate`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L3985))

**Support boundary is a spline knot.** Proposition. Requires the chosen support boundary to occur in both amplitudes used by each field key, choosing the nonzero-azimuthal or axisymmetric representation as appropriate. ([`HasEdgeBreak`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4024))

**Pressure gauge classes.** Structure. Stores the pressure gauge classes, deleted coordinates and an exact rational inverse for their incidence matrix. These are extra data behind the paper’s unspecified global coordinate relations. ([`GaugeKeyValues`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4056))

**Gauge endpoint indicator.** Definition. An endpoint contributes one precisely when its optional class equals the requested gauge class; an absent endpoint contributes zero. ([`endWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4069))

**Real pressure gauge direction.** Definition. Only zero-azimuthal pressure keys with the matching harmonic class contribute. Radial faces use a one-dimensional moment, while horizontal faces use a weighted endpoint difference. ([`dirReal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4072))

**Complex pressure gauge direction.** Definition. Embeds the real pressure gauge moment into ℂ without adding an imaginary component. ([`dir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4082))

**Deleted-key integration weight.** Definition. Returns a pressure-key moment and zero for other key kinds. The horizontal value uses the upper radial primitive; it is not the endpoint difference used by a full gauge direction. ([`keyWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4084))

**Weight of a deleted pressure key.** Definition. Evaluates the key weight at the pressure coordinate chosen for deletion; the gauge conditions later require this number to be nonzero. ([`deletedWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4090))

**Gauge matrix at deleted coordinates.** Definition. Rows index deleted pressure coordinates and columns index gauge classes. This fixes the orientation of the incidence comparison. ([`matrix`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4092))

**Weighted incidence matrix.** Definition. Scales each row of the integer incidence matrix by that deleted coordinate’s real integration weight, then views the result as complex. ([`weightedIncidence`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4095))

**Azimuthal mode carried by a key.** Definition. Extracts the mode of velocity, gradient, pressure and corner keys; stream keys carry mode zero and private coordinates have no skeleton mode. ([`keyMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4113))

**Reflection sign at the plane.** Definition. Attaches a parity only to keys on z=0. Velocity and gradient moments have opposite frame signs, pressure is even, and the stream value is odd. ([`planeSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4122))

**Omit the imaginary zero mode.** Proposition. Marks only an imaginary coordinate at harmonic zero with skeleton mode zero as absent by reality. ([`RealLabelOmitted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4130))

**Omit a plane-paired component.** Proposition. For the specified positive diagonal family of labels, reflection and reality remove one real or imaginary component according to the key’s parity. ([`PlanePairOmitted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4133))

**Omit an odd axisymmetric trace.** Proposition. Marks mode-zero plane keys with odd reflection parity as absent. ([`PlaneOddOmitted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4137))

**Coordinate deleted by gauge choice.** Proposition. A key is deleted only when it occurs in the stored list with exactly the same harmonic label. ([`DeletedOmitted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4144))

**Valid pressure gauge data.** Structure. exact-gauge-inverse: Check the rational inverse and gauge-moment identities exactly or prove exact equality from their encoding; a residual near zero is insufficient. ([`Conditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4146))

**Replace the form’s coercivity.** Definition. Changes only the coefficient c in each parameter-dependent collection of pieces. It leaves the certificate’s own coercivity field unchanged. ([`withFormCoercivity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4184))

**Perturbation with finite form energy.** Structure. similarity-transport-field: The field g is T_P v, not the time derivative alone: its weak transport identity includes v/2 and (y·∇)v/2. Decode the right-hand side with this convention. ([`AdmissibleTuple`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4193))

**Carry a complex form to real data.** Definition. Computes the real matrix of the pulled-back complex form using the conjugate transpose of P. Its argument coordinates are real global unknowns. ([`realLeafForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4222))

**Segment for a skeleton key.** Definition. Builds the segment used to interpret a common boundary key. Its unused opposite level is chosen as lev+1, so this helper must not be confused with a cell’s physical width. ([`keySeg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4263))

**Four kinds of tree leaves.** Definition. Leaves distinguish A₀, ordered cell blocks, signed null-pair occurrences and rectangle credits. The nested sum preserves these cases even when some index sets are empty. ([`Leaf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4269))

**Finite enumeration of tree leaves.** Instance. Combines the recorded finite enumerations to enumerate all four leaf kinds. It adds no numerical positivity condition. ([`leafFintype`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4271))

**One ordered cell-matrix block.** Definition. Masks the cell matrix to a chosen row-part and column-part. An off-diagonal block need not be Hermitian by itself; its transposed partner is placed at the same node. ([`pieceForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4277))

**Embed a rectangle’s trace data.** Definition. Selects from each owning cell’s embedding the coordinates used by a rectangle credit. Different entries may come from different cells. ([`creditEmbed`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4282))

**Node receiving each leaf.** Definition. Uses the relevant node field for each leaf kind, including a separate node for each sign of a null pair. ([`leafNode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4293))

**Instantiate the signed tree.** Definition. Combines the tree data with candidate front matrices Vξ. The front matrices are witnesses supplied to the node and pivot-count conditions. ([`tree`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4299))

**Gauge direction in a cell.** Definition. Places pressure gauge moments in the cell’s skeleton coordinates and zero in ports and both multiplier blocks. ([`gaugeDir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4317))

**Tree enclosure and pivot count.** Structure. Requires a unique root and one common family of front matrices that passes every node enclosure and the global pivot count. The existential witness is shared across all nodes. ([`TreeConditionsGiven`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4324))

**Lower bounds for all coefficients.** Structure. Stores bounds on unresolved regions and fixed lower coefficients on resolved or eliminated modes. The regions and mode sets can be infinite, so a finite list of entries still describes continuum obligations. ([`CoefficientEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4334))

**Uniform continuum hypotheses.** Structure. Collects enclosure admissibility, reflection symmetry and a global coefficient-floor witness. The same three enclosure constants must work for every α. ([`ContinuumConditionsGiven`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4370))

**Moment of constant pressure.** Definition. Computes the full face moment of a unit pressure value. Horizontal faces use a difference of weighted primitives, distinguishing this from a deleted-key endpoint weight. ([`unitMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4423))

**Skeleton key in the half-plane.** Proposition. Requires positive radius for radial faces and corners, allows zero radius for horizontal segments and stream values, and imposes no geometry on private coordinates. ([`KeyInHalfPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4432))

**Reasons to omit a key component.** Proposition. A real or imaginary component may be absent through reality, plane parity or an explicit gauge deletion. The plane cases additionally require the key to lie in the permitted half-plane. ([`KeyPartOmitted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4449))

**Gauge action on a global unknown.** Definition. Uses a cell-coordinate gauge value first; multiplier unknowns contribute zero; otherwise a common skeleton key supplies the gauge value. Missing keys contribute zero. ([`varDir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4453))

**Real and imaginary gauge parts.** Definition. Combines a gauge class with its conjugate class to obtain the real or imaginary coordinate direction. This is a pair of class directions, not ordinary numeric extraction from one entry. ([`varPartDir`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4462))

**Gauge directions pass through rows.** Proposition. For every non-deleted cell key, its direct gauge direction equals the row representation acting on global gauge directions. ([`GaugeRowTransport`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4466))

**Gauge directions are invisible.** Structure. Requires pressure gauges to lie in both left and right kernels of cell forms, to vanish on credit coordinates, and to reconstruct unit pressure moments. ([`GaugeKeyConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4472))

**Skeleton labels and geometry agree.** Structure. Checks that standalone skeleton unknowns carry the mode recorded by their label, and that every cell key lies in the permitted half-plane. ([`RealKeyConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4481))

**All coordinates of one cell.** Definition. Includes the resolved cell data, auxiliary ports, β coordinates and ζ coordinates. The type is larger than the polynomial velocity coefficients alone. ([`CellVars`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4516))

**Bounds for stretching on a region.** Structure. The paper’s s₁,s₂,s₃,h are represented as curl, product, gradient and length charges. The length is required to be positive and independent of the harmonic label on the region. ([`IsRegionChargeBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4519))

**Assembly data for every cell.** Structure. Associates each cell with blocks indexed by that cell’s complete coordinate type, including ports and both multiplier blocks. ([`AssemblyEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4575))

**Select one harmonic’s cell data.** Definition. Reads only the resolved-coordinate summand for one harmonic. Ports and the β,ζ blocks are excluded by the sum-type injections. ([`restrictData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4580))

**Evaluate a linear coefficient field.** Definition. Forms a finite complex linear combination of the stored coefficient fields using the supplied cell vector. No conjugation is applied to the input coefficients. ([`linearField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4584))

**Velocity charge from rectangles.** Definition. Adds the rectangle charge exactly where the harmonic is the reflected rectangle label or its negative and the point lies in the rectangle. This is part of the unresolved velocity budget. ([`creditVelDemand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4588))

**Angular derivative matrix.** Definition. angular-inverse-domain: Before using the inverse in turnedVec, check n≠0 and n²≠1 on eliminated modes; the raw matrix inverse is totalized outside that domain. ([`turnMatrix`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4593))

**Total gradient tail cost.** Definition. Adds the potential, pairing and row contributions charged against the resolved gradient tail. ([`totalStrainCost`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4598))

**Total velocity tail cost.** Definition. Adds the potential and row contributions charged against the resolved velocity tail; there is no separate pairing velocity charge. ([`totalVelCost`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4601))

**Measurable bounded cell charges.** Structure. The bounds are uniform in the harmonic label on each cell. The common bound also controls the charge length above and through an inverse lower bound, so simple point sampling is insufficient. ([`EntryChargesRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4604))

**Regularity of pairing and leaf fields.** Structure. Adds bounded measurability of pairing surrogates and every local matrix entry to the field and charge hypotheses. Bounds may depend on the listed indices, according to their quantifier order. ([`AssemblyRegular`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4631))

**Combined eliminated-mode source.** Definition. Adds the potential source and finite-dimensional pairing source before the angular square completion. ([`sourceSum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4645))

**Gradient slot among twelve entries.** Definition. Embeds the nine gradient indices as slots 0 through 8 of the twelve-component gradient/value vector. ([`gradSlot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4648))

**Remove the angular velocity term.** Definition. twelve-slot-order: Keep gradient slots 0–8, velocity slots 9–11 and the condition j mod 3=1 exactly; changing the tensor order changes the eliminated form. ([`turnedVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4650))

**Turn the combined source.** Definition. Applies the cylindrical angular correction at the harmonic’s actual azimuthal frequency to the combined potential and pairing source. ([`turnedSource`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4655))

**Turn a tested row’s band source.** Definition. Applies the same angular correction to one row’s eliminated-mode coefficient field. ([`turnedRowBand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4658))

**Eliminated-harmonic form.** Definition. zero-band-slack: Do not divide numerically when bandSlack=0. Preserve Lean’s totalized value and check EliminationConditions.slack_zero, or impose and prove a strictly positive slack. ([`bandEliminated`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4661))

**Eliminated tested-row form.** Definition. row-full-inverse: Use the full row matrix including the band correction; the positive-definite row weight and domination condition justify the inverse on the accepted path. ([`rowsEliminated`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4668))

**Gram matrix of eliminated row terms.** Definition. Integrates the conjugate product of turned row fields with radial weight and inverse gradient weights. The order of the two row indices fixes the Hermitian convention. ([`bandGram`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4672))

**Bounded measurable scalar on a cell.** Proposition. Requires both almost-everywhere strong measurability and a pointwise finite bound on the entire closed cell rectangle. ([`IsBoundedOnCell`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4677))

**Allocate resolved tail absorption.** Structure. Matches each harmonic’s tail budget to the local Hessian floors and allocates all potential, pairing and row costs. The top matrix is assembled by an exact weighted sum. ([`TailConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4700))

**Highest-degree coefficient charge.** Definition. top-degree-boundaries: Preserve the ≤ degree tests and the radial/vertical split; an off-by-one change loses highest-degree coefficients. ([`topValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4715))

**Evaluate one polynomial row test.** Definition. Evaluates the stored test-field polynomial on the physical cell rectangle. ([`testAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4733))

**Gram matrix of tested row fields.** Definition. Rows from different harmonic labels have zero pairing. Equal-label entries integrate one test times the conjugate of the other with radial weight r. ([`rowGram`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4736))

**Rescale the row Gram by harmonic.** Definition. Divides a same-harmonic Gram block by the scalar attached to its row’s harmonic label. Positivity of that scalar is established by the surrounding row conditions. ([`scaledRowGram`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4740))

**Gram allowance for unresolved rows.** Definition. Uses the leakage weight as the harmonic block scale of the row Gram matrix. ([`leakGram`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4744))

**Base weight for the tested rows.** Definition. Uses the certificate’s test weight to scale each harmonic block of the row Gram matrix. ([`rowBaseWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4747))

**Gram matrix of row remainders.** Definition. Integrates either the nine gradient slots or the three velocity slots of the tail tests using the cell’s line weight, which differs from r on non-axis cells. ([`tailGramPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4750))

**Row enumeration and matrix bounds.** Structure. row-bijection: Validate both injectivity and surjectivity against the declared tested pairs. A missing or duplicate row cannot be repaired by a Gram check alone. ([`RowConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4756))

**Resolved polynomial gradient.** Definition. Sums the low polynomial gradient data over the internal cell modes of one resolved harmonic. ([`lowGrad`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4788))

**Resolved polynomial velocity.** Definition. Sums the low polynomial velocity data over the internal cell modes of one resolved harmonic. ([`lowVel`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4793))

**Twelve-component resolved profile.** Definition. Packs the nine gradient entries followed by the three velocity entries into the vector on which the local 12×12 matrices act. ([`lowProfile`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4797))

**Complex sesquilinear pairing.** Definition. Uses conjugation on the first vector and no real-part extraction. Later integration or quadratic-form definitions choose when to take the real part. ([`sesq12`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4800))

**Reference-field bilinear coupling.** Definition. Expands the three model stretching and transport contributions using the strain, vorticity gradient and alternating symbol. It is bilinear in the two gradient/value pairs before conjugation is supplied elsewhere. ([`modelBilin`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4803))

**Symmetric model coupling.** Definition. Averages the bilinear model expression with the expression in the swapped pair of arguments. This symmetrisation is distinct from taking a Hermitian adjoint. ([`modelTriple`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4810))

**Read the velocity slots.** Definition. Reads slots 9,10,11 from a twelve-component gradient/value vector. ([`velOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4814))

**Read the gradient slots.** Definition. gradient-slot-order: Keep slot 3a+b throughout matrix assembly, curl extraction and row tests; a transpose is not an innocuous storage change. ([`gradOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4816))

**Flatten a gradient matrix.** Definition. Reindexes a curried 3×3 array as a function on pairs. It changes indexing only and applies no transpose or symmetry operation. ([`pairArray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4818))

**Curl, gradient and velocity charge.** Definition. Adds separate squared-norm costs for the curl, full gradient and velocity of one mode. ([`splitCharge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4820))

**Potential coupling data.** Structure. Encodes the model convolution, the matrix used to split kept data, harmonic groups and Young-inequality costs. The paper describes the role of P_Q but does not specify this full record. ([`PotentialData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4823))

**Pairing-tail Gram data.** Structure. Stores the harmonic set, positive weights and Gram forms that control tails of the β and 2ζ pairing profiles. ([`PairingData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4857))

**Potential and pairing entries.** Structure. Keeps the potential data and finite-dimensional pairing data together for each cell, with its own coordinate type. ([`CouplingEntries`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4862))

**Identify a pressure coordinate.** Definition. Recognizes the pressure summand in the nested CellDatum representation. The decision depends on the sum-type constructor, not a numerical coordinate range. ([`isPressureDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4866))

**Complement of the selected part.** Definition. Returns x−Px for the supplied bandProjection matrix P. This decomposition is meaningful without assuming that P is an orthogonal projection. ([`upperPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4870))

**Selected part of a cell vector.** Definition. Returns Px for the supplied bandProjection matrix. Together with upperPart it sums exactly to x. ([`bandPart`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4874))

**Charge for local model error.** Definition. Applies the curl, gradient and velocity split to local reference-model errors, with the two separate positive lengths used in the formal estimates. ([`epsOwnCharge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4878))

**Low or high long-range factor.** Definition. Uses longBalance up to the absolute azimuthal-label cutoff and 1+1/longBalance above it. Equality with the cutoff belongs to the low branch. ([`longFactor`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4883))

**Charge for distant harmonics.** Definition. Multiplies the distant strain and vorticity-gradient split by the low/high long-range factor. ([`longOwnCharge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4886))

**Charge for one coupling group.** Definition. Balances a group’s vorticity-gradient bound between full-gradient and velocity costs, with its chosen matrix constant and positive length. ([`groupCharge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4890))

**Model convolution on resolved data.** Definition. Integrates all resolved harmonic pairs with coupling label ι−ι′ and the radial weight r. The order of that difference is part of the convolution convention. ([`couplingPair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4894))

**Local absorption already allocated.** Definition. Evaluates the curl, gradient and velocity absorption reserved in the leaf data for one resolved harmonic. ([`absorbValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4898))

**Exact kept potential expression.** Definition. Combines upper-upper and twice upper-selected couplings, then subtracts selected local forms, port costs and group, local-error and distant-harmonic charges. PotentialConditions bounds the stored P_Q by this expression. ([`potentialExact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4902))

**Reshape the gradient entries.** Definition. Despite the name, this helper only reshapes the first nine entries into a 3×3 array. It does not replace the gradient by its symmetric part. ([`strainOfVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4920))

**Resolved profile with zero extension.** Definition. Returns the low profile at resolved labels and the zero twelve-vector at all other labels. This is an explicit zero continuation, not an inferred sparse default. ([`lowAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4922))

**Upper profiles at every label.** Definition. Applies the resolved-profile zero extension to the complementary cell vector x−Px. ([`upperProfiles`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4925))

**Charge for high-degree model error.** Definition. Forms the high-error curl, full-gradient and velocity penalty from the three Young weights. ([`highOwnCharge`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4929))

**Integrated high-error charge.** Definition. Sums that penalty over an explicitly supplied finite harmonic set and integrates with cylindrical weight r on the cell. ([`highOwnAmount`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4933))

**Tail of a coupling field.** Definition. tail-degree-truncation: The velocity degree uses natural subtraction d−1. Active layout conditions supply the relevant lower degree; do not reinterpret the subtraction as an unbounded integer operation. ([`couplingTailFull`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4937))

**Maximum radial weight ratio.** Definition. Uses the outer radius divided by the line weight there. It equals one on an axis cell and the outer radius on a non-axis cell once the cell is valid. ([`rHatMax`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L4945))

**Pairing weights β and twice ζ.** Definition. The forcing block is read unchanged and the pin block is multiplied by two, matching the coefficients of the B_Q pairing. ([`pairWeightOf`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5110))

**Weighted forcing and pin gradient.** Definition. Forms the complex linear combination of stored pairing profiles with the β,2ζ weight vector. ([`pairingProfile`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5114))

**Exact kept pairing expression.** Definition. Pairs resolved polynomial gradients with the weighted forcing/pin profile, then subtracts the Gram penalty for all selected gamma harmonics. The integral carries the cylindrical factor r. ([`pairingExact`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5117))

**Polynomial test of a stored row.** Definition. Selects the three polynomial components using the row’s harmonic label and natural test index. ([`rowTestPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5155))

**Polynomial model velocity coefficient.** Definition. Reads the three velocity components at one model harmonic and point. ([`modelVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5158))

**Polynomial model vorticity coefficient.** Definition. Reads the three vorticity components at one model harmonic and point. ([`modelVorticity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5161))

**Coupling test for one model harmonic.** Definition. Encodes the velocity/vorticity cross-product terms as a twelve-component test. Its nested conjugations fix how this complex test pairs with a perturbation. ([`crossTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5164))

**Coupling test at a row difference.** Definition. Uses the difference between the row’s harmonic and the source harmonic to select the model coefficients in the cross test. ([`rowCrossTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5169))

**Forcing field against a row test.** Definition. Integrates one forcing harmonic against the conjugated polynomial test with radial weight r. ([`actuatorRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5174))

**Unresolved sources of tested rows.** Definition. Takes all tested-label minus reference-label differences, then removes resolved and eliminated modes. These finite differences must be included in the leakage set. ([`deactSources`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5178))

**Groups contributing to a tested row.** Definition. Selects coupling groups whose row-partner set can produce the row label through a group harmonic difference. ([`activeGroups`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5182))

**Long-range cost for the row.** Definition. Chooses the low or high row cost according to the validated low-label predicate. ([`longRowCost`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5186))

**Long-range cost for the source.** Definition. For a low source label uses the high cost, and for a high source label uses both low and high costs. This differs from longRowCost. ([`longSourceCost`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5190))

**Reciprocal long-range row charge.** Definition. long-error-exact-zero: The zero branch requires equality of both error bounds to zero. An interval containing zero or a numerical tolerance does not justify it. ([`longRowTerm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5194))

**Cover of unresolved cell modes.** Structure. Stores finitely many regional conditions and, for each cell and every integer harmonic, a finite selection of them. The selector’s infinite domain needs a mathematical decoding rule. ([`OffModeCover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5302))

**Every unresolved mode is covered.** Structure. unresolved-is-infinite: The quantifier is every harmonic not resolved, not merely every label in a stored finite list; include eliminated modes and the infinite remainder. ([`IsOffModeCover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5307))

**Pointwise and unbounded exterior parts.** Structure. Combines ray-type exterior entries with ordinary pointwise regions. Every harmonic chooses parts from this common finite collection and all parts use one charge family. ([`ExteriorCover`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5319))

**Region of an exterior part.** Definition. Selects the region from the ray-condition or point-condition branch of the tagged exterior index. ([`region`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5327))

**Modes of an exterior part.** Definition. Selects the possibly infinite harmonic set from the appropriate tagged exterior entry. ([`modes`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5332))

**Change a key’s azimuthal mode.** Definition. Replaces the mode in velocity, gradient, pressure and corner keys while preserving geometry; stream and private keys remain unchanged. ([`keyWithMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5368))

**Key lies on the reflection plane.** Proposition. Recognizes horizontal face keys at z=0 and corner or stream points on that plane. A private coordinate is never classified as a plane key. ([`keyOnPlane`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5376))

**Reflection multiplier for a key.** Definition. Returns the frame parity for velocity and corner data, the opposite parity for gradient data, one for pressure, and the axial parity for the stream value. ([`keyFlipSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5384))

**Geometry of a face key.** Definition. Extracts side orientation, level, interval, polynomial tests and degree from velocity, gradient or pressure keys. Other key types return none. ([`sideKeyGeom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5392))

**Replace a key’s face partition.** Definition. Changes a face key’s interval, polynomial test family and degree while keeping its field type, mode and orientation. Non-face keys are left as they were. ([`retileKey`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5398))

**Constant-pressure datum.** Definition. Evaluates the face moment contributed by constant pressure, including the mode convention of the layout. Every non-pressure coordinate receives zero. ([`presUnitMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5404))

**Pressure-head direction.** Definition. Extends the constant-pressure moment to a single resolved harmonic of the full cell-coordinate vector, with zeros in the other harmonics, ports and multiplier blocks. ([`headUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5409))

**Normal axisymmetric velocity key.** Proposition. Recognizes a mode-zero velocity moment in the component normal to its radial or horizontal face. These are the keys that can be reconstructed from stream endpoint values. ([`keyVelNormal`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5414))

**Conjugate cell coordinates.** Proposition. Matches each of the eight datum kinds with the opposite azimuthal mode and the same relevant geometry. Matching indices alone is insufficient when two layouts differ. ([`ConjDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5418))

**Endpoints of a stream segment.** Definition. Returns the lower or upper geometric endpoint, with the variable coordinate chosen according to the face orientation. ([`streamEnds`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5444))

**How a skeleton key is evaluated.** Structure. Stores a target harmonic, whether to conjugate, and a real parity factor. IsKeyEvaluation constrains these values to one of four valid symmetry cases. ([`KeyEvaluation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5447))

**Four allowed symmetry evaluations.** Proposition. Allows direct reading, complex conjugation, reflection on z=0, or their combination. The reflected cases require both plane geometry and the prescribed key parity. ([`IsKeyEvaluation`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5452))

**A global skeleton component.** Proposition. Identifies a purely skeletal global unknown: both the cell and multiplier evaluations must be absent, while key, harmonic and real/imaginary choice must agree. ([`IsKeyVar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5457))

**Valid stored or omitted component.** Proposition. option-none-is-a-claim: Do not treat none as a missing coefficient silently filled with zero. It must be justified by the specified symmetry, gauge or axis-stream condition. ([`PartBound`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5461))

**Complex value from two real slots.** Definition. Builds a complex linear functional from optional real and imaginary global slots, changing the imaginary sign under conjugation. If both options name the same slot, both contributions are added. ([`partVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5467))

**Witness for splitting a face moment.** Structure. Stores a subdivision, local test bases and coefficient expansions of a parent face moment, together with optional global coordinates and stream endpoints. SplitRow supplies all geometric and algebraic checks. ([`SplitChoice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5470))

**Witness for a stream-flux row.** Structure. Stores the symmetry reading and the optional real and imaginary stream values at the two ends of a face. FluxRow supplies the moment identity and denominator checks. ([`FluxChoice`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5484))

**Seven reasons for a coordinate row.** Inductive type. A row is justified by a shared key, a subdivision, a flux identity, a derived relation, a normal-derivative relation, a directly evaluated leaf, or an unused-coordinate proof. ([`RowReason`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5489))

**Recognize an unused-coordinate reason.** Proposition. This predicate is true only for the unused constructor. It does not check the matrix-zero facts that make an unused row valid. ([`IsUnused`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5499))

**Sparse rows for global coordinates.** Structure. free-type-inhabited: portRe : ℕ → Free supplies a free coordinate even when k=0 or no active ports are used. An empty Free type cannot decode this record. ([`RowEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5504))

**Sparse complex row vector.** Definition. sparse-row-support: Treat rowVars as the declared finite support. A serializer with repeated indices must combine them consistently before it can represent this Finset-indexed row. ([`rowVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5520))

**Evaluate a row on real globals.** Definition. Sums the supported complex coefficients against real global unknowns. Realness of the input is part of the coordinate model. ([`rowValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5523))

**Embedding of global real unknowns.** Definition. Builds X_Q from row vectors, optional complex ports and the β,ζ selections. The two port slots may share indices, so their contributions must be added exactly. ([`rowEmbed`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5527))

**A row read from a common key.** Proposition. Excludes private keys, checks the symmetry evaluation and both optional components, then requires exact equality with the resulting complex row vector. ([`KeyRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5537))

**Subsegment used by a split row.** Definition. Constructs the segment for one tile of a face-moment subdivision using its local interval and test coefficients. ([`tileSeg`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5545))

**Flux reconstruction on a subsegment.** Definition. split-flux-denominators: The raw formula permits zero denominators through Lean’s totalized division. SplitRow requires the appropriate denominator to be nonzero when that flux branch is used. ([`tileFlux`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5548))

**Choose direct or flux reconstruction.** Definition. Uses the stream-flux formula only for a tile marked flux and degree zero. All other local moments use their optional direct real and imaginary slots. ([`tileVec`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5558))

**Check a subdivided moment row.** Proposition. subdivision-cover-and-identities: Check strict tile widths, adjacent endpoints, both outer endpoints and polynomial identities for every real argument. A pointwise quadrature check does not prove SplitRow. ([`SplitRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5561))

**Check a stream-flux row.** Proposition. Provides separate radial and horizontal moment identities. The horizontal branch also requires the linear velocity moment to have smaller rank and to be used. ([`FluxRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5598))

**Combine local linear relations.** Definition. Forms the coefficient of one datum in a finite linear combination of the layout’s relation rows. ([`relCoef`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5619))

**Solve a relation for one row.** Proposition. derived-row-acyclic: Check the exact unit target coefficient, pressure cancellation and every strict rank decrease. Permitting a self-dependent cycle would change the justification. ([`DerivedRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5625))

**A row evaluated directly from a cell.** Proposition. Binds the real component to a cell datum and allows an optional imaginary component. Omitting the imaginary component is permitted only at harmonic zero. ([`LeafRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5633))

**Coordinate invisible to the forms.** Proposition. Requires the sparse row itself, the entire row and column of the cell matrix, and every credit use to vanish. The coordinate remains free in InRowRange. ([`UnusedRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5643))

**Velocity-moment row with cutoff.** Definition. out-of-range-velocity-row: Preserve the explicit zero fallback; use velReady when an actual lower-rank row is needed instead of assuming every natural index names a stored datum. ([`velRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5650))

**A velocity-moment row is ready.** Proposition. Requires a valid in-range degree, a strictly smaller rank than the target, and a justification other than unused. ([`velReady`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5654))

**Optional corner-velocity row.** Definition. An absent corner returns the zero row. A present corner uses the corresponding cell velocity datum. ([`cornerRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5660))

**All corner components are ready.** Proposition. Requires all three corner-velocity components to have smaller rank and a non-unused justification. ([`cornerReady`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5666))

**Reconstruct a normal derivative row.** Proposition. normal-row-polynomial-identity: The test derivative expansion must hold for every real argument, with radial factors and boundary signs preserved. Every velocity and corner row used must be ready. ([`NormalRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5671))

**Validate the chosen row reason.** Proposition. Dispatches on the seven row-reason constructors and asks for that constructor’s exact justification. This is the complete row-level obligation, rather than a tag-only test. ([`Accounted`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5714))

**Exterior stretching value sets.** Structure. Supplies chart-based upper bounds for the strain, mean vorticity gradient and oscillatory vorticity gradient used outside all cells. ([`FarFieldValueSets`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5786))

**Exterior field bounds and charges.** Structure. Binds the three chart enclosures to the exact exterior model charges and gives a positive harmonic-independent length h. The field bounds hold at every time and angle on the full exterior. ([`FarFieldConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5792))

**Potential checks after regularity.** Proposition. This is an implication: once eight analytic and geometric prerequisites are supplied, the potential conditions must follow. Those prerequisites are obtained elsewhere in the complete cell route. ([`PotentialEntryConditions`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5835))

**Complex vector components.** Inductive type. Uses the x+iy, x−iy and axial components so that each has one azimuthal phase shift. This is the component encoding of the potential fields. ([`PotComponent`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5916))

**Components carrying a polar sine.** Definition. The two horizontal complex components receive a polar-sine factor; the axial component does not. ([`carriesSine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5927))

**One potential amplitude.** Structure. A tensor-product Hermite amplitude is multiplied by explicit near-origin, far-field and axis factors. Endpoint vanishing may supply part of the required radial order. ([`PotScalar`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5931))

**Polar sine from the height ratio.** Definition. Computes √(1−η²) using the height ratio defined on Cartesian points. Its values at the origin and axis follow the existing totalized chart conventions. ([`polarSine`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5937))

**Potentials for one harmonic key.** Structure. Stores amplitudes for G_j, U_j, the radial and polar contributions to F_j, and q_j. The radial/polar flux entries encode vector components of matrix columns. ([`PotKeyData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5954))

**Finite harmonic potential series.** Structure. Stores a finite key set and a total key-to-amplitude function. Only amplitudes at keys in the finite set enter the decoded field. ([`PotentialSeries`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5961))

**Decode G or U from its series.** Definition. Sums the selected complex components, reconstructs Cartesian coordinates and takes the real vector. The selector chooses the G or U amplitude family. ([`vectorPotential`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5965))

**Radial and polar flux contribution.** Definition. Forms a vector in the input index by combining the radial direction with the polar vector, for one output component and harmonic key. ([`fluxVector`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5970))

**One entry of the potential flux.** Definition. Sums the flux modes, reconstructs the output component and takes its real part. The two indices are output component a and input direction i. ([`fluxEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5975))

**Flux as a continuous linear map.** Definition. Turns the output-by-input matrix into a continuous linear map. Relative to the paper’s derivative convention this represents the transposed flux used in div F_jᵀ. ([`fluxMap`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5979))

**Decode the potential pressure.** Definition. Uses the unshifted harmonic azimuth, with no extra polar-sine factor, and takes the real part of the scalar sum. ([`pressureValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5982))

**Ordered jet breakpoints only.** Structure. jet-mesh-versus-jet-axis: Do not replace IsJetMesh by IsJetAxis or assume it proves continuity. The flux conditions use the stronger predicate only in the direction needed for normal-flux continuity. ([`IsJetMesh`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5988))

**Zero radial jets at the origin.** Proposition. Requires all node-jet coefficients below the requested order to vanish at the first radial breakpoint, for every polar degree of freedom. ([`StartVanishOrder`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5993))

**Zero radial jets at infinity.** Proposition. Requires the low-order radial node coefficients to vanish at the final compactified breakpoint, with the final index computed by cellCount. ([`EndVanishOrder`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5996))

**Degree of freedom touches an end.** Proposition. Classifies node and bubble degrees of freedom that can affect the first or last cell. Natural subtraction in N−1 is truncated at zero. ([`dofMeetsEndCells`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L5999))

**Amplitude vanishes in axis cells.** Proposition. Requires zero coefficients for every polar degree of freedom that touches either polar endpoint cell. This supplies an alternative to an explicit positive axis power. ([`AxisCellsVanish`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6003))

**Constant angular row at the origin.** Proposition. Zeros all non-value polar degrees of freedom in the initial radial row and equates the remaining polar node values. This enforces one common scalar origin value. ([`StartRowConstant`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6006))

**Cylindrical pin-potential series.** Structure. Stores a finite harmonic support and three cylindrical jet amplitudes per label. The field decoder supplies an extra radial factor. ([`CylModeData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6040))

**Decode a cylindrical pin potential.** Definition. Combines each harmonic phase with r times its spline amplitude and the rotating cylindrical frame vector. Taking real parts yields the real field Φ_l. ([`cylField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6044))

**Compact cylindrical pin data.** Structure. Separates a positive support radius from a larger mesh radius and requires support boundaries to be actual spline knots. All active harmonic amplitudes obey the coefficient vanishing predicate. ([`IsCylModeData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6057))

**Pin fields and compact generators.** Structure. Stores both the cylindrical pin potentials Φ_l and compact generators Φ̃_l, together with the cell matrix fields used by the certificate. A later equality ties these representations together. ([`PinShapeEntry`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6064))

**Decode a cell pin matrix field.** Definition. Reads the stored piecewise pin matrix using the entry’s own mesh and rotational order. Equality with the certificate’s pinField is required separately. ([`pinField`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6078))

**Reference-to-profile error constants.** Structure. Separates the error from the fixed reference to the centre profile and the additional error over the parameter set. Their gradient bounds use different Lebesgue exponents. ([`ShiftNumbers`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6171))

**Adjoint potential and pin entries.** Structure. Stores one harmonic potential series and chart per multiplier coordinate, together with shared pin representations. Only selected adjoint coordinates need their series validated. ([`PotentialEntries`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StatementDefs.lean#L6198))

### Breakdown.Defs (also in the readable files)

**Coordinate unit vectors.** Definition. These are the three standard basis vectors used to write the divergence, Laplacian and gradient of (1.1). Coordinates are numbered 0, 1 and 2 in Lean. ([`unitVector`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L12))

**Divergence.** Definition. This is the trace of the spatial derivative, representing div u in (1.1) and div W in (1.2). The derivative is stored as a continuous linear map. ([`divergenceAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L14))

**Laplacian.** Definition. The sum of the three diagonal second directional derivatives represents the vector Laplacian in (1.1). ([`sumSecondPartialsAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L17))

**Pressure gradient.** Definition. This reconstructs the vector ∇p from the three coordinate derivatives of the scalar pressure. Only the gradient enters the equation, so adding a function of time to p does not change this term. ([`gradientAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L20))

**Nonlinear transport.** Definition. Applying the spatial derivative of v to v itself gives the paper’s (v·∇)v. This order of application fixes the convection convention used throughout the certificate files. ([`advectionAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L23))

**Compactly supported scalar test.** Proposition. This supplies the scalar C∞ compactly supported test functions used to express weak spatial derivatives. Such tests make integration by parts local in the spatial variable. ([`IsTestFunction`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L63))

**Weak spatial gradient.** Proposition. Test each coordinate derivative against every scalar smooth compactly supported function. ([`IsWeakGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L65))

**Weak self-similar equation.** Definition. Time integration by parts and the three-dimensional drift produce the negative time-test term, negative W·φ, and negative half radial-test term. ([`weakSimilarityIntegrand`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Defs.lean#L74))

### Breakdown.FracCell.CellDataDefs (also in the readable files)

**Polynomials with two degree bounds.** Definition. Describes functions representable by complex coefficients with separate radial and height degree cutoffs. It is a set of functions, not a stored coefficient array. ([`polyFn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellDataDefs.lean#L34))

**Weighted complex cell pairing.** Definition. Integrates F times the complex conjugate of the test polynomial with a supplied real weight. ([`pairOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellDataDefs.lean#L45))

**Weighted squared cell norm.** Definition. Integrates the squared complex modulus against a supplied weight. Nonnegativity requires the weight assumptions used by the estimate. ([`normSqOn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellDataDefs.lean#L48))

**Radial basis weight on the cell.** Definition. Lifts the one-dimensional basis weight to the meridian rectangle without introducing a height dependence. ([`lineWeightFn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellDataDefs.lean#L54))

**Real local matrix form.** Definition. Evaluates the real part of the complex form on the packed gradient-velocity vector, using conjugation on its first factor. ([`sesqValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/CellDataDefs.lean#L226))

### Breakdown.FracCell.StatementDefs (also in the readable files)

**Orientation of three components.** Definition. The alternating sign fixes the curl convention in cylindrical component arrays. Repeated indices contribute zero; the order of the two gradient indices matters. ([`permSign`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L25))

**Abstract cell approximation data.** Structure. Also inherits the 46 directly declared fields of Breakdown.SteadyCert.FracCertData; those glosses are stored at the parent declaration. ([`FracCellData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L48))

**Real quadratic form.** Definition. Evaluates the real matrix form on a real vector. Symmetry and positivity are separate requirements, so this evaluator alone supplies neither. ([`quadValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L127))

**Cylindrical radius.** Definition. Returns r from the first two Cartesian coordinates, leaving the height coordinate out of the norm. ([`cylRadius`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L306))

**Cylindrical height.** Definition. Returns the signed height z; reflection to the stored upper half-plane is performed separately. ([`cylHeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L308))

**Point in cylindrical coordinates.** Definition. Builds the Cartesian point with radius r, angle θ and height z. Here θ is the spatial angle, whereas the paper uses θ for time and φ for angle. ([`cylPoint`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L310))

**Radial frame vector.** Definition. The first vector of the moving cylindrical frame is represented in the fixed Cartesian basis. ([`radialUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L313))

**Angular frame vector.** Definition. The second frame vector differentiates the radial direction with respect to angle and is orthogonal to it. ([`angularUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L315))

**Axial frame vector.** Definition. The third frame vector is the constant unit vector in the height direction. ([`axialUnit`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L317))

**Spatial harmonic frequency.** Definition. Multiplies an integer mode by the azimuthal order. This one-frequency helper is distinct from the active two-integer label map of (B.2). ([`azimuth`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L325))

**Meridian rectangle.** Structure. Stores the four endpoints of a rectangle Q in the nonnegative meridian quadrant. Endpoint ordering is not part of the data record and is imposed by IsCellBox. ([`CellBox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L335))

**Meridian rectangle as a set.** Definition. The stored meridian rectangle includes all four sides. Later integration permits shared boundaries of measure zero. ([`rect`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L347))

**Cell reflected and rotated.** Definition. A cell describes all angles and both signs of height because membership uses the absolute value of z. ([`solid`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L349))

**Valid meridian rectangle.** Structure. Requires nonnegative lower endpoints and strictly positive width and height. These inequalities justify the affine reference coordinates and exclude degenerate rectangles. ([`IsCellBox`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L361))

**Derivative in the radial variable.** Definition. Takes a one-variable derivative while holding the height fixed. It is an evaluator, so differentiability must be established separately. ([`radialDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L378))

**Derivative in the height variable.** Definition. Takes a one-variable derivative while holding the radius fixed. This complex-valued derivative is used before the finite matrix forms are assembled. ([`heightDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L380))

**Squared gradient-array norm.** Definition. Adds squared complex moduli of all nine gradient entries, with no symmetry reduction. ([`sumSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L464))

**Squared vector norm.** Definition. Adds squared complex moduli of the three velocity components. ([`vecSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L466))

**Squared curl-array norm.** Definition. Forms curlComp first, then sums the three squared moduli; it is not a sum over all nine entries. ([`curlSq`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L468))

**Local form coefficients and losses.** Structure. Collects polynomial cutoffs, resolved modes, local matrix fields and tail-absorption weights for the reusable one-frequency estimate. The active certificate supplies corresponding data separately for each space-time label. ([`CellScalars`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L480))

**Ratio of radial measures.** Definition. Divides cylindrical measure r by the basis weight. On an axis cell this agrees with one away from the axis; at r=0 Lean's total division gives zero. ([`rHat`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L511))

**Real part of a complex form.** Definition. Uses the conjugate of the first vector in the complex matrix pairing and returns its real part. Hermitian symmetry is a separate condition. ([`quadFormValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L771))

**Pressure mode on a meridian plane.** Definition. This helper takes a normalised angular Fourier coefficient at fixed r and z. It has a single angular integer and no time transform; active space-time modes are supplied later. ([`presMode`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L836))

**Gradient coefficient slot.** Definition. Selects one component and two polynomial degrees of a resolved harmonic's gradient; the cutoff is Q+1 in each direction. ([`lowStrain`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L880))

**Velocity coefficient slot.** Definition. Selects one velocity component with both polynomial degrees below Q. Its degree range is one shorter than the gradient block. ([`lowVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L883))

**Side velocity moment slot.** Definition. Selects a side, component and test degree below q+2 for a resolved harmonic. ([`sideVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L886))

**Side gradient moment slot.** Definition. Selects the side derivative moment with degrees below q+1, a different range from side velocity moments. ([`sideGradient`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L890))

**Corner velocity slot.** Definition. Selects a labelled velocity component at a corner. Axis corners can instead be absent from the layout through an optional lookup. ([`cornerVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L897))

**Corner stream-function slot.** Definition. unlabelled-stream-block: Corner-stream indices have no harmonic parameter. Multiplying this block by the number of modes silently changes every later packed coordinate position. ([`cornerStream`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L900))

**Auxiliary side velocity slot.** Definition. Selects one of four whole-cell sides and a polynomial test degree through Q. These coordinates are later related to the segmented side moments. ([`extraVelocity`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L903))

**Equality of cell coordinate tags.** Instance. Provides classical equality for the finite tagged coordinate type. This instance is a logical convenience and is not a serialised comparison routine. ([`instDecEqDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L915))

**Whole-side polynomial test.** Definition. Radial faces use height polynomials; height faces use radial polynomials with an extra factor r on axis cells. ([`sideTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L944))

**Pairing with a segment test.** Definition. Integrates a supplied one-variable test against a segment polynomial over that segment's interval. ([`segmentTestPair`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L986))

**Integral on the radial interval.** Definition. This helper uses ordinary one-dimensional measure; callers insert lineWeight explicitly when it is needed. ([`radialInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L989))

**Integral on the height interval.** Definition. Integrates over the closed height interval. Boundary endpoints have no extra mass in the integral. ([`heightInt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L991))

**Radial derivative matrix entry.** Definition. Pairs a derivative of one radial basis polynomial with another, using lineWeight and the reference-interval vanishing factor. ([`radialStiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L993))

**Height derivative matrix entry.** Definition. Pairs a height derivative with a basis polynomial using the corresponding reference-interval factor. ([`heightStiff`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L996))

**Multiplication by the radius.** Definition. Represents multiplication by r in the weighted radial basis through an integral of two basis polynomials. ([`radialShift`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L999))

**Coordinate unit row.** Definition. Returns the row that reads one tagged datum. It is an exact algebraic coordinate selector. ([`unitAt`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1002))

**Angular derivative of velocity.** Definition. Combines multiplication by the angular frequency with rotation of the cylindrical basis. The radial and angular components acquire opposite frame-coupling terms. ([`turnRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1011))

**All cell relation rows.** Definition. Builds the ten families of exact linear relations from differentiation, divergence, axis behaviour and trace matching. Some index cases deliberately produce zero rows; independent selected rows are checked later. ([`relationRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1030))

**Identify boundary coordinates.** Proposition. Marks side velocity, side gradient, pressure, corner velocity and corner stream blocks as skeleton data. Volume and extra-side coefficients are excluded. ([`IsSkeletonDatum`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1101))

**Selected cell relations.** Structure. Identifies every elimination row with a row of relationRow and restricts the retained skeleton to skeleton data. It deliberately keeps the selector and solved-block data explicit. ([`IsCellParam`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1167))

**Side derivative moment row.** Definition. Combines segmented gradient moments with the integrals of a whole-side test against each segment test polynomial. ([`sideGradientRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1181))

**Side velocity moment row.** Definition. Combines velocity moments on the side's segments, retaining the q+2 test range. ([`sideVelocityRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1191))

**Angular side derivative row.** Definition. Applies the angular-frequency and cylindrical-frame terms to the assembled side velocity row. ([`turnSideRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1195))

**Primitive of the radial test weight.** Definition. Integrates ρ times the supplied test function from zero to r. This is a helper for weighted trace identities, rather than a new certificate condition. ([`radialWeightIntegral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1294))

**Pull a form back along rows.** Definition. The returned matrix is the conjugate-row pullback of the supplied form. Complex conjugation is on the first row factor. ([`formOfRows`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1400))

**Locations of low-order coefficients.** Structure. Abstracts the map from a cell's gradient and velocity coefficients and face rows to a larger coordinate set. ([`LowIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1408))

**Tensor-product cell polynomial.** Definition. Multiplies one radial and one height basis polynomial, with normalisation supplied by the basis predicate. ([`basisFn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1414))

**Meridian monomial.** Definition. Uses ordinary r and z powers, unlike CellPoly.eval, which uses affine reference coordinates. ([`monomial`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1416))

**Radial derivative of a real test.** Definition. Differentiates a real test function while fixing height; regularity is a separate mathematical input. ([`radialSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1418))

**Height derivative of a real test.** Definition. Differentiates a real test function while fixing radius. ([`heightSlope`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1420))

**Integral over a cell rectangle.** Definition. Uses ordinary two-dimensional measure. Callers supply the cylindrical or polynomial-basis radial weight explicitly. ([`rectIntegral`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1422))

**Cylindrical frame rotation.** Definition. Records the two nonzero coefficients that couple radial and angular basis directions under rotation. ([`frameTurn`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1427))

**Angular derivative of one entry.** Definition. Combines the harmonic frequency with frame rotation in both indices of a gradient array. ([`angularComb`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1430))

**Angular derivative of an array.** Definition. Applies angularComb to a linear combination of gradient components, retaining both frame corrections. ([`angularArray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1434))

**Select one gradient component.** Definition. The coefficient array isolates a single ordered gradient entry, without imposing symmetry. ([`unitArray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1437))

**Select one curl component.** Definition. The alternating array extracts the appropriate difference of gradient entries with the same convention as curlComp. ([`curlArray`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1439))

**Row for a gradient combination.** Definition. Combines low-gradient coordinate selectors with the supplied component array at one harmonic and one polynomial index. ([`lowRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1446))

**Radial-face component row.** Definition. Combines stored radial-face rows with an array selecting gradient or curl components. ([`radialFaceComp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1449))

**Height-face component row.** Definition. The height-face version keeps the same component convention and its own polynomial-index direction. ([`heightFaceComp`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1452))

**Pair a polynomial test with data.** Definition. Expands a test pairing through the known low-gradient coefficients, using integrals against tensor-product basis functions. ([`lowPairRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1455))

**Height monomial moment.** Definition. Integrates a power of z against a height basis polynomial over the cell interval. ([`heightMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1459))

**Weighted radial monomial moment.** Definition. Integrates a power of r against a radial basis polynomial with the axis-dependent lineWeight. ([`radialMoment`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1461))

**Known radial derivative energy.** Definition. Forms the derivative contribution already determined by low coefficients, including innerRadius and the reference vanishing factor. ([`radialProjForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1463))

**Known height derivative energy.** Definition. Forms the corresponding height derivative contribution using the height reference coordinate. ([`heightProjForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1468))

**Interior radial test weight.** Definition. The weight combines r−r₁ with the radial reference vanishing factor and is used by the off-axis inner form. ([`radialInnerWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1473))

**Interior height test weight.** Definition. Combines r−r₁ with the height reference vanishing factor for the off-axis inner form. ([`heightInnerWeight`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1475))

**Interior radial derivative bound.** Definition. Uses an inverse Gram matrix on degrees below Q−1 in radius and through Q in height. Natural subtraction makes the index empty for small Q. ([`radialInnerForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1477))

**Weighted outer radial test.** Definition. Multiplies a meridian monomial by the basis lineWeight; this is a test function, not a coordinate value. ([`radialOuterTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1487))

**Radial boundary derivative row.** Definition. Combines moments on both radial faces with a differentiated interior test. The displayed plus signs follow the reference-coordinate factors already included in the formula. ([`radialOuterRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1489))

**Height boundary derivative row.** Definition. Combines height-face moments and an interior derivative of r times the height reference coordinate and test monomial. ([`heightOuterRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1499))

**Axis-compatible angular test.** Definition. Adds a factor r to the monomial so that the angular test family has the required axis behaviour. ([`angularTest`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1509))

**Angular energy off the axis.** Definition. Adds an inverse-r₂ diagonal form to a weighted test-supremum remainder. It is selected only in the off-axis component form. ([`angularOffForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1517))

**Resolved gradient and curl energy.** Definition. Sums component derivative forms with mode weights and subtracts the prescribed highest-degree penalty. ([`energyForm`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1538))

**Gradient or velocity basis slot.** Inductive type. The two constructors distinguish a nine-component gradient basis element from a three-component velocity element, with different degree cutoffs. ([`LowSlot`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1546))

**Field represented by one low slot.** Definition. A gradient slot has zero velocity and a velocity slot has zero gradient. Each nonzero component is one tensor-product basis function. ([`slotValue`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1551))

**Embed a low slot in cell data.** Definition. Routes a gradient or velocity slot through the corresponding map in LowIndex. ([`slotIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1559))

**Read one low coefficient.** Definition. The row is one at the embedded slot and zero elsewhere; it includes a harmonic label as well as the slot constructor. ([`slotRow`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1563))

**Low rows supplied by a layout.** Definition. Connects abstract LowIndex to the tagged CellDatum slots and translates two radial plus two height faces into the four-side numbering. ([`layoutIndex`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L1629))

**Substitute the radial coordinate.** Definition. Replaces the first polynomial variable by a complex constant while leaving the second variable unchanged. ([`atFirst`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2548))

**Substitute the height coordinate.** Definition. Replaces the second polynomial variable while preserving the first. This is used in exact polynomial join identities. ([`atSecond`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2551))

**Repeated radial polynomial derivative.** Definition. Iterates formal differentiation in the first variable. Order zero leaves the polynomial unchanged. ([`tDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2554))

**Repeated height polynomial derivative.** Definition. Iterates formal differentiation in the second variable, which represents the chart height rather than a Cartesian coordinate. ([`xDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2556))

**Conjugate spline coefficients.** Definition. Keeps the mesh and conjugates each polynomial coefficient. This is the coefficient-level operation used for harmonic reality conditions. ([`conj`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2571))

**Zero spline pieces after a cutoff.** Proposition. Quantifies over all natural indices, using one as the default radial knot. Thus a cutoff below one also constrains out-of-range pieces, not only the serialised valid cells. ([`VanishesFrom`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2574))

**Prescribed radial endpoint powers.** Definition. Forms σ^e₀(1−σ)^e₁, the origin and infinity factors used in the field formulas. The exponents are natural numbers. ([`weightPoly`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2595))

**Radial derivative in the chart.** Definition. Applies σ(1−σ)∂σ, corresponding to |y|∂|y| in (B.3). Radial phase terms are added by later operators. ([`radialScale`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2597))

**Derivative in chart height.** Definition. Differentiates the chart coefficient in η while fixing σ. This is separate from the physical height derivative in cylindrical coordinates. ([`heightDeriv`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/StatementDefs.lean#L2602))

### Breakdown.FracCert.Defs (also in the readable files)

**Abstract steady certificate data.** Structure. Also inherits the 46 directly declared fields of Breakdown.SteadyCert.FracCertData; those glosses are stored at the parent declaration. ([`FracCertData`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCert/Defs.lean#L117))
<!-- /passage:front -->

