
<!-- passage:front -->
# Library guide 25: Breakdown/FreqTr, Breakdown/Held, Breakdown/Profile, Breakdown/Spectral

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) **25** [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FreqTr.Advection` to `Breakdown.Spectral.SpectrumEigen` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.
<!-- /passage:front -->

## Breakdown/FreqTr

<!-- passage:sec-breakdown-freqtr -->

### Breakdown.FreqTr.Advection

Coordinate pairing algebra identifies physical advection with the trilinear form built from recovered velocity and derivatives.

**Source namespace:** Breakdown.Freq.Internal.Advection.

**Pair a coordinate expansion.** The sum of coordinate weighted pairings of a linear map equals the pairing of that map applied to the full vector. Source: Breakdown.Freq.Internal.Advection.sum_coord_inner in Breakdown.FreqTr.Advection, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Advection.lean#L12).

**Source namespace:** Breakdown.Freq.

**Advection as a trilinear pairing.** The velocity and derivative recovery interfaces identify physical advection with the Fourier space trilinear pairing. Source: Breakdown.Freq.advectionTrilinear in Breakdown.FreqTr.Advection, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Advection.lean#L24).

### Breakdown.FreqTr.Assembly

Heat, dilation, bilinear interaction, dense tests and compactness are assembled into the concrete mild framework and its physical realization.

**Source namespace:** Breakdown.Freq.

**Symmetry of the bilinear operator.** Exchanging the two inputs leaves the chosen bilinear interaction unchanged. Source: Breakdown.Freq.bilinX_symm in Breakdown.FreqTr.Assembly, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Assembly.lean#L10).

**The bilinear operator norm bound.** At positive time the bilinear operator norm is bounded by the chosen constant times time to the power negative three quarters. Source: Breakdown.Freq.bilinX_opNorm_le in Breakdown.FreqTr.Assembly, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Assembly.lean#L20).

**Assemble the mild framework.** The construction packages heat, dilation, bilinear interaction, dense tests and compactness into the abstract mild framework. Source: Breakdown.Freq.frameOf in Breakdown.FreqTr.Assembly, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Assembly.lean#L25).

**Assemble the physical realization.** The construction adds rotations, the physical embedding and the weak to mild implication to the concrete mild framework. Source: Breakdown.Freq.realizationOf in Breakdown.FreqTr.Assembly, line 48. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Assembly.lean#L48).

### Breakdown.FreqTr.Basic

The Fourier symbol subspace, total operator restrictions, velocity specification and bilinear specification define the concrete homogeneous-energy model.

**Source namespace:** Breakdown.Freq.

**Complex three dimensional vectors.** The complex vector space is three dimensional Euclidean space over the complex numbers. Source: Breakdown.Freq.CSpace in Breakdown.FreqTr.Basic, line 12. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L12).

**Square integrable complex fields.** The complex L2 space consists of square integrable complex vector fields modulo almost everywhere equality. Source: Breakdown.Freq.L2C in Breakdown.FreqTr.Basic, line 14. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L14).

**Square integrable real fields.** The real L2 space consists of square integrable spatial vector fields modulo almost everywhere equality. Source: Breakdown.Freq.L2R in Breakdown.FreqTr.Basic, line 16. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L16).

**The sixth exponent is admissible.** The instance records that the L6 exponent is at least one. Source: Breakdown.Freq.factOneLeSix in Breakdown.FreqTr.Basic, line 18. [Instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L18).

**Sixth power integrable real fields.** The real L6 space consists of spatial vector fields with integrable sixth power norm modulo almost everywhere equality. Source: Breakdown.Freq.L6R in Breakdown.FreqTr.Basic, line 20. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L20).

**A total map into an Lp space.** The map uses the field's Lp equivalence class when it has finite Lp norm and returns zero otherwise. Source: Breakdown.Freq.toLpOrZero in Breakdown.FreqTr.Basic, line 22. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L22).

**Include real vectors in complex space.** The continuous real linear inclusion sends each real coordinate to its complex value. Source: Breakdown.Freq.complexifyVec in Breakdown.FreqTr.Basic, line 26. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L26).

**Take the real vector part.** The continuous real linear map takes the real part of each complex coordinate. Source: Breakdown.Freq.realVec in Breakdown.FreqTr.Basic, line 32. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L32).

**Conjugate each vector coordinate.** The continuous real linear map conjugates every complex vector coordinate. Source: Breakdown.Freq.conjVec in Breakdown.FreqTr.Basic, line 38. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L38).

**Complex scalar multiplication.** Multiplication by a complex scalar is packaged as a continuous real linear map. Source: Breakdown.Freq.cmul in Breakdown.FreqTr.Basic, line 44. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L44).

**Complexify an L2 field.** The induced L2 operator complexifies each vector value of a real field. Source: Breakdown.Freq.complexify in Breakdown.FreqTr.Basic, line 47. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L47).

**Take real parts of an L2 field.** The induced L2 operator takes the real vector part of a complex field. Source: Breakdown.Freq.realPart in Breakdown.FreqTr.Basic, line 49. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L49).

**The unitary L2 Fourier transform.** The L2 Fourier transform is a complex linear isometric equivalence. Source: Breakdown.Freq.freqTrL2 in Breakdown.FreqTr.Basic, line 51. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L51).

**Fourier transform over real scalars.** The same L2 Fourier transform is viewed as a continuous real linear map. Source: Breakdown.Freq.freqTrR in Breakdown.FreqTr.Basic, line 53. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L53).

**Inverse transform over real scalars.** The inverse L2 Fourier transform is viewed as a continuous real linear map. Source: Breakdown.Freq.freqTrInvR in Breakdown.FreqTr.Basic, line 56. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L56).

**Recover a real physical field.** The physical field map takes the real part after the inverse L2 Fourier transform. Source: Breakdown.Freq.toPhys in Breakdown.FreqTr.Basic, line 59. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L59).

**An almost everywhere operator formula.** The realization predicate specifies the operator almost everywhere by a change of frequency and a pointwise linear map. Source: Breakdown.Freq.IsRealizedBy in Breakdown.FreqTr.Basic, line 61. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L61).

**The complex frequency vector.** The frequency vector is the complexification of the real frequency. Source: Breakdown.Freq.freqVec in Breakdown.FreqTr.Basic, line 68. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L68).

**Projection along the frequency.** The longitudinal operator projects onto the frequency direction with the inverse squared radius normalization. Source: Breakdown.Freq.longitudinal in Breakdown.FreqTr.Basic, line 70. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L70).

**Reflect and conjugate the symbol.** The operator composes frequency negation with coordinatewise conjugation. Source: Breakdown.Freq.reflConj in Breakdown.FreqTr.Basic, line 74. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L74).

**Completeness of the symbol space.** The closed solenoidal symbol subspace inherits completeness. Source: anonymous instance in Breakdown.FreqTr.Basic, line 83. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L83).

**Restrict an operator to the state space.** The restricted operator uses its action on the invariant symbol subspace when invariance holds and returns zero otherwise. Source: Breakdown.Freq.restrictX in Breakdown.FreqTr.Basic, line 87. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L87).

**The heat multiplier on L2.** The L2 heat operator multiplies each frequency by the heat factor. Source: Breakdown.Freq.heatL2 in Breakdown.FreqTr.Basic, line 92. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L92).

**Dilation on L2 symbols.** The L2 dilation rescales both frequency and amplitude by the inverse square root of its parameter. Source: Breakdown.Freq.dilL2 in Breakdown.FreqTr.Basic, line 97. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L97).

**Rotate a complex vector.** The complex vector rotation applies the matrix of the given real spatial isometry. Source: Breakdown.Freq.rotC in Breakdown.FreqTr.Basic, line 102. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L102).

**Rotate an L2 symbol.** The symbol rotation rotates vector values and composes frequencies with the inverse spatial isometry. Source: Breakdown.Freq.rotL2 in Breakdown.FreqTr.Basic, line 108. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L108).

**The gradient embedding symbol.** The embedding symbol is negative imaginary coordinate divided by the frequency radius. Source: Breakdown.Freq.gradSymbol in Breakdown.FreqTr.Basic, line 113. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L113).

**The derivative recovery symbol.** The derivative symbol is imaginary coordinate divided by the frequency radius. Source: Breakdown.Freq.derivSymbol in Breakdown.FreqTr.Basic, line 115. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L115).

**A coordinate derivative field.** The partial field is the classical derivative evaluated in the chosen unit vector direction. Source: Breakdown.Freq.partialField in Breakdown.FreqTr.Basic, line 117. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L117).

**Embed the gradient in Fourier space.** The gradient embedding sums the transformed coordinate derivatives after multiplying by their embedding symbols. Source: Breakdown.Freq.ofGrad in Breakdown.FreqTr.Basic, line 119. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L119).

**Recover one derivative from a state.** The derivative recovery operator multiplies the Fourier state by a derivative symbol and takes its real inverse transform. Source: Breakdown.Freq.partialX in Breakdown.FreqTr.Basic, line 124. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L124).

**The velocity recovery requirement.** The velocity specification requires the recovery map to return every embedded solenoidal test field in L6. Source: Breakdown.Freq.VelocitySpec in Breakdown.FreqTr.Basic, line 127. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L127).

**The smoothed first derivative factor.** The factor is two pi times frequency radius multiplied by the heat exponential. Source: Breakdown.Freq.phiFactor in Breakdown.FreqTr.Basic, line 132. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L132).

**A smoothed derivative test operator.** The operator multiplies the Fourier state by the smoothed first derivative factor and takes its real inverse transform. Source: Breakdown.Freq.phiX in Breakdown.FreqTr.Basic, line 134. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L134).

**The physical trilinear pairing.** The trilinear pairing integrates velocity coordinates against recovered derivatives and the third test field. Source: Breakdown.Freq.trilinear in Breakdown.FreqTr.Basic, line 137. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L137).

**The symmetrised interaction form.** The interaction form is negative one half of the two trilinear pairings obtained by exchanging the input states. Source: Breakdown.Freq.bilinForm in Breakdown.FreqTr.Basic, line 140. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L140).

**The bilinear operator requirement.** The bilinear specification requires its inner product with every state to equal the symmetrised interaction form. Source: Breakdown.Freq.BilinSpec in Breakdown.FreqTr.Basic, line 143. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L143).

**The negative componentwise Laplacian.** The field is the negative sum of its second coordinate derivatives. Source: Breakdown.Freq.negSsp in Breakdown.FreqTr.Basic, line 148. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L148).

**The Laplacian frequency factor.** The factor is four pi squared times the squared frequency radius. Source: Breakdown.Freq.sspFactor in Breakdown.FreqTr.Basic, line 150. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L150).

**A Laplacian relation between states.** The relation requires the second state to equal the first multiplied by the Laplacian factor almost everywhere. Source: Breakdown.Freq.IsSspOf in Breakdown.FreqTr.Basic, line 152. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L152).

**A square root Laplacian relation.** The relation requires the second state to equal the first multiplied by two pi times radius almost everywhere. Source: Breakdown.Freq.IsHalfSspOf in Breakdown.FreqTr.Basic, line 154. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L154).

**The span of embedded test fields.** The test submodule is the real linear span of the embedded solenoidal test fields. Source: Breakdown.Freq.testSpan in Breakdown.FreqTr.Basic, line 156. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Basic.lean#L156).

### Breakdown.FreqTr.BilinCompact

Frequency truncation and physical localization estimates make the bilinear interaction with an embedded test field compact.

**Source namespace:** Breakdown.Freq.Internal.BilinCompact.

**The L6 times L3 product estimate.** The exponent instance supplies the Hölder relation placing an L6 times L3 product in L2. Source: Breakdown.Freq.Internal.BilinCompact.lpProd_six_three in Breakdown.FreqTr.BilinCompact, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L14).

**Nonnegative derivative heat factor.** The smoothed derivative factor is nonnegative. Source: Breakdown.Freq.Internal.BilinCompact.phiFactor_nonneg in Breakdown.FreqTr.BilinCompact, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L25).

**The high frequency factor bound.** Beyond a positive frequency radius the factor is bounded by the reciprocal of two pi times time times that radius. Source: Breakdown.Freq.Internal.BilinCompact.phiFactor_tail in Breakdown.FreqTr.BilinCompact, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L28).

**A uniform derivative heat bound.** At positive time the factor is bounded by two pi plus the reciprocal of two pi times time. Source: Breakdown.Freq.Internal.BilinCompact.phiFactor_le in Breakdown.FreqTr.BilinCompact, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L47).

**Continuity of the derivative factor.** The smoothed derivative factor is continuous in frequency. Source: Breakdown.Freq.Internal.BilinCompact.continuous_phiFactor in Breakdown.FreqTr.BilinCompact, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L63).

**Multiply by the derivative heat factor.** The operator acts on L2 symbols by multiplication by the smoothed derivative factor. Source: Breakdown.Freq.Internal.BilinCompact.phiMul in Breakdown.FreqTr.BilinCompact, line 66. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L66).

**The multiplier formula almost everywhere.** Under the realization interface, the multiplier agrees almost everywhere with its pointwise scalar formula at positive time. Source: Breakdown.Freq.Internal.BilinCompact.phiMul_ae in Breakdown.FreqTr.BilinCompact, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L69).

**Complexification preserves norm.** Embedding a real vector in complex space preserves its norm. Source: Breakdown.Freq.Internal.BilinCompact.norm_complexifyVec in Breakdown.FreqTr.BilinCompact, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L83).

**A Lipschitz bound for characters.** The distance between two Fourier characters is at most two pi times their phase difference. Source: Breakdown.Freq.Internal.BilinCompact.eChar_sub_le in Breakdown.FreqTr.BilinCompact, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L89).

**Bound a Fourier value by L1 norm.** The norm of a Fourier transform value is bounded by the integral of the original norm. Source: Breakdown.Freq.Internal.BilinCompact.norm_freqTr_le in Breakdown.FreqTr.BilinCompact, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L100).

**Continuity of an integrable transform.** The Fourier transform of an integrable field is continuous. Source: Breakdown.Freq.Internal.BilinCompact.continuous_freqTr_of_integrable in Breakdown.FreqTr.BilinCompact, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L103).

**A compact support transform bound.** The Fourier transform of a field supported in a ball has the stated frequency difference bound in terms of its L1 norm and support radius. Source: Breakdown.Freq.Internal.BilinCompact.freqTr_sub_le in Breakdown.FreqTr.BilinCompact, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L107).

**Cut off and complexify a field.** The cut field restricts the complexified real field to the chosen spatial set. Source: Breakdown.Freq.Internal.BilinCompact.cutField in Breakdown.FreqTr.BilinCompact, line 134. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L134).

**Fields with bounded norm and support.** The set contains L2 fields with the stated norm bound that vanish almost everywhere outside the chosen set. Source: Breakdown.Freq.Internal.BilinCompact.supSet in Breakdown.FreqTr.BilinCompact, line 137. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L137).

**Square integrability after inclusion.** The pointwise complexification of a real L2 field is square integrable. Source: Breakdown.Freq.Internal.BilinCompact.memLp_complexify in Breakdown.FreqTr.BilinCompact, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L140).

**Square integrability after cutoff.** Restricting a complexified L2 field to a compact set preserves square integrability. Source: Breakdown.Freq.Internal.BilinCompact.memLp_cutField in Breakdown.FreqTr.BilinCompact, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L143).

**Integrability on a compact set.** The compactly restricted L2 field is integrable. Source: Breakdown.Freq.Internal.BilinCompact.integrable_cutField in Breakdown.FreqTr.BilinCompact, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L146).

**The L2 norm as an integral.** The integral of the squared norm of an L2 representative equals its squared L2 norm. Source: Breakdown.Freq.Internal.BilinCompact.integral_sq_norm in Breakdown.FreqTr.BilinCompact, line 153. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L153).

**Bound the cutoff L1 norm.** The cutoff L1 norm is bounded by half the compact set's volume plus half the squared L2 norm. Source: Breakdown.Freq.Internal.BilinCompact.integral_norm_cutField_le in Breakdown.FreqTr.BilinCompact, line 159. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L159).

**Identify a supported L2 field.** A field supported almost everywhere on the compact set has the same complex L2 class as its cutoff representative. Source: Breakdown.Freq.Internal.BilinCompact.complexify_eq_toLp in Breakdown.FreqTr.BilinCompact, line 180. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L180).

**Read the supported Fourier transform.** The L2 Fourier transform of the supported field agrees almost everywhere with the ordinary transform of its cutoff representative. Source: Breakdown.Freq.Internal.BilinCompact.freqTrR_complexify_ae in Breakdown.FreqTr.BilinCompact, line 195. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L195).

**A closed frequency ball.** The frequency ball is the closed ball centered at zero with the specified radius. Source: Breakdown.Freq.Internal.BilinCompact.ballR in Breakdown.FreqTr.BilinCompact, line 208. [Type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L208).

**Extend a weighted ball field by zero.** The extension multiplies the bounded continuous ball field by the derivative heat factor inside the ball and is zero outside. Source: Breakdown.Freq.Internal.BilinCompact.extendField in Breakdown.FreqTr.BilinCompact, line 210. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L210).

**The extension is supported in the ball.** The extended field equals its own indicator restriction to the closed frequency ball. Source: Breakdown.Freq.Internal.BilinCompact.extendField_eq in Breakdown.FreqTr.BilinCompact, line 213. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L213).

**Continuity on the frequency ball.** The weighted extension is continuous when restricted to its closed frequency ball. Source: Breakdown.Freq.Internal.BilinCompact.continuousOn_extendField in Breakdown.FreqTr.BilinCompact, line 220. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L220).

**Bound the extended field.** The norm of the weighted extension is bounded by the stated heat factor constant times the uniform norm of the ball field. Source: Breakdown.Freq.Internal.BilinCompact.norm_extendField_le in Breakdown.FreqTr.BilinCompact, line 228. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L228).

**The extension is square integrable.** At positive time the weighted extension belongs to L2. Source: Breakdown.Freq.Internal.BilinCompact.memLp_extendField in Breakdown.FreqTr.BilinCompact, line 236. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L236).

**The cutoff field as an L2 class.** The cutoff L2 class is obtained from the weighted zero extension. Source: Breakdown.Freq.Internal.BilinCompact.cutLp in Breakdown.FreqTr.BilinCompact, line 244. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L244).

**The cutoff class has its expected values.** The cutoff L2 class agrees almost everywhere with the weighted extension at positive time. Source: Breakdown.Freq.Internal.BilinCompact.cutLp_ae in Breakdown.FreqTr.BilinCompact, line 246. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L246).

**A Lipschitz bound for the cutoff map.** The cutoff map from bounded continuous ball fields into L2 has a uniform Lipschitz constant. Source: Breakdown.Freq.Internal.BilinCompact.dist_cutLp_le in Breakdown.FreqTr.BilinCompact, line 252. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L252).

**Restrict a transform to a ball.** The compactly supported physical field's transform is packaged as a bounded continuous function on the frequency ball. Source: Breakdown.Freq.Internal.BilinCompact.fcut in Breakdown.FreqTr.BilinCompact, line 273. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L273).

**Evaluate the restricted transform.** The bounded continuous ball function evaluates to the Fourier transform of the cutoff physical field. Source: Breakdown.Freq.Internal.BilinCompact.fcut_apply in Breakdown.FreqTr.BilinCompact, line 278. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L278).

**Control the discarded frequency tail.** The derivative weighted transform differs from its ball cutoff by at most the stated reciprocal radius factor times the transform's L2 norm. Source: Breakdown.Freq.Internal.BilinCompact.tail_le in Breakdown.FreqTr.BilinCompact, line 281. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L281).

**Compactness of restricted transforms.** Transforms of fields with common compact support and bounded L2 norm have compact closure when restricted to a frequency ball. Source: Breakdown.Freq.Internal.BilinCompact.isCompact_closure_fcut in Breakdown.FreqTr.BilinCompact, line 302. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L302).

**Total boundedness after smoothing.** The derivative weighted transforms of the supported bounded family form a totally bounded subset of L2. Source: Breakdown.Freq.Internal.BilinCompact.totallyBounded_image in Breakdown.FreqTr.BilinCompact, line 341. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L341).

**One symmetrised advection term.** The term adds the test velocity times a recovered derivative to the state velocity times the test derivative. Source: Breakdown.Freq.Internal.BilinCompact.advectTerm in Breakdown.FreqTr.BilinCompact, line 380. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L380).

**A bounded supported advection family.** Advection against a fixed test field sends unit norm states into one uniformly bounded L2 family supported on that test field. Source: Breakdown.Freq.Internal.BilinCompact.advect_mem in Breakdown.FreqTr.BilinCompact, line 383. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCompact.lean#L383).

### Breakdown.FreqTr.BilinCont

The heat time-shift identity and bounded bilinear realization give continuity of the interaction on positive times.

**Source namespace:** Breakdown.Freq.Internal.BilinCont.

**Heat factors add their times.** Multiplying the derivative heat factor by a nonnegative time heat factor adds the two times. Source: Breakdown.Freq.Internal.BilinCont.phiFactor_mul_heatFactor in Breakdown.FreqTr.BilinCont, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCont.lean#L12).

**Heat shifts the smoothed derivative.** Applying the smoothed derivative after heat gives the operator with the summed times. Source: Breakdown.Freq.Internal.BilinCont.phiX_heatX in Breakdown.FreqTr.BilinCont, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCont.lean#L19).

**The selected interaction meets its form.** At positive time, the existence interface ensures the chosen bilinear operator satisfies its pairing specification. Source: Breakdown.Freq.Internal.BilinCont.bilinX_spec in Breakdown.FreqTr.BilinCont, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCont.lean#L37).

**Shift the bilinear interaction in time.** The later bilinear interaction equals heat evolution of the earlier interaction under the stated time ordering. Source: Breakdown.Freq.Internal.BilinCont.bilinX_shift in Breakdown.FreqTr.BilinCont, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCont.lean#L42).

**Source namespace:** Breakdown.Freq.

**Prove bilinear time continuity.** The theorem discharges the bilinear continuity interface from the stated existence, bounds, realization and heat interfaces. Source: Breakdown.Freq.bilinContinuous in Breakdown.FreqTr.BilinCont, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinCont.lean#L58).

### Breakdown.FreqTr.BilinDilate

Fourier change of variables and trilinear scaling establish the precise time and amplitude factors in bilinear dilation covariance.

**Source namespace:** Breakdown.Freq.Internal.BilinDilate.

**Dilate an inverse Fourier transform.** Positive frequency dilation becomes inverse spatial dilation with the reciprocal cubic Jacobian under inverse transformation. Source: Breakdown.Freq.Internal.BilinDilate.freqTrInv_comp_smul_aux in Breakdown.FreqTr.BilinDilate, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L12).

**A nonzero dilation equivalence.** A nonzero scalar dilation is packaged as a continuous real linear equivalence of space. Source: Breakdown.Freq.Internal.BilinDilate.scaleEquiv in Breakdown.FreqTr.BilinDilate, line 24. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L24).

**Evaluate the dilation equivalence.** The continuous dilation equivalence acts by scalar multiplication. Source: Breakdown.Freq.Internal.BilinDilate.scaleEquiv_apply in Breakdown.FreqTr.BilinDilate, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L27).

**Frequency dilation on L2.** The operator is the total fieldOp realization of composition with scalar frequency dilation. Source: Breakdown.Freq.Internal.BilinDilate.scaleOp in Breakdown.FreqTr.BilinDilate, line 29. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L29).

**The dilation formula almost everywhere.** For nonzero scale and a realized multiplier calculus, the L2 dilation agrees almost everywhere with frequency composition. Source: Breakdown.Freq.Internal.BilinDilate.scaleOp_ae in Breakdown.FreqTr.BilinDilate, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L32).

**Dilation preserves a.e. equality.** Composition with a nonzero scalar dilation preserves almost everywhere equality. Source: Breakdown.Freq.Internal.BilinDilate.comp_smul_ae in Breakdown.FreqTr.BilinDilate, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L38).

**Conjugate inverse transform by dilation.** The inverse L2 transform and positive frequency dilation commute with inverse scale and reciprocal cubic amplitude. Source: Breakdown.Freq.Internal.BilinDilate.freqTrInvR_scaleOp in Breakdown.FreqTr.BilinDilate, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L42).

**Read the dilated inverse transform.** The inverse transformed dilated L2 field has the rescaled representative and reciprocal cubic amplitude almost everywhere. Source: Breakdown.Freq.Internal.BilinDilate.freqTrInv_scaleOp_ae in Breakdown.FreqTr.BilinDilate, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L70).

**Read the physical L2 representative.** The physical L2 field is almost everywhere the real part of the inverse transformed symbol. Source: Breakdown.Freq.Internal.BilinDilate.toPhys_ae in Breakdown.FreqTr.BilinDilate, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L80).

**Dilate the physical representative.** Positive frequency dilation induces inverse physical dilation with the reciprocal cubic amplitude almost everywhere. Source: Breakdown.Freq.Internal.BilinDilate.toPhys_scaleOp_ae in Breakdown.FreqTr.BilinDilate, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L84).

**Read a bounded pointwise multiplier.** Under measurability and a uniform operator bound, the identity change of variables operator has the stated pointwise representative. Source: Breakdown.Freq.Internal.BilinDilate.fieldOp_id_ae in Breakdown.FreqTr.BilinDilate, line 91. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L91).

**Move dilation through a multiplier.** Compatible pointwise symbols allow the multiplier and nonzero frequency dilation to commute with their specified scalar factor. Source: Breakdown.Freq.Internal.BilinDilate.fieldOp_id_scaleOp in Breakdown.FreqTr.BilinDilate, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L96).

**Continuity of scalar multiplication.** The map sending a complex scalar to its real linear multiplication operator is continuous. Source: Breakdown.Freq.Internal.BilinDilate.cmul_cont in Breakdown.FreqTr.BilinDilate, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L108).

**The derivative symbol has degree zero.** The derivative recovery symbol is unchanged by a positive frequency dilation. Source: Breakdown.Freq.Internal.BilinDilate.derivSymbol_smul in Breakdown.FreqTr.BilinDilate, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L110).

**Bound the derivative recovery symbol.** The derivative recovery symbol has norm at most one. Source: Breakdown.Freq.Internal.BilinDilate.norm_derivSymbol_le in Breakdown.FreqTr.BilinDilate, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L121).

**Bound complex scalar multiplication.** The operator norm of complex multiplication is at most the scalar's complex norm. Source: Breakdown.Freq.Internal.BilinDilate.norm_cmul_le in Breakdown.FreqTr.BilinDilate, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L131).

**Measurability of the derivative symbol.** Each derivative recovery symbol is measurable. Source: Breakdown.Freq.Internal.BilinDilate.measurable_derivSymbol in Breakdown.FreqTr.BilinDilate, line 138. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L138).

**Measurability of the derivative map.** The operator valued derivative multiplier is almost everywhere strongly measurable. Source: Breakdown.Freq.Internal.BilinDilate.aesm_derivOp in Breakdown.FreqTr.BilinDilate, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L142).

**The derivative multiplier is contractive.** The pointwise derivative multiplier has operator norm at most one. Source: Breakdown.Freq.Internal.BilinDilate.norm_derivOp_le in Breakdown.FreqTr.BilinDilate, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L146).

**A nonnegative derivative heat factor.** The smoothed derivative factor is nonnegative. Source: Breakdown.Freq.Internal.BilinDilate.phiFactor_nonneg in Breakdown.FreqTr.BilinDilate, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L149).

**A square root time factor bound.** At positive time the smoothed derivative factor is at most the inverse square root of time. Source: Breakdown.Freq.Internal.BilinDilate.phiFactor_le in Breakdown.FreqTr.BilinDilate, line 152. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L152).

**Measurability of the derivative heat map.** The operator valued smoothed derivative multiplier is almost everywhere strongly measurable. Source: Breakdown.Freq.Internal.BilinDilate.aesm_phiOp in Breakdown.FreqTr.BilinDilate, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L166).

**Bound the derivative heat multiplier.** At positive time the pointwise derivative heat operator norm is at most the inverse square root of time. Source: Breakdown.Freq.Internal.BilinDilate.norm_phiOp_le in Breakdown.FreqTr.BilinDilate, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L172).

**Rescale the derivative heat factor.** Scaling time by the square of a positive factor equals inverse amplitude times frequency dilation of the original factor. Source: Breakdown.Freq.Internal.BilinDilate.phiFactor_scale in Breakdown.FreqTr.BilinDilate, line 180. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L180).

**Read dilation in the symbol space.** The state dilation is inverse square root amplitude times inverse square root frequency dilation. Source: Breakdown.Freq.Internal.BilinDilate.dilX_coe in Breakdown.FreqTr.BilinDilate, line 188. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L188).

**Expand derivative recovery.** A recovered coordinate derivative is the physical inverse transform of the state multiplied by its derivative symbol. Source: Breakdown.Freq.Internal.BilinDilate.partialX_eq in Breakdown.FreqTr.BilinDilate, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L201).

**Expand the smoothed derivative.** The smoothed derivative is the physical inverse transform of the state multiplied by its derivative heat factor. Source: Breakdown.Freq.Internal.BilinDilate.phiX_eq in Breakdown.FreqTr.BilinDilate, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L204).

**Scale a recovered derivative.** State dilation rescales the recovered derivative almost everywhere by its parameter and the square root spatial dilation. Source: Breakdown.Freq.Internal.BilinDilate.partialX_dilX in Breakdown.FreqTr.BilinDilate, line 207. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L207).

**Scale the smoothed test oppositely.** The inverse state dilation and rescaled smoothing time produce the stated inverse spatial scale and cubic amplitude. Source: Breakdown.Freq.Internal.BilinDilate.phiX_dilX_inv in Breakdown.FreqTr.BilinDilate, line 226. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L226).

**Move dilation across an inner product.** Positive frequency dilation moves to the other side of the L2 pairing with inverse scale and reciprocal cubic Jacobian. Source: Breakdown.Freq.Internal.BilinDilate.inner_scaleOp in Breakdown.FreqTr.BilinDilate, line 248. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L248).

**The adjoint of state dilation.** State dilation moves across the real inner product with inverse scale and a square root amplitude factor. Source: Breakdown.Freq.Internal.BilinDilate.dilX_adjoint in Breakdown.FreqTr.BilinDilate, line 265. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L265).

**Scale a trilinear coordinate term.** The stated scaling of the three vectors multiplies their coordinate pairing by the sixth power of the scale. Source: Breakdown.Freq.Internal.BilinDilate.summand_scale in Breakdown.FreqTr.BilinDilate, line 273. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L273).

**Integrate the sixth power scaling.** Integrating a sixth power weighted dilation leaves a cubic amplitude factor in three dimensions. Source: Breakdown.Freq.Internal.BilinDilate.integral_scale_six in Breakdown.FreqTr.BilinDilate, line 278. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L278).

**Scale the trilinear interaction.** Dilating the two state inputs transfers to the inverse dilation of the smoothed test with the stated cubic square root factor. Source: Breakdown.Freq.Internal.BilinDilate.trilinear_dilX in Breakdown.FreqTr.BilinDilate, line 284. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L284).

**The selected bilinear pairing.** At positive time, the chosen bilinear operator satisfies the pairing specification supplied by the existence interface. Source: Breakdown.Freq.Internal.BilinDilate.bilinX_spec in Breakdown.FreqTr.BilinDilate, line 315. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L315).

**Source namespace:** Breakdown.Freq.

**Prove bilinear dilation covariance.** The theorem discharges the bilinear dilation identity from existence, dilation, realization and velocity covariance interfaces. Source: Breakdown.Freq.bilinDilate in Breakdown.FreqTr.BilinDilate, line 325. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinDilate.lean#L325).

### Breakdown.FreqTr.BilinExists

Bounded trilinear pairings are represented by a continuous bilinear operator with the required symmetry and time-dependent norm bound.

**Source namespace:** Breakdown.Freq.Internal.BilinExists.

**The pointwise trilinear density.** The density sums velocity coordinates times pairings of recovered derivatives with the third field. Source: Breakdown.Freq.Internal.BilinExists.triDensity in Breakdown.FreqTr.BilinExists, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L12).

**Integrate the trilinear density.** The trilinear functional equals the integral of its pointwise density. Source: Breakdown.Freq.Internal.BilinExists.trilinear_eq in Breakdown.FreqTr.BilinExists, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L15).

**Add the first density input.** The trilinear density is additive in its first state input almost everywhere. Source: Breakdown.Freq.Internal.BilinExists.triDensity_add_left in Breakdown.FreqTr.BilinExists, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L18).

**Scale the first density input.** Scaling the first state input scales the trilinear density almost everywhere. Source: Breakdown.Freq.Internal.BilinExists.triDensity_smul_left in Breakdown.FreqTr.BilinExists, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L23).

**Add the second density input.** The trilinear density is additive in its second state input almost everywhere. Source: Breakdown.Freq.Internal.BilinExists.triDensity_add_mid in Breakdown.FreqTr.BilinExists, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L29).

**Scale the second density input.** Scaling the second state input scales the trilinear density almost everywhere. Source: Breakdown.Freq.Internal.BilinExists.triDensity_smul_mid in Breakdown.FreqTr.BilinExists, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L40).

**Add the third density input.** The trilinear density is pointwise additive in its third field input. Source: Breakdown.Freq.Internal.BilinExists.triDensity_add_right in Breakdown.FreqTr.BilinExists, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L52).

**Scale the third density input.** Scaling the third field input scales the trilinear density pointwise. Source: Breakdown.Freq.Internal.BilinExists.triDensity_smul_right in Breakdown.FreqTr.BilinExists, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L57).

**Replace an almost equal test field.** Almost everywhere equal third fields give almost everywhere equal trilinear densities. Source: Breakdown.Freq.Internal.BilinExists.triDensity_congr in Breakdown.FreqTr.BilinExists, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L63).

**Add the first trilinear input.** Integrability of the two densities makes the trilinear functional additive in its first state input. Source: Breakdown.Freq.Internal.BilinExists.trilinear_add_left in Breakdown.FreqTr.BilinExists, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L68).

**Scale the first trilinear input.** Scaling the first state scales the trilinear functional by the same real scalar. Source: Breakdown.Freq.Internal.BilinExists.trilinear_smul_left in Breakdown.FreqTr.BilinExists, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L73).

**Add the second trilinear input.** Integrability of the two densities makes the trilinear functional additive in its second state input. Source: Breakdown.Freq.Internal.BilinExists.trilinear_add_mid in Breakdown.FreqTr.BilinExists, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L77).

**Scale the second trilinear input.** Scaling the second state scales the trilinear functional by the same real scalar. Source: Breakdown.Freq.Internal.BilinExists.trilinear_smul_mid in Breakdown.FreqTr.BilinExists, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L82).

**Replace the trilinear test a.e..** Almost everywhere equal test fields give equal trilinear pairings. Source: Breakdown.Freq.Internal.BilinExists.trilinear_congr in Breakdown.FreqTr.BilinExists, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L86).

**Integrability after heat smoothing.** The trilinear and smoothing bounds make the smoothed test density integrable at positive time. Source: Breakdown.Freq.Internal.BilinExists.integrable_triDensity_phi in Breakdown.FreqTr.BilinExists, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L90).

**Add the smoothed test input.** At positive time and under the stated bounds, the trilinear pairing is additive in the state defining its smoothed test. Source: Breakdown.Freq.Internal.BilinExists.trilinear_phi_add in Breakdown.FreqTr.BilinExists, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L96).

**Scale the smoothed test input.** Scaling the state defining the smoothed test scales the trilinear pairing. Source: Breakdown.Freq.Internal.BilinExists.trilinear_phi_smul in Breakdown.FreqTr.BilinExists, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L108).

**Symmetry of the interaction form.** Exchanging the first two states leaves the symmetrised interaction form unchanged. Source: Breakdown.Freq.Internal.BilinExists.bilinForm_symm in Breakdown.FreqTr.BilinExists, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L116).

**Add the first interaction input.** The trilinear and smoothing bounds make the interaction form additive in its first state at positive time. Source: Breakdown.Freq.Internal.BilinExists.bilinForm_add_left in Breakdown.FreqTr.BilinExists, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L119).

**Scale the first interaction input.** Scaling the first state scales the interaction form. Source: Breakdown.Freq.Internal.BilinExists.bilinForm_smul_left in Breakdown.FreqTr.BilinExists, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L126).

**Add the interaction test input.** The trilinear and smoothing bounds make the interaction form additive in its test state at positive time. Source: Breakdown.Freq.Internal.BilinExists.bilinForm_add_right in Breakdown.FreqTr.BilinExists, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L131).

**Scale the interaction test input.** Scaling the test state scales the interaction form. Source: Breakdown.Freq.Internal.BilinExists.bilinForm_smul_right in Breakdown.FreqTr.BilinExists, line 136. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L136).

**Interpolate the smoothed test bounds.** The geometric mean of the L2 and L6 smoothed test norms has the stated time to negative three quarters bound. Source: Breakdown.Freq.Internal.BilinExists.sqrt_phi_le in Breakdown.FreqTr.BilinExists, line 141. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L141).

**Bound the full interaction form.** The interaction form is bounded by a common constant times time to negative three quarters and the product of the three state norms. Source: Breakdown.Freq.Internal.BilinExists.bilinForm_bound in Breakdown.FreqTr.BilinExists, line 169. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L169).

**Represent a bounded trilinear form.** A separately linear bounded trilinear form on a real Hilbert space has a bounded bilinear vector representation with the stated norm bound. Source: Breakdown.Freq.Internal.BilinExists.exists_bilin_of_form in Breakdown.FreqTr.BilinExists, line 200. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L200).

**Source namespace:** Breakdown.Freq.

**Construct and bound the interaction.** The theorem proves both existence of the bilinear interaction and its uniform time weighted bound. Source: Breakdown.Freq.bilinExistsBound in Breakdown.FreqTr.BilinExists, line 240. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinExists.lean#L240).

### Breakdown.FreqTr.BilinH1

For bounded H1 fields, the abstract bilinear interaction is identified with projected heat evolution of the physical advection field.

**Source namespace:** Breakdown.Freq.Internal.BilinH1.

**The Lp class represents its input.** When the input belongs to Lp, the total Lp conversion equals that input almost everywhere. Source: Breakdown.Freq.Internal.BilinH1.toLpOrZero_ae in Breakdown.FreqTr.BilinH1, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L13).

**The interaction has its required form.** At positive time the chosen interaction satisfies the bilinear pairing specification. Source: Breakdown.Freq.Internal.BilinH1.bilinX_spec in Breakdown.FreqTr.BilinH1, line 19. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L19).

**The pointwise multiplier representative.** A uniformly bounded measurable multiplier has the stated pointwise L2 action almost everywhere. Source: Breakdown.Freq.Internal.BilinH1.fieldOp_id_ae in Breakdown.FreqTr.BilinH1, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L25).

**Move complexification across a pairing.** Pairing a complexified real vector with a complex vector equals pairing the real vector with the other's real part. Source: Breakdown.Freq.Internal.BilinH1.inner_complexifyVec in Breakdown.FreqTr.BilinH1, line 31. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L31).

**The L2 real part pairing.** The complexification and real part operators are adjoint for the real L2 inner product. Source: Breakdown.Freq.Internal.BilinH1.inner_complexify in Breakdown.FreqTr.BilinH1, line 35. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L35).

**The Fourier isometry over the reals.** The complex Fourier isometry is restricted to a real linear isometry. Source: Breakdown.Freq.Internal.BilinH1.freqTrRealIsometry in Breakdown.FreqTr.BilinH1, line 46. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L46).

**Move Fourier transform across a pairing.** The real L2 adjoint of the Fourier transform is the inverse Fourier transform. Source: Breakdown.Freq.Internal.BilinH1.inner_freqTrR in Breakdown.FreqTr.BilinH1, line 49. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L49).

**A nonnegative heat derivative factor.** The smoothed derivative factor is nonnegative. Source: Breakdown.Freq.Internal.BilinH1.phiFactor_nonneg in Breakdown.FreqTr.BilinH1, line 53. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L53).

**An elementary multiplier bound.** The pointwise derivative heat multiplier norm is bounded by one plus the reciprocal of positive time. Source: Breakdown.Freq.Internal.BilinH1.norm_phiFactor_smul_le in Breakdown.FreqTr.BilinH1, line 56. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L56).

**The projected heat pairing.** Pairing the projected heat output with a state equals pairing the original physical field with its smoothed derivative test. Source: Breakdown.Freq.Internal.BilinH1.heatDivFree_inner in Breakdown.FreqTr.BilinH1, line 77. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L77).

**Expand physical advection.** Physical advection is the sum of velocity coordinates times the corresponding coordinate derivative fields. Source: Breakdown.Freq.Internal.BilinH1.advectionAt_eq_sum in Breakdown.FreqTr.BilinH1, line 97. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L97).

**Bounded advection belongs to L2.** A smooth H1 field with the stated uniform velocity and derivative bounds has square integrable advection. Source: Breakdown.Freq.Internal.BilinH1.advection_memLp in Breakdown.FreqTr.BilinH1, line 106. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L106).

**Source namespace:** Breakdown.Freq.

**Prove the H1 interaction formula.** The theorem identifies the bilinear interaction of an H1 field with the projected heat evolution of its physical advection. Source: Breakdown.Freq.bilinH1Formula in Breakdown.FreqTr.BilinH1, line 124. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinH1.lean#L124).

### Breakdown.FreqTr.BilinRotate

Rotation covariance of Fourier transforms, recovered derivatives and trilinear pairings proves covariance of the bilinear interaction.

**Source namespace:** Breakdown.Freq.Internal.BilinRotate.

**The complex linear rotation map.** The matrix of the real spatial isometry defines a continuous complex linear rotation of complex vectors. Source: Breakdown.Freq.Internal.BilinRotate.rotCc in Breakdown.FreqTr.BilinRotate, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L12).

**The two rotation maps agree.** The complex linear and real linear representations of the same vector rotation agree. Source: Breakdown.Freq.Internal.BilinRotate.rotCc_apply in Breakdown.FreqTr.BilinRotate, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L18).

**Rotate almost everywhere equality.** Composition with the inverse spatial isometry preserves almost everywhere equality. Source: Breakdown.Freq.Internal.BilinRotate.ae_comp_symm in Breakdown.FreqTr.BilinRotate, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L20).

**The L2 rotation representative.** The L2 rotation acts almost everywhere by inverse spatial composition and rotation of the vector values. Source: Breakdown.Freq.Internal.BilinRotate.rotL2_ae in Breakdown.FreqTr.BilinRotate, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L24).

**Rotate a Schwartz function.** The Schwartz rotation composes the inverse spatial isometry and the complex linear rotation of values. Source: Breakdown.Freq.Internal.BilinRotate.rotRapid in Breakdown.FreqTr.BilinRotate, line 29. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L29).

**Evaluate the Schwartz rotation.** The rotated Schwartz function is the vector rotation of the original value at the inverse rotated point. Source: Breakdown.Freq.Internal.BilinRotate.rotRapid_apply in Breakdown.FreqTr.BilinRotate, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L33).

**Rotation commutes with the L2 class.** Rotating a Schwartz function before forming its L2 class gives the L2 rotation of its original class. Source: Breakdown.Freq.Internal.BilinRotate.rotL2_toLp in Breakdown.FreqTr.BilinRotate, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L37).

**Invert a rotated Schwartz function.** Inverse Fourier transformation commutes with the simultaneous rotation of Schwartz arguments and values. Source: Breakdown.Freq.Internal.BilinRotate.freqTrInv_rotRapid in Breakdown.FreqTr.BilinRotate, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L45).

**Inverse transform under rotation.** The inverse L2 Fourier transform commutes with the L2 rotation operator. Source: Breakdown.Freq.Internal.BilinRotate.freqTrInv_rotL2 in Breakdown.FreqTr.BilinRotate, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L65).

**Expand a rotation in coordinates.** Each rotated coordinate is the sum of the original coordinates weighted by the isometry's matrix entries. Source: Breakdown.Freq.Internal.BilinRotate.apply_coord in Breakdown.FreqTr.BilinRotate, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L81).

**Rotate the real vector part.** Taking real parts after complex rotation equals real spatial rotation of the real parts. Source: Breakdown.Freq.Internal.BilinRotate.realVec_rotC in Breakdown.FreqTr.BilinRotate, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L89).

**Read the L2 real part.** The real part L2 operator agrees almost everywhere with coordinatewise real parts. Source: Breakdown.Freq.Internal.BilinRotate.realPart_ae in Breakdown.FreqTr.BilinRotate, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L95).

**The physical field rotates covariantly.** The physical field of a rotated symbol is almost everywhere the spatial pushforward of the original physical field. Source: Breakdown.Freq.Internal.BilinRotate.toPhys_rotL2 in Breakdown.FreqTr.BilinRotate, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L98).

**The realized multiplier acts pointwise.** A bounded measurable multiplier acts almost everywhere by its pointwise linear maps. Source: Breakdown.Freq.Internal.BilinRotate.fieldOp_id_ae in Breakdown.FreqTr.BilinRotate, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L109).

**Evaluate complex multiplication.** The multiplication operator acts as complex scalar multiplication on vectors. Source: Breakdown.Freq.Internal.BilinRotate.cmul_apply in Breakdown.FreqTr.BilinRotate, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L114).

**Scalar multiplication as an operator.** The real linear multiplication map is the complex scalar multiple of the identity restricted to real scalars. Source: Breakdown.Freq.Internal.BilinRotate.cmul_eq in Breakdown.FreqTr.BilinRotate, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L116).

**The derivative symbol is bounded.** The norm of the derivative recovery symbol is at most one. Source: Breakdown.Freq.Internal.BilinRotate.derivSymbol_norm_le in Breakdown.FreqTr.BilinRotate, line 120. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L120).

**Measurability of derivative multipliers.** The operator valued derivative multiplier is almost everywhere strongly measurable. Source: Breakdown.Freq.Internal.BilinRotate.deriv_meas in Breakdown.FreqTr.BilinRotate, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L125).

**A contractive derivative multiplier.** The derivative multiplier has operator norm at most one at every frequency. Source: Breakdown.Freq.Internal.BilinRotate.deriv_bound in Breakdown.FreqTr.BilinRotate, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L132).

**Bound a Gaussian weighted radius.** For positive Gaussian coefficient, radius times the Gaussian is at most one plus the reciprocal coefficient. Source: Breakdown.Freq.Internal.BilinRotate.scaled_exp_le in Breakdown.FreqTr.BilinRotate, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L143).

**A uniform smoothing factor bound.** At positive time the absolute derivative heat factor has the displayed uniform bound. Source: Breakdown.Freq.Internal.BilinRotate.phiFactor_le in Breakdown.FreqTr.BilinRotate, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L158).

**Measurability of the smoothing map.** The operator valued derivative heat multiplier is almost everywhere strongly measurable. Source: Breakdown.Freq.Internal.BilinRotate.phi_meas in Breakdown.FreqTr.BilinRotate, line 168. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L168).

**Bound the smoothing multiplier.** At positive time the derivative heat multiplier has the displayed uniform operator norm bound. Source: Breakdown.Freq.Internal.BilinRotate.phi_bound in Breakdown.FreqTr.BilinRotate, line 174. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L174).

**The smoothing multiplier rotates.** The radial derivative heat multiplier commutes with rotation on L2. Source: Breakdown.Freq.Internal.BilinRotate.phiOp_rot in Breakdown.FreqTr.BilinRotate, line 184. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L184).

**Read a finite sum of Lp classes.** A sum of three Lp classes equals the pointwise sum of their representatives almost everywhere. Source: Breakdown.Freq.Internal.BilinRotate.coeFn_sum3 in Breakdown.FreqTr.BilinRotate, line 194. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L194).

**Rotate the derivative symbols.** The derivative symbol after rotation is the coordinate sum of rotated derivative symbols with the rotation matrix coefficients. Source: Breakdown.Freq.Internal.BilinRotate.deriv_pt in Breakdown.FreqTr.BilinRotate, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L201).

**Rotate the derivative multipliers.** A coordinate derivative multiplier after L2 rotation is the corresponding matrix weighted sum of rotated derivative multipliers. Source: Breakdown.Freq.Internal.BilinRotate.derivOp_rot in Breakdown.FreqTr.BilinRotate, line 218. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L218).

**Rotate the recovered derivatives.** Recovered derivatives of a rotated state obey the almost everywhere matrix transformation rule. Source: Breakdown.Freq.Internal.BilinRotate.partialX_rot in Breakdown.FreqTr.BilinRotate, line 232. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L232).

**Rotate the smoothed derivative field.** The smoothed derivative of a rotated state is almost everywhere the pushforward of the original smoothed field. Source: Breakdown.Freq.Internal.BilinRotate.phiX_rot in Breakdown.FreqTr.BilinRotate, line 255. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L255).

**Orthogonality extracts a coordinate.** Pairing rotated coordinates with a rotated basis vector recovers the original coordinate. Source: Breakdown.Freq.Internal.BilinRotate.inner_unit_sum in Breakdown.FreqTr.BilinRotate, line 265. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L265).

**Rotation of the trilinear density.** Simultaneously rotating the vector inputs and derivative coordinates leaves the trilinear density unchanged. Source: Breakdown.Freq.Internal.BilinRotate.integrand_pt in Breakdown.FreqTr.BilinRotate, line 275. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L275).

**Rotate all trilinear inputs.** The trilinear pairing is unchanged by simultaneously rotating both states and pushing forward the test field. Source: Breakdown.Freq.Internal.BilinRotate.trilinear_rot in Breakdown.FreqTr.BilinRotate, line 284. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L284).

**The trilinear pairing respects null sets.** Almost everywhere equal third fields give equal trilinear pairings. Source: Breakdown.Freq.Internal.BilinRotate.trilinear_congr in Breakdown.FreqTr.BilinRotate, line 301. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L301).

**Rotate all interaction form inputs.** At positive time the interaction form is invariant when all three states are rotated together. Source: Breakdown.Freq.Internal.BilinRotate.bilinForm_rot in Breakdown.FreqTr.BilinRotate, line 308. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L308).

**Source namespace:** Breakdown.Freq.

**Prove bilinear rotation covariance.** The theorem discharges rotation covariance of the bilinear interaction from the stated realization interfaces. Source: Breakdown.Freq.bilinRotate in Breakdown.FreqTr.BilinRotate, line 318. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinRotate.lean#L318).

### Breakdown.FreqTr.BilinShift

Composing heat with the bilinear interaction advances its positive time parameter by the heat time.

**Source namespace:** Breakdown.Freq.Internal.BilinShift.

**Read a bounded scalar multiplier.** A bounded continuous scalar multiplier acts almost everywhere by scalar multiplication of the L2 representative. Source: Breakdown.Freq.Internal.BilinShift.scalar_ae in Breakdown.FreqTr.BilinShift, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L12).

**The heat factor is bounded by one.** The absolute heat factor is at most one. Source: Breakdown.Freq.Internal.BilinShift.heatFactor_abs_le in Breakdown.FreqTr.BilinShift, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L31).

**Bound the derivative heat factor.** At positive time the absolute derivative heat factor is at most one plus reciprocal time. Source: Breakdown.Freq.Internal.BilinShift.phiFactor_abs_le in Breakdown.FreqTr.BilinShift, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L37).

**Continuity of the heat factor.** The heat factor is continuous in frequency. Source: Breakdown.Freq.Internal.BilinShift.continuous_heatFactor in Breakdown.FreqTr.BilinShift, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L64).

**Continuity of the smoothing factor.** The derivative heat factor is continuous in frequency. Source: Breakdown.Freq.Internal.BilinShift.continuous_phiFactor in Breakdown.FreqTr.BilinShift, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L67).

**Combine heat and derivative smoothing.** Multiplication by a nonnegative time heat factor adds that time to the derivative smoothing time. Source: Breakdown.Freq.Internal.BilinShift.phiFactor_mul_heatFactor in Breakdown.FreqTr.BilinShift, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L70).

**Heat shifts derivative smoothing.** Applying heat before derivative smoothing adds their times under the stated time restrictions. Source: Breakdown.Freq.Internal.BilinShift.phiX_heatX in Breakdown.FreqTr.BilinShift, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L77).

**The chosen operator has its pairing.** At positive time the chosen bilinear interaction satisfies its pairing specification. Source: Breakdown.Freq.Internal.BilinShift.bilinX_spec in Breakdown.FreqTr.BilinShift, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L93).

**Source namespace:** Breakdown.Freq.

**Prove the bilinear time shift.** The theorem discharges the bilinear time shift interface from bilinear existence, heat and multiplier realization. Source: Breakdown.Freq.bilinShift in Breakdown.FreqTr.BilinShift, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinShift.lean#L102).

### Breakdown.FreqTr.BilinTestFormula

The interaction with an embedded solenoidal test is represented as projected heat of symmetrised test advection.

**Source namespace:** Breakdown.Freq.Internal.BilinTestFormula.

**The Lp conversion keeps its field.** For an Lp field, the total conversion agrees almost everywhere with the original field. Source: Breakdown.Freq.Internal.BilinTestFormula.toLpOrZero_ae in Breakdown.FreqTr.BilinTestFormula, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L12).

**Test fields belong to every Lp space.** A smooth compactly supported test field belongs to every Lp space. Source: Breakdown.Freq.Internal.BilinTestFormula.test_memLp in Breakdown.FreqTr.BilinTestFormula, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L18).

**Velocity meets its specification.** Existence of a velocity recovery operator makes the chosen velocity satisfy the test field recovery specification. Source: Breakdown.Freq.Internal.BilinTestFormula.velocity_spec in Breakdown.FreqTr.BilinTestFormula, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L21).

**Recover an embedded test velocity.** The velocity of an embedded test field equals that test field almost everywhere. Source: Breakdown.Freq.Internal.BilinTestFormula.velocity_test in Breakdown.FreqTr.BilinTestFormula, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L27).

**The bilinear operator is specified.** At positive time the chosen interaction satisfies the required bilinear pairing. Source: Breakdown.Freq.Internal.BilinTestFormula.bilinX_spec in Breakdown.FreqTr.BilinTestFormula, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L32).

**Read the pointwise multiplier action.** A measurable uniformly bounded multiplier acts almost everywhere by its pointwise linear map. Source: Breakdown.Freq.Internal.BilinTestFormula.fieldOp_id_ae in Breakdown.FreqTr.BilinTestFormula, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L38).

**The multiplication map acts by scalars.** The complex multiplication operator applies the scalar to the vector. Source: Breakdown.Freq.Internal.BilinTestFormula.cmul_apply in Breakdown.FreqTr.BilinTestFormula, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L45).

**The scalar bounds multiplication norm.** The real operator norm of complex multiplication is at most the scalar norm. Source: Breakdown.Freq.Internal.BilinTestFormula.norm_cmul_le in Breakdown.FreqTr.BilinTestFormula, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L47).

**Continuity in the complex scalar.** The multiplication operator depends continuously on its complex scalar. Source: Breakdown.Freq.Internal.BilinTestFormula.continuous_cmul in Breakdown.FreqTr.BilinTestFormula, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L50).

**Read a bounded complex symbol.** A measurable complex symbol of norm at most one gives the expected pointwise L2 multiplier almost everywhere. Source: Breakdown.Freq.Internal.BilinTestFormula.symbol_ae in Breakdown.FreqTr.BilinTestFormula, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L58).

**Bound a derivative symbol.** Each derivative symbol has norm at most one. Source: Breakdown.Freq.Internal.BilinTestFormula.norm_derivSymbol_le in Breakdown.FreqTr.BilinTestFormula, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L66).

**A derivative symbol is measurable.** Each derivative symbol is measurable. Source: Breakdown.Freq.Internal.BilinTestFormula.measurable_derivSymbol in Breakdown.FreqTr.BilinTestFormula, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L71).

**The sign of the derivative symbol.** The gradient embedding symbol is the negative of the derivative recovery symbol. Source: Breakdown.Freq.Internal.BilinTestFormula.gradSymbol_eq in Breakdown.FreqTr.BilinTestFormula, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L75).

**The zero field embeds as zero.** The Fourier gradient representation of the zero field is zero. Source: Breakdown.Freq.Internal.BilinTestFormula.ofGrad_zero in Breakdown.FreqTr.BilinTestFormula, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L77).

**A test gradient lies in state space.** The gradient representation of a test field lies in the solenoidal symbol subspace. Source: Breakdown.Freq.Internal.BilinTestFormula.ofGrad_mem_of_test in Breakdown.FreqTr.BilinTestFormula, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L88).

**Test derivatives belong to every Lp.** Every coordinate derivative of a test field belongs to every Lp space. Source: Breakdown.Freq.Internal.BilinTestFormula.partialField_memLp in Breakdown.FreqTr.BilinTestFormula, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L103).

**Real parts undo complexification.** Taking real vector parts after complexification recovers the original real vector. Source: Breakdown.Freq.Internal.BilinTestFormula.realVec_complexifyVec in Breakdown.FreqTr.BilinTestFormula, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L111).

**Transform a test field derivative.** The transformed coordinate derivative of a test field equals two pi times the imaginary frequency coordinate times its transform almost everywhere. Source: Breakdown.Freq.Internal.BilinTestFormula.gradHat_ae in Breakdown.FreqTr.BilinTestFormula, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L116).

**Recover the test field derivative.** The derivative recovered from an embedded test field equals its classical coordinate derivative almost everywhere. Source: Breakdown.Freq.Internal.BilinTestFormula.partial_test in Breakdown.FreqTr.BilinTestFormula, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L142).

**The real and complex vector pairing.** Pairing a complexified real vector with a complex vector is the real pairing with the complex vector's real part. Source: Breakdown.Freq.Internal.BilinTestFormula.inner_complexifyVec in Breakdown.FreqTr.BilinTestFormula, line 196. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L196).

**Complexification and real parts.** The L2 complexification and real part maps are adjoint for the real inner product. Source: Breakdown.Freq.Internal.BilinTestFormula.inner_complexify in Breakdown.FreqTr.BilinTestFormula, line 200. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L200).

**Real linear Fourier isometry.** The Fourier isometry is viewed over real scalars. Source: Breakdown.Freq.Internal.BilinTestFormula.freqTrRealIsometry in Breakdown.FreqTr.BilinTestFormula, line 211. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L211).

**The Fourier and inverse pairing.** The real inner product with a Fourier transformed input equals the inner product with an inverse transformed second input. Source: Breakdown.Freq.Internal.BilinTestFormula.inner_freqTrR in Breakdown.FreqTr.BilinTestFormula, line 214. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L214).

**The smoothing factor is nonnegative.** The derivative heat factor is nonnegative. Source: Breakdown.Freq.Internal.BilinTestFormula.phiFactor_nonneg in Breakdown.FreqTr.BilinTestFormula, line 218. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L218).

**A reciprocal time multiplier bound.** The pointwise smoothing multiplier norm is at most one plus reciprocal positive time. Source: Breakdown.Freq.Internal.BilinTestFormula.norm_phiFactor_smul_le in Breakdown.FreqTr.BilinTestFormula, line 221. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L221).

**The adjoint projected heat formula.** The projected heat pairing equals the physical field pairing against the smoothed derivative test. Source: Breakdown.Freq.Internal.BilinTestFormula.heatDivFree_inner in Breakdown.FreqTr.BilinTestFormula, line 243. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L243).

**The Hölder exponents six and three.** The exponent relation places the product of L6 and L3 functions in L2. Source: Breakdown.Freq.Internal.BilinTestFormula.lpProd_six_three in Breakdown.FreqTr.BilinTestFormula, line 264. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L264).

**Integrability of an L2 pairing.** The pointwise inner product of two L2 fields is integrable. Source: Breakdown.Freq.Internal.BilinTestFormula.integrable_inner_of_memLp in Breakdown.FreqTr.BilinTestFormula, line 270. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L270).

**Each coordinate stays in Lp.** Every coordinate of an Lp vector field belongs to the same Lp space. Source: Breakdown.Freq.Internal.BilinTestFormula.coord_memLp in Breakdown.FreqTr.BilinTestFormula, line 277. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L277).

**Combine the two trilinear terms.** The two trilinear terms with one embedded test field sum to the L2 pairing with the symmetrised advection field. Source: Breakdown.Freq.Internal.BilinTestFormula.trilinear_sum in Breakdown.FreqTr.BilinTestFormula, line 281. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L281).

**Source namespace:** Breakdown.Freq.

**Prove the test interaction formula.** The theorem identifies bilinear interaction against a test field through the projected heat and symmetrised advection formula. Source: Breakdown.Freq.bilinTestFormula in Breakdown.FreqTr.BilinTestFormula, line 321. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/BilinTestFormula.lean#L321).

### Breakdown.FreqTr.Dilation

The state dilation is realized as scaled frequency composition and proved to satisfy its norm, composition and heat identities.

**Source namespace:** Breakdown.Freq.Internal.Dilation.

**Choose an existing realization.** When a realization exists, the chosen field operator realizes the specified change of variables and multiplier. Source: Breakdown.Freq.Internal.Dilation.fieldOp_isRealizedBy_of_exists in Breakdown.FreqTr.Dilation, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L12).

**Zero when realization is unavailable.** If no bounded realization exists, the total field operator is zero. Source: Breakdown.Freq.Internal.Dilation.fieldOp_eq_zero_of_not in Breakdown.FreqTr.Dilation, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L18).

**The dilation formula on L2.** At positive parameter, L2 dilation rescales argument and amplitude by the inverse square root almost everywhere. Source: Breakdown.Freq.Internal.Dilation.dilL2_ae in Breakdown.FreqTr.Dilation, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L23).

**Bound the heat factor.** The absolute heat factor is at most one. Source: Breakdown.Freq.Internal.Dilation.heatFactor_le_one in Breakdown.FreqTr.Dilation, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L36).

**Read the L2 heat operator.** The heat operator multiplies the L2 representative by the heat factor almost everywhere. Source: Breakdown.Freq.Internal.Dilation.heatL2_ae in Breakdown.FreqTr.Dilation, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L41).

**Longitudinal projection ignores scale.** Multiplying a frequency by a nonzero real scalar leaves its longitudinal projection unchanged. Source: Breakdown.Freq.Internal.Dilation.longitudinal_smul in Breakdown.FreqTr.Dilation, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L60).

**Dilation preserves the symbol subspace.** Positive parameter L2 dilation preserves the solenoidal conjugate symmetric symbol subspace. Source: Breakdown.Freq.Internal.Dilation.dilL2_mem in Breakdown.FreqTr.Dilation, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L71).

**State dilation is restricted L2 dilation.** The state dilation agrees with the ambient L2 dilation at positive parameter. Source: Breakdown.Freq.Internal.Dilation.dilX_coe in Breakdown.FreqTr.Dilation, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L111).

**The quarter power dilation norm.** The L2 norm after dilation is the parameter's quarter power times the original norm. Source: Breakdown.Freq.Internal.Dilation.norm_dilL2 in Breakdown.FreqTr.Dilation, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L117).

**Heat and dilation scale together.** Scaling time and inversely scaling frequency by the square root leave the heat factor unchanged. Source: Breakdown.Freq.Internal.Dilation.heatFactor_dil in Breakdown.FreqTr.Dilation, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L143).

**Source namespace:** Breakdown.Freq.

**Prove the dilation algebra.** The theorem discharges the norm, identity, composition and heat compatibility laws for state dilation. Source: Breakdown.Freq.dilationAlgebra in Breakdown.FreqTr.Dilation, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Dilation.lean#L154).

### Breakdown.FreqTr.DilationCont

Continuity of amplitude-weighted frequency dilation is proved first for compact representatives and then extended to all L2 states.

**Source namespace:** Breakdown.Freq.Internal.DilationCont.

**Amplitude weighted frequency dilation.** The operator is the total fieldOp realization of multiplying by the scale while composing the frequency field with that same dilation. Source: Breakdown.Freq.Internal.DilationCont.scaleOp in Breakdown.FreqTr.DilationCont, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L14).

**A continuous dilation equivalence.** Nonzero scalar dilation is packaged as a continuous linear equivalence. Source: Breakdown.Freq.Internal.DilationCont.scaleEquiv in Breakdown.FreqTr.DilationCont, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L17).

**Read amplitude weighted dilation.** The weighted dilation operator acts almost everywhere by scale times the field at scaled frequency. Source: Breakdown.Freq.Internal.DilationCont.scaleOp_realized in Breakdown.FreqTr.DilationCont, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L20).

**The L2 norm under frequency dilation.** Positive frequency dilation scales the extended L2 norm by the square root of the reciprocal cubic Jacobian. Source: Breakdown.Freq.Internal.DilationCont.eLpNorm_comp_smul in Breakdown.FreqTr.DilationCont, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L28).

**Norm of amplitude weighted dilation.** The norm of the weighted dilation has the scale factor and square root Jacobian prescribed by the change of variables. Source: Breakdown.Freq.Internal.DilationCont.norm_scaleOp in Breakdown.FreqTr.DilationCont, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L41).

**Dilation continuity on compact fields.** The weighted dilation varies continuously near positive scale for continuous compactly supported representatives. Source: Breakdown.Freq.Internal.DilationCont.tendsto_scaleOp_of_compact in Breakdown.FreqTr.DilationCont, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L50).

**Dilation continuity on every L2 field.** The weighted dilation varies continuously near every positive scale for any L2 field. Source: Breakdown.Freq.Internal.DilationCont.tendsto_scaleOp in Breakdown.FreqTr.DilationCont, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L130).

**Source namespace:** Breakdown.Freq.

**Prove state dilation continuity.** The theorem transfers L2 dilation continuity to the abstract state dilation interface. Source: Breakdown.Freq.dilationContinuous in Breakdown.FreqTr.DilationCont, line 165. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/DilationCont.lean#L165).

### Breakdown.FreqTr.EmbedDilate

Scaling of Fourier gradients connects physical dilation of decay fields with the chosen state dilation.

**Source namespace:** Breakdown.Freq.Internal.EmbedDilate.

**Compose a symbol with dilation.** The L2 scaling operator is the total fieldOp realization of composition with scalar frequency dilation. Source: Breakdown.Freq.Internal.EmbedDilate.scaleOp in Breakdown.FreqTr.EmbedDilate, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L12).

**The scalar dilation equivalence.** A nonzero real scalar induces a continuous linear equivalence of space. Source: Breakdown.Freq.Internal.EmbedDilate.scaleEquiv in Breakdown.FreqTr.EmbedDilate, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L15).

**The dilation equivalence as a function.** The underlying function of the dilation equivalence is scalar multiplication. Source: Breakdown.Freq.Internal.EmbedDilate.scaleEquiv_coe in Breakdown.FreqTr.EmbedDilate, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L18).

**The L2 scaling representative.** The frequency scaling operator equals composition with the nonzero dilation almost everywhere. Source: Breakdown.Freq.Internal.EmbedDilate.scaleOp_ae in Breakdown.FreqTr.EmbedDilate, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L20).

**Dilation transports null set equality.** Almost everywhere equality is preserved by composition with nonzero scalar dilation. Source: Breakdown.Freq.Internal.EmbedDilate.ae_comp_smul in Breakdown.FreqTr.EmbedDilate, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L27).

**Bound the complex multiplication map.** The multiplication operator norm is at most the complex scalar norm. Source: Breakdown.Freq.Internal.EmbedDilate.norm_cmul_le in Breakdown.FreqTr.EmbedDilate, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L31).

**Continuity of multiplication operators.** Complex scalar multiplication operators depend continuously on their scalar. Source: Breakdown.Freq.Internal.EmbedDilate.continuous_cmul in Breakdown.FreqTr.EmbedDilate, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L35).

**The embedding symbol is bounded.** The gradient embedding symbol has norm at most one. Source: Breakdown.Freq.Internal.EmbedDilate.gradSymbol_norm_le in Breakdown.FreqTr.EmbedDilate, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L40).

**Measurability of the embedding symbol.** The gradient embedding symbol is measurable. Source: Breakdown.Freq.Internal.EmbedDilate.measurable_gradSymbol in Breakdown.FreqTr.EmbedDilate, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L45).

**The embedding symbol has degree zero.** Positive frequency dilation leaves the gradient embedding symbol unchanged. Source: Breakdown.Freq.Internal.EmbedDilate.gradSymbol_smul in Breakdown.FreqTr.EmbedDilate, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L48).

**Fourier transform of a dilated field.** A nonzero physical dilation becomes inverse frequency dilation with the absolute reciprocal cubic Jacobian. Source: Breakdown.Freq.Internal.EmbedDilate.freqTr_comp_smul in Breakdown.FreqTr.EmbedDilate, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L56).

**Dilate the L2 Fourier transform.** The L2 Fourier transform obeys the same inverse dilation and absolute reciprocal cubic Jacobian rule. Source: Breakdown.Freq.Internal.EmbedDilate.freqTr_scaleOp in Breakdown.FreqTr.EmbedDilate, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L74).

**Differentiate a scaled velocity field.** The derivative of scale times the field at the scaled point is scale squared times the original derivative there. Source: Breakdown.Freq.Internal.EmbedDilate.hasFDerivAt_scaled in Breakdown.FreqTr.EmbedDilate, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L100).

**Decay bounds survive positive scaling.** The stated velocity and derivative radial decay bounds persist after positive dilation with a common enlarged constant. Source: Breakdown.Freq.Internal.EmbedDilate.scaled_bound in Breakdown.FreqTr.EmbedDilate, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L110).

**Scaled decay fields remain decay fields.** Positive simultaneous amplitude and spatial scaling preserves the decay field conditions. Source: Breakdown.Freq.Internal.EmbedDilate.isDecayField_scaled in Breakdown.FreqTr.EmbedDilate, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L125).

**Physical dilation preserves decay.** The physical dilation of a decay field is again a decay field. Source: Breakdown.Freq.Internal.EmbedDilate.isDecayField_dilate in Breakdown.FreqTr.EmbedDilate, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L151).

**Differentiate physical dilation.** A coordinate derivative of the dilated field is the parameter times the original derivative at the square root scaled point. Source: Breakdown.Freq.Internal.EmbedDilate.partialField_dilate in Breakdown.FreqTr.EmbedDilate, line 155. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L155).

**Decay derivatives lie in L2.** Every coordinate derivative of a decay field is square integrable. Source: Breakdown.Freq.Internal.EmbedDilate.memLp_partialField in Breakdown.FreqTr.EmbedDilate, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L163).

**Complexify a dilated derivative.** The complex L2 class of a dilated coordinate derivative equals the corresponding scaled composition of the original class. Source: Breakdown.Freq.Internal.EmbedDilate.complexify_dilate in Breakdown.FreqTr.EmbedDilate, line 182. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L182).

**Dilate the transformed gradient.** The transformed gradient of a dilated field has inverse square root frequency and amplitude scaling. Source: Breakdown.Freq.Internal.EmbedDilate.gradHat_dilate in Breakdown.FreqTr.EmbedDilate, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L201).

**Embedding symbols commute with dilation.** The gradient embedding multiplier commutes with positive frequency dilation. Source: Breakdown.Freq.Internal.EmbedDilate.mult_scaleOp in Breakdown.FreqTr.EmbedDilate, line 215. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L215).

**Separate dilation amplitude and argument.** The L2 dilation equals inverse square root amplitude times inverse square root frequency composition. Source: Breakdown.Freq.Internal.EmbedDilate.dilL2_eq in Breakdown.FreqTr.EmbedDilate, line 231. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L231).

**The gradient embedding respects dilation.** Embedding the gradient of a physically dilated decay field equals dilating its gradient representation in L2. Source: Breakdown.Freq.Internal.EmbedDilate.ofGrad_dilate in Breakdown.FreqTr.EmbedDilate, line 245. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedDilate.lean#L245).

### Breakdown.FreqTr.EmbedMem

Fourier gradient compatibility, conjugate symmetry and zero divergence place each decay field embedding in the constrained symbol subspace.

**Source namespace:** Breakdown.Freq.Internal.EmbedMem.

**Control complex multiplication norm.** The operator norm of complex multiplication is at most the scalar norm. Source: Breakdown.Freq.Internal.EmbedMem.norm_cmul_le in Breakdown.FreqTr.EmbedMem, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L12).

**Continuous complex multiplication maps.** The multiplication operator varies continuously with its complex scalar. Source: Breakdown.Freq.Internal.EmbedMem.continuous_cmul in Breakdown.FreqTr.EmbedMem, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L17).

**The gradient symbol is measurable.** Each gradient embedding symbol is measurable. Source: Breakdown.Freq.Internal.EmbedMem.measurable_gradSymbol in Breakdown.FreqTr.EmbedMem, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L22).

**The gradient symbol is contractive.** Each gradient embedding symbol has norm at most one. Source: Breakdown.Freq.Internal.EmbedMem.norm_gradSymbol_le in Breakdown.FreqTr.EmbedMem, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L26).

**Symmetry of the gradient symbol.** Conjugating the gradient symbol at the negated frequency returns its original value. Source: Breakdown.Freq.Internal.EmbedMem.star_gradSymbol_neg in Breakdown.FreqTr.EmbedMem, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L35).

**Read the gradient multiplier.** The gradient multiplier acts almost everywhere by multiplication by its scalar symbol. Source: Breakdown.Freq.Internal.EmbedMem.gradOp_ae in Breakdown.FreqTr.EmbedMem, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L38).

**Read reflected conjugation.** The reflected conjugation operator takes the conjugate at the negative frequency almost everywhere. Source: Breakdown.Freq.Internal.EmbedMem.reflConj_ae in Breakdown.FreqTr.EmbedMem, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L45).

**Reflection preserves almost equality.** Frequency negation preserves almost everywhere equality. Source: Breakdown.Freq.Internal.EmbedMem.ae_comp_neg in Breakdown.FreqTr.EmbedMem, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L50).

**Norm of the complex frequency.** The complex frequency vector has the same norm as the real frequency. Source: Breakdown.Freq.Internal.EmbedMem.norm_freqVec in Breakdown.FreqTr.EmbedMem, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L54).

**The longitudinal projection is bounded.** The longitudinal projection has operator norm at most one. Source: Breakdown.Freq.Internal.EmbedMem.norm_longitudinal_le in Breakdown.FreqTr.EmbedMem, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L57).

**Measurability of the longitudinal map.** The longitudinal projection is almost everywhere strongly measurable as an operator valued map. Source: Breakdown.Freq.Internal.EmbedMem.aesm_longitudinal in Breakdown.FreqTr.EmbedMem, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L72).

**Read the longitudinal operator.** The L2 longitudinal operator agrees almost everywhere with its pointwise projection. Source: Breakdown.Freq.Internal.EmbedMem.longitudinal_ae in Breakdown.FreqTr.EmbedMem, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L83).

**Postcompose before taking an L2 class.** Applying a complex linear map to a Schwartz function commutes with forming its L2 class. Source: Breakdown.Freq.Internal.EmbedMem.compLpL_toLp in Breakdown.FreqTr.EmbedMem, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L93).

**Fourier transform under value maps.** A complex continuous linear map commutes with the Schwartz Fourier transform. Source: Breakdown.Freq.Internal.EmbedMem.freqTr_postcomp in Breakdown.FreqTr.EmbedMem, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L100).

**A linear map commutes with L2 transform.** A fixed complex linear value map commutes with the L2 Fourier transform. Source: Breakdown.Freq.Internal.EmbedMem.freqTrL2_compLpL in Breakdown.FreqTr.EmbedMem, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L112).

**Complexify compatible value maps.** Compatible real and complex pointwise maps commute with complexification on L2. Source: Breakdown.Freq.Internal.EmbedMem.complexify_compLpL in Breakdown.FreqTr.EmbedMem, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L130).

**The decay gradient is square integrable.** Each coordinate derivative of a decay field belongs to L2. Source: Breakdown.Freq.Internal.EmbedMem.memLp_partialField in Breakdown.FreqTr.EmbedMem, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L143).

**Place a real coordinate on one axis.** The real coordinate map extracts the chosen coordinate and places it in the first basis direction. Source: Breakdown.Freq.Internal.EmbedMem.coordReal in Breakdown.FreqTr.EmbedMem, line 163. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L163).

**Place a complex coordinate on one axis.** The complex coordinate map extracts the chosen coordinate and places it in the first basis direction. Source: Breakdown.Freq.Internal.EmbedMem.coordCplx in Breakdown.FreqTr.EmbedMem, line 166. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L166).

**Evaluate the real coordinate map.** The real coordinate map gives the chosen scalar coordinate times the first unit vector. Source: Breakdown.Freq.Internal.EmbedMem.coordReal_apply in Breakdown.FreqTr.EmbedMem, line 169. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L169).

**Evaluate the complex coordinate map.** The complex coordinate map gives the chosen scalar coordinate times the first complex unit vector. Source: Breakdown.Freq.Internal.EmbedMem.coordCplx_apply in Breakdown.FreqTr.EmbedMem, line 171. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L171).

**Complexification respects coordinates.** Complexifying the real coordinate map equals applying its complex counterpart after complexification. Source: Breakdown.Freq.Internal.EmbedMem.complexifyVec_coord in Breakdown.FreqTr.EmbedMem, line 173. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L173).

**The transformed divergence vanishes.** For a decay field, the sum of matching transformed derivative coordinates vanishes almost everywhere. Source: Breakdown.Freq.Internal.EmbedMem.div_ae in Breakdown.FreqTr.EmbedMem, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L179).

**The gradient multiplier is symmetric.** The gradient embedding multiplier preserves the reflected conjugation constraint. Source: Breakdown.Freq.Internal.EmbedMem.conjSym_grad in Breakdown.FreqTr.EmbedMem, line 223. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L223).

**Read the Fourier gradient representation.** The gradient representation is almost everywhere the sum of gradient symbols times the transformed partial fields. Source: Breakdown.Freq.Internal.EmbedMem.ofGrad_ae in Breakdown.FreqTr.EmbedMem, line 237. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L237).

**Expand the frequency pairing.** The complex inner product with the frequency vector is the sum of frequency coordinates times vector coordinates. Source: Breakdown.Freq.Internal.EmbedMem.inner_freqVec in Breakdown.FreqTr.EmbedMem, line 247. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L247).

**The gradient symbol is transverse.** The longitudinal projection of the gradient representation vanishes under gradient compatibility. Source: Breakdown.Freq.Internal.EmbedMem.long_ofGrad in Breakdown.FreqTr.EmbedMem, line 251. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L251).

**Source namespace:** Breakdown.Freq.

**Prove membership in the state space.** The theorem proves the gradient embedding satisfies the symmetry and solenoidal constraints of the state space. Source: Breakdown.Freq.embedMem in Breakdown.FreqTr.EmbedMem, line 278. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedMem.lean#L278).

### Breakdown.FreqTr.EmbedNeZero

Vanishing of the gradient embedding forces a decay field to vanish, so a nonzero physical field has a nonzero state.

**Source namespace:** Breakdown.Freq.Internal.EmbedNeZero.

**A decaying constant is zero.** A constant vector bounded by a fixed inverse radial decay rate everywhere must be zero. Source: Breakdown.Freq.Internal.EmbedNeZero.eq_zero_of_decay in Breakdown.FreqTr.EmbedNeZero, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNeZero.lean#L12).

**A linear map vanishes on a basis.** A continuous linear map vanishing on all three coordinate unit vectors is zero. Source: Breakdown.Freq.Internal.EmbedNeZero.clm_eq_zero_of_units in Breakdown.FreqTr.EmbedNeZero, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNeZero.lean#L28).

**A square gradient majorant.** Second order radial decay of the derivative gives the stated fourth order majorant for the sum of squared coordinate derivative norms. Source: Breakdown.Freq.Internal.EmbedNeZero.sq_grad_bound in Breakdown.FreqTr.EmbedNeZero, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNeZero.lean#L37).

**Source namespace:** Breakdown.Freq.

**Nonzero fields have nonzero embeddings.** The gradient norm identity makes the embedding detect nonzero decay fields. Source: Breakdown.Freq.embedNeZero in Breakdown.FreqTr.EmbedNeZero, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNeZero.lean#L61).

### Breakdown.FreqTr.EmbedNegSsp

Fourier differentiation and compact support show that embedding a negative Laplacian gives the corresponding state Laplacian relation.

**Source namespace:** Breakdown.Freq.Internal.EmbedNegSsp.

**Coordinate differentiation.** The partial derivative operator differentiates a field in a coordinate unit vector direction. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd in Breakdown.FreqTr.EmbedNegSsp, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L16).

**Partial derivatives preserve smoothness.** A coordinate derivative of a smooth field is smooth. Source: Breakdown.Freq.Internal.EmbedNegSsp.contDiff_pd in Breakdown.FreqTr.EmbedNegSsp, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L18).

**Smooth fields are differentiable.** Every smooth field is differentiable. Source: Breakdown.Freq.Internal.EmbedNegSsp.differentiable_of_smooth in Breakdown.FreqTr.EmbedNegSsp, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L21).

**Differentiate a negative field.** Coordinate differentiation commutes with negation. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd_neg in Breakdown.FreqTr.EmbedNegSsp, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L24).

**Differentiate a finite sum.** Coordinate differentiation distributes over a finite sum of differentiable fields. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd_sum in Breakdown.FreqTr.EmbedNegSsp, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L28).

**Differentiate after a linear map.** A continuous linear value map commutes with coordinate differentiation of a differentiable field. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd_clm in Breakdown.FreqTr.EmbedNegSsp, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L35).

**Read an iterated partial derivative.** The iterated coordinate derivative equals the second Fréchet derivative evaluated on the two unit vectors. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd_pd in Breakdown.FreqTr.EmbedNegSsp, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L43).

**Mixed coordinate derivatives commute.** Two coordinate derivatives of a smooth field commute. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd_comm in Breakdown.FreqTr.EmbedNegSsp, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L51).

**Expand the componentwise Laplacian.** The sum of second partials is the sum of repeated coordinate derivatives. Source: Breakdown.Freq.Internal.EmbedNegSsp.sumSecondPartialsAt_eq in Breakdown.FreqTr.EmbedNegSsp, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L57).

**Expand the negative Laplacian.** The negative Laplacian is the negative sum of repeated coordinate derivatives of a smooth field. Source: Breakdown.Freq.Internal.EmbedNegSsp.negSsp_eq in Breakdown.FreqTr.EmbedNegSsp, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L62).

**Derivatives keep compact support.** A coordinate derivative of a compactly supported field has compact support. Source: Breakdown.Freq.Internal.EmbedNegSsp.hasCompactSupport_pd in Breakdown.FreqTr.EmbedNegSsp, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L71).

**Differentiate the zero field.** A coordinate derivative of the zero field is zero. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd_zero in Breakdown.FreqTr.EmbedNegSsp, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L75).

**Divergence as a coordinate sum.** The auxiliary divergence sums the matching coordinates of each partial derivative. Source: Breakdown.Freq.Internal.EmbedNegSsp.dv in Breakdown.FreqTr.EmbedNegSsp, line 80. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L80).

**Identify the coordinate divergence.** The coordinate sum definition agrees with the physical divergence operator. Source: Breakdown.Freq.Internal.EmbedNegSsp.divergenceAt_eq_dv in Breakdown.FreqTr.EmbedNegSsp, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L82).

**Divergence commutes with differentiation.** For a smooth field, coordinate differentiation commutes with divergence. Source: Breakdown.Freq.Internal.EmbedNegSsp.pd_dv in Breakdown.FreqTr.EmbedNegSsp, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L85).

**Divergence of a negative finite sum.** Divergence distributes over the negative sum of smooth fields. Source: Breakdown.Freq.Internal.EmbedNegSsp.dv_neg_sum in Breakdown.FreqTr.EmbedNegSsp, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L93).

**Test fields survive the Laplacian.** The negative Laplacian of a solenoidal test field is another solenoidal test field. Source: Breakdown.Freq.Internal.EmbedNegSsp.isTestField_negSsp in Breakdown.FreqTr.EmbedNegSsp, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L100).

**Test fields satisfy the decay conditions.** Every smooth compactly supported solenoidal test field is a decay field. Source: Breakdown.Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField in Breakdown.FreqTr.EmbedNegSsp, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L121).

**Fourier transform of a derivative.** Transforming a Schwartz coordinate derivative multiplies the transform by two pi times the imaginary frequency coordinate. Source: Breakdown.Freq.Internal.EmbedNegSsp.freqTr_pd_apply in Breakdown.FreqTr.EmbedNegSsp, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L148).

**Read the Schwartz partial derivative.** The Schwartz derivative of a complexified smooth field is the complexification of its coordinate derivative. Source: Breakdown.Freq.Internal.EmbedNegSsp.coe_lineDeriv_eq in Breakdown.FreqTr.EmbedNegSsp, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L156).

**Recover the real vector.** Real parts undo the inclusion of a real vector into complex space. Source: Breakdown.Freq.Internal.EmbedNegSsp.realVec_complexifyVec in Breakdown.FreqTr.EmbedNegSsp, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L163).

**Identify a complexified Schwartz class.** The complex L2 class of a real field represented by a Schwartz function is that Schwartz function's L2 class. Source: Breakdown.Freq.Internal.EmbedNegSsp.complexify_toLpOrZero in Breakdown.FreqTr.EmbedNegSsp, line 167. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L167).

**Transforming Schwartz Lp classes.** Taking the L2 Fourier transform of a Schwartz class gives the L2 class of its Schwartz transform. Source: Breakdown.Freq.Internal.EmbedNegSsp.freqTrR_toLp in Breakdown.FreqTr.EmbedNegSsp, line 183. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L183).

**Complex multiplication is norm bounded.** The complex multiplication operator norm is at most its scalar norm. Source: Breakdown.Freq.Internal.EmbedNegSsp.norm_cmul_le in Breakdown.FreqTr.EmbedNegSsp, line 186. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L186).

**Bound the gradient symbol.** The gradient embedding symbol has norm at most one. Source: Breakdown.Freq.Internal.EmbedNegSsp.norm_gradSymbol_le in Breakdown.FreqTr.EmbedNegSsp, line 189. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L189).

**The gradient multiplier representative.** The L2 gradient multiplier has the indicated pointwise representative almost everywhere. Source: Breakdown.Freq.Internal.EmbedNegSsp.gradOp_ae in Breakdown.FreqTr.EmbedNegSsp, line 194. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L194).

**Read a sum of three L2 fields.** The representative of a three term L2 sum is the pointwise sum almost everywhere. Source: Breakdown.Freq.Internal.EmbedNegSsp.coeFn_sum_three in Breakdown.FreqTr.EmbedNegSsp, line 211. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L211).

**Embed through Schwartz derivatives.** The gradient representation is the sum of gradient multipliers applied to the Fourier transforms of the Schwartz derivative representatives. Source: Breakdown.Freq.Internal.EmbedNegSsp.ofGrad_ae in Breakdown.FreqTr.EmbedNegSsp, line 217. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L217).

**The Laplacian scalar identity.** Summing the second derivative frequency factors gives the Laplacian factor times the remaining first derivative factor. Source: Breakdown.Freq.Internal.EmbedNegSsp.ssp_scalar in Breakdown.FreqTr.EmbedNegSsp, line 238. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L238).

**Embed the negative Laplacian.** The gradient representation of a negative test Laplacian is the Laplacian factor times the original representation almost everywhere. Source: Breakdown.Freq.Internal.EmbedNegSsp.ofGrad_negSsp_ae in Breakdown.FreqTr.EmbedNegSsp, line 248. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L248).

**Source namespace:** Breakdown.Freq.

**Prove Laplacian compatibility.** The theorem discharges compatibility between the physical negative Laplacian and the Fourier state Laplacian relation. Source: Breakdown.Freq.embedNegSsp in Breakdown.FreqTr.EmbedNegSsp, line 286. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNegSsp.lean#L286).

### Breakdown.FreqTr.EmbedNorm

Linearity and Plancherel identities identify the embedded state norm with the physical gradient square integral.

**Source namespace:** Breakdown.Freq.Internal.EmbedNorm.

**The valid branch of Lp conversion.** For an Lp input, the total conversion is exactly the Lp class constructed from its integrability proof. Source: Breakdown.Freq.Internal.EmbedNorm.toLpOrZero_eq in Breakdown.FreqTr.EmbedNorm, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L12).

**Decay derivatives belong to L2.** Each coordinate derivative of a decay field belongs to L2. Source: Breakdown.Freq.Internal.EmbedNorm.memLp_partialField in Breakdown.FreqTr.EmbedNorm, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L16).

**Add coordinate derivatives.** The coordinate derivative of a sum of decay fields is the sum of the coordinate derivatives. Source: Breakdown.Freq.Internal.EmbedNorm.partialField_add in Breakdown.FreqTr.EmbedNorm, line 44. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L44).

**Subtract coordinate derivatives.** The coordinate derivative of a difference of decay fields is the difference of the coordinate derivatives. Source: Breakdown.Freq.Internal.EmbedNorm.partialField_sub in Breakdown.FreqTr.EmbedNorm, line 51. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L51).

**Scale a coordinate derivative.** A constant real scalar commutes with coordinate differentiation. Source: Breakdown.Freq.Internal.EmbedNorm.partialField_smul in Breakdown.FreqTr.EmbedNorm, line 58. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L58).

**Add gradient embeddings.** The Fourier gradient representation is additive on decay fields. Source: Breakdown.Freq.Internal.EmbedNorm.ofGrad_add in Breakdown.FreqTr.EmbedNorm, line 64. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L64).

**Subtract gradient embeddings.** The Fourier gradient representation respects subtraction of decay fields. Source: Breakdown.Freq.Internal.EmbedNorm.ofGrad_sub in Breakdown.FreqTr.EmbedNorm, line 74. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L74).

**Scale a gradient embedding.** The Fourier gradient representation respects real scalar multiplication of a decay field. Source: Breakdown.Freq.Internal.EmbedNorm.ofGrad_smul in Breakdown.FreqTr.EmbedNorm, line 84. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L84).

**Read a valid state embedding.** When the gradient representation lies in the symbol subspace, the embedded state has exactly that ambient L2 value. Source: Breakdown.Freq.Internal.EmbedNorm.embedX_coe in Breakdown.FreqTr.EmbedNorm, line 93. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L93).

**Prove linearity of the embedding.** Membership of decay field gradients in the state space gives the embedding linearity interface. Source: Breakdown.Freq.Internal.EmbedNorm.embedLinear_of in Breakdown.FreqTr.EmbedNorm, line 97. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L97).

**The L2 square norm formula.** The squared L2 norm equals the integral of the squared representative norm. Source: Breakdown.Freq.Internal.EmbedNorm.norm_sq_Lp_eq in Breakdown.FreqTr.EmbedNorm, line 109. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L109).

**The compatible gradient square identity.** At nonzero frequency, compatibility of the gradient components identifies the squared embedded symbol norm with the sum of their squares. Source: Breakdown.Freq.Internal.EmbedNorm.norm_sq_sum_gradSymbol in Breakdown.FreqTr.EmbedNorm, line 116. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L116).

**Apply the complex multiplication map.** The multiplication operator applies its complex scalar to the vector. Source: Breakdown.Freq.Internal.EmbedNorm.cmul_apply in Breakdown.FreqTr.EmbedNorm, line 146. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L146).

**Bound the multiplication map.** The complex multiplication operator norm is at most the scalar norm. Source: Breakdown.Freq.Internal.EmbedNorm.norm_cmul_le in Breakdown.FreqTr.EmbedNorm, line 148. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L148).

**Subtract multiplication maps.** The difference of two complex multiplication operators is multiplication by the scalar difference. Source: Breakdown.Freq.Internal.EmbedNorm.cmul_sub in Breakdown.FreqTr.EmbedNorm, line 151. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L151).

**Continuity in the multiplying scalar.** The complex multiplication operator is continuous as a function of its scalar. Source: Breakdown.Freq.Internal.EmbedNorm.continuous_cmul in Breakdown.FreqTr.EmbedNorm, line 155. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L155).

**Gradient symbols are measurable.** Each gradient embedding symbol is measurable. Source: Breakdown.Freq.Internal.EmbedNorm.measurable_gradSymbol in Breakdown.FreqTr.EmbedNorm, line 160. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L160).

**The embedding symbol has unit bound.** The gradient embedding symbol has norm at most one. Source: Breakdown.Freq.Internal.EmbedNorm.norm_gradSymbol_le in Breakdown.FreqTr.EmbedNorm, line 164. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L164).

**The gradient operator acts pointwise.** The gradient multiplier acts almost everywhere by its scalar frequency symbol. Source: Breakdown.Freq.Internal.EmbedNorm.gradOp_ae in Breakdown.FreqTr.EmbedNorm, line 169. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L169).

**Expand the embedded gradient symbol.** The gradient representation is almost everywhere the sum of gradient symbols times transformed partial derivatives. Source: Breakdown.Freq.Internal.EmbedNorm.ofGrad_ae in Breakdown.FreqTr.EmbedNorm, line 180. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L180).

**Complexification preserves squared norm.** Complexification preserves the squared L2 norm of a real field. Source: Breakdown.Freq.Internal.EmbedNorm.norm_complexify_sq in Breakdown.FreqTr.EmbedNorm, line 195. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L195).

**The transformed partial square norm.** The squared norm of a transformed partial field equals the integral of the corresponding classical derivative square. Source: Breakdown.Freq.Internal.EmbedNorm.norm_gradHat_sq in Breakdown.FreqTr.EmbedNorm, line 203. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L203).

**Prove the gradient norm identity.** The theorem derives the physical gradient norm formula from multiplier realization, gradient compatibility and state space membership. Source: Breakdown.Freq.Internal.EmbedNorm.embedNorm_of in Breakdown.FreqTr.EmbedNorm, line 213. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L213).

**Source namespace:** Breakdown.Freq.

**Prove norm and linearity together.** The theorem supplies both the gradient norm identity and linearity of the state embedding. Source: Breakdown.Freq.embedNormLinear in Breakdown.FreqTr.EmbedNorm, line 240. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedNorm.lean#L240).

### Breakdown.FreqTr.EmbedRot

Fourier covariance under orthogonal coordinate changes proves that the physical embedding respects spatial rotation.

**Source namespace:** Breakdown.Freq.Internal.EmbedRot.

**Rotate arguments and map values on L2.** The construction composes an L2 field with an inverse spatial isometry and applies a fixed complex linear map to its values. Source: Breakdown.Freq.Internal.EmbedRot.rotComp in Breakdown.FreqTr.EmbedRot, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L14).

**Read the rotated value composition.** The composed L2 field agrees almost everywhere with the fixed value map applied at the inverse rotated point. Source: Breakdown.Freq.Internal.EmbedRot.coeFn_rotComp in Breakdown.FreqTr.EmbedRot, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L17).

**Continuity of rotated value composition.** The rotation and value map construction is continuous on L2. Source: Breakdown.Freq.Internal.EmbedRot.continuous_rotComp in Breakdown.FreqTr.EmbedRot, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L25).

**Fourier rotation of Schwartz fields.** Fourier transformation commutes with inverse orthogonal argument composition and a fixed complex linear value map on Schwartz fields. Source: Breakdown.Freq.Internal.EmbedRot.freqTr_rapid_rot in Breakdown.FreqTr.EmbedRot, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L31).

**Fourier transform of rotated L2 fields.** The L2 Fourier transform commutes with the rotation and fixed value map construction. Source: Breakdown.Freq.Internal.EmbedRot.freqTr_rotComp in Breakdown.FreqTr.EmbedRot, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L49).

**The complex linear spatial rotation.** The matrix of a real spatial isometry is packaged as a continuous complex linear map. Source: Breakdown.Freq.Internal.EmbedRot.rotCplx in Breakdown.FreqTr.EmbedRot, line 87. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L87).

**Identify the complex rotation map.** The complex linear rotation agrees with the original real linear complex vector rotation. Source: Breakdown.Freq.Internal.EmbedRot.rotCplx_apply in Breakdown.FreqTr.EmbedRot, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L94).

**Expand a vector on the unit basis.** Every spatial vector is the sum of its coordinate multiples of the three unit vectors. Source: Breakdown.Freq.Internal.EmbedRot.vec_decomp in Breakdown.FreqTr.EmbedRot, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L96).

**Complexification commutes with rotation.** Including a rotated real vector into complex space equals complex rotation of its inclusion. Source: Breakdown.Freq.Internal.EmbedRot.complexifyVec_rot in Breakdown.FreqTr.EmbedRot, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L100).

**Directional decay derivatives lie in L2.** Every fixed directional derivative of a decay field is square integrable. Source: Breakdown.Freq.Internal.EmbedRot.memLp_dir in Breakdown.FreqTr.EmbedRot, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L106).

**Differentiate a pushed forward field.** A coordinate derivative of a smooth pushforward is the matrix weighted sum of rotated original derivatives. Source: Breakdown.Freq.Internal.EmbedRot.partialField_push in Breakdown.FreqTr.EmbedRot, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L140).

**Rotate the gradient embedding symbols.** The matrix combination of gradient symbols equals the corresponding symbol at inverse rotated frequency. Source: Breakdown.Freq.Internal.EmbedRot.symbol_rot in Breakdown.FreqTr.EmbedRot, line 157. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L157).

**Use the L2 branch of conversion.** For a square integrable field, the total conversion equals its ordinary L2 class. Source: Breakdown.Freq.Internal.EmbedRot.toLpOrZero_of in Breakdown.FreqTr.EmbedRot, line 170. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L170).

**Read a complexified L2 field.** The complex L2 class agrees almost everywhere with pointwise complexification of the real field. Source: Breakdown.Freq.Internal.EmbedRot.ae_complexify in Breakdown.FreqTr.EmbedRot, line 174. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L174).

**A three term L2 representative.** A sum of three L2 fields has the pointwise sum as its representative almost everywhere. Source: Breakdown.Freq.Internal.EmbedRot.coeFn_sum3 in Breakdown.FreqTr.EmbedRot, line 183. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L183).

**Multiplication is a scalar identity map.** The complex multiplication map is a complex scalar multiple of the identity operator. Source: Breakdown.Freq.Internal.EmbedRot.cmul_eq in Breakdown.FreqTr.EmbedRot, line 189. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L189).

**The embedding multiplier is measurable.** The gradient embedding symbol is measurable. Source: Breakdown.Freq.Internal.EmbedRot.measurable_gradSymbol in Breakdown.FreqTr.EmbedRot, line 193. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L193).

**The embedding symbol norm bound.** The gradient embedding symbol has norm at most one. Source: Breakdown.Freq.Internal.EmbedRot.norm_gradSymbol_le in Breakdown.FreqTr.EmbedRot, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L197).

**Unit scalars give contractive maps.** A complex scalar of norm at most one gives a multiplication operator of norm at most one. Source: Breakdown.Freq.Internal.EmbedRot.norm_cmul_le in Breakdown.FreqTr.EmbedRot, line 203. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L203).

**Read the gradient embedding sum.** The gradient representation has the pointwise sum of the three transformed derivative terms almost everywhere. Source: Breakdown.Freq.Internal.EmbedRot.ofGrad_ae in Breakdown.FreqTr.EmbedRot, line 209. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L209).

**Pushed forward derivatives lie in L2.** The coordinate derivatives of a rotated decay field are square integrable. Source: Breakdown.Freq.Internal.EmbedRot.memLp_push in Breakdown.FreqTr.EmbedRot, line 230. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L230).

**Complexify the rotated derivative sum.** Complexifying a pushed forward derivative gives the matrix weighted sum of the rotated complex derivative classes. Source: Breakdown.Freq.Internal.EmbedRot.complexify_push in Breakdown.FreqTr.EmbedRot, line 243. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L243).

**The real and complex Fourier maps agree.** The real linear Fourier map and the complex Fourier isometry have the same value on every L2 field. Source: Breakdown.Freq.Internal.EmbedRot.freqTrR_apply in Breakdown.FreqTr.EmbedRot, line 267. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L267).

**Transform a pushed forward derivative.** The transformed derivative of a pushforward is the matrix weighted sum of rotated transformed derivatives. Source: Breakdown.Freq.Internal.EmbedRot.gradHat_push in Breakdown.FreqTr.EmbedRot, line 269. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L269).

**Rotation realizes its pointwise formula.** The L2 rotation realizes inverse spatial composition together with complex vector rotation. Source: Breakdown.Freq.Internal.EmbedRot.rotL2_ae in Breakdown.FreqTr.EmbedRot, line 278. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L278).

**Rotate the gradient representation.** Rotating the gradient representation equals the representation of the pushed forward decay field. Source: Breakdown.Freq.Internal.EmbedRot.rotL2_ofGrad in Breakdown.FreqTr.EmbedRot, line 283. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L283).

**Source namespace:** Breakdown.Freq.

**Prove embedding rotation covariance.** The theorem discharges commutation of the state embedding with physical rotations. Source: Breakdown.Freq.embedRot in Breakdown.FreqTr.EmbedRot, line 322. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/EmbedRot.lean#L322).

### Breakdown.FreqTr.FieldOp

Bounded measurable multipliers with invertible linear coordinate changes are constructed on L2 and identified with their total chosen realization.

**Source namespace:** Breakdown.Freq.Internal.FieldOp.

**A nonzero coordinate determinant.** A continuous linear equivalence of space has nonzero determinant. Source: Breakdown.Freq.Internal.FieldOp.det_ne_zero in Breakdown.FreqTr.FieldOp, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L12).

**The inverse Jacobian factor.** The measure factor is the nonnegative extended real absolute value of the inverse determinant. Source: Breakdown.Freq.Internal.FieldOp.detFactor in Breakdown.FreqTr.FieldOp, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L15).

**The Jacobian factor is finite.** The inverse determinant measure factor is finite. Source: Breakdown.Freq.Internal.FieldOp.detFactor_ne_top in Breakdown.FreqTr.FieldOp, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L17).

**The linear change of variables measure.** The pushforward of volume by the linear equivalence is volume multiplied by its inverse absolute determinant factor. Source: Breakdown.Freq.Internal.FieldOp.map_eq in Breakdown.FreqTr.FieldOp, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L19).

**Linear equivalences preserve null sets.** A continuous linear equivalence is quasi measure preserving for volume. Source: Breakdown.Freq.Internal.FieldOp.qmp in Breakdown.FreqTr.FieldOp, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L22).

**The L2 norm change of variables.** Composition with a linear equivalence multiplies the extended L2 norm by the square root of its inverse Jacobian factor. Source: Breakdown.Freq.Internal.FieldOp.eLpNorm_comp in Breakdown.FreqTr.FieldOp, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L25).

**Coordinate changes preserve L2.** Composition with a linear equivalence preserves square integrability. Source: Breakdown.Freq.Internal.FieldOp.memLp_comp in Breakdown.FreqTr.FieldOp, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L30).

**The pointwise transformed multiplier.** The function applies a frequency dependent linear map after composing the input representative with the coordinate change. Source: Breakdown.Freq.Internal.FieldOp.applyFun in Breakdown.FreqTr.FieldOp, line 35. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L35).

**Measurability of the transformed field.** The transformed multiplier field is almost everywhere strongly measurable when its operator coefficient is measurable. Source: Breakdown.Freq.Internal.FieldOp.aesm_apply in Breakdown.FreqTr.FieldOp, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L38).

**Bound the transformed field pointwise.** The pointwise transformed field norm is bounded by the coefficient bound times the norm of the composed input. Source: Breakdown.Freq.Internal.FieldOp.norm_apply_le in Breakdown.FreqTr.FieldOp, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L44).

**The transformed field belongs to L2.** A uniformly bounded measurable multiplier after a linear equivalence maps L2 fields to L2 fields. Source: Breakdown.Freq.Internal.FieldOp.memLp_apply in Breakdown.FreqTr.FieldOp, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L49).

**Coordinate changes preserve a.e..** A continuous linear equivalence preserves almost everywhere equality under composition. Source: Breakdown.Freq.Internal.FieldOp.comp_ae in Breakdown.FreqTr.FieldOp, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L55).

**The induced linear L2 operator.** The construction lifts the transformed multiplier to a real linear operator on L2 classes. Source: Breakdown.Freq.Internal.FieldOp.opLin in Breakdown.FreqTr.FieldOp, line 59. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L59).

**Bound the induced L2 operator.** The induced linear operator is bounded by the coefficient bound times the square root Jacobian factor. Source: Breakdown.Freq.Internal.FieldOp.norm_opLin_le in Breakdown.FreqTr.FieldOp, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L75).

**The induced bounded L2 operator.** The established norm estimate packages the transformed multiplier as a continuous real linear map. Source: Breakdown.Freq.Internal.FieldOp.op in Breakdown.FreqTr.FieldOp, line 93. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L93).

**The operator realizes its formula.** The bounded transformed multiplier operator satisfies its almost everywhere realization specification. Source: Breakdown.Freq.Internal.FieldOp.op_spec in Breakdown.FreqTr.FieldOp, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L97).

**Source namespace:** Breakdown.Freq.

**Prove multiplier realization.** The theorem discharges the realization interface for measurable bounded multipliers with invertible linear coordinate changes. Source: Breakdown.Freq.fieldOpRealized in Breakdown.FreqTr.FieldOp, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L103).

**Uniqueness of a realized operator.** Two continuous L2 operators with the same almost everywhere realization formula are equal. Source: Breakdown.Freq.isRealizedBy_unique in Breakdown.FreqTr.FieldOp, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L109).

**Identify the chosen field operator.** Any operator satisfying the realization specification equals the chosen field operator. Source: Breakdown.Freq.fieldOp_eq_of_isRealizedBy in Breakdown.FreqTr.FieldOp, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L114).

**Realize a bounded transformed multiplier.** The chosen field operator realizes every bounded measurable multiplier whose coordinate map is a continuous linear equivalence. Source: Breakdown.Freq.isRealizedBy_fieldOp in Breakdown.FreqTr.FieldOp, line 120. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L120).

**Read the chosen operator representative.** The chosen operator equals its transformed pointwise multiplier formula almost everywhere under the stated bounds. Source: Breakdown.Freq.fieldOp_ae in Breakdown.FreqTr.FieldOp, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L126).

**Realize a pointwise multiplier.** A bounded measurable pointwise multiplier is realized by the field operator with identity coordinates. Source: Breakdown.Freq.isRealizedBy_fieldOp_id in Breakdown.FreqTr.FieldOp, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L132).

**Source namespace:** Breakdown.Freq.Internal.FieldOp.

**Read the square root Jacobian factor.** The real value of the half power determinant factor equals the square root of the absolute inverse determinant. Source: Breakdown.Freq.Internal.FieldOp.detFactor_rpow_toReal in Breakdown.FreqTr.FieldOp, line 138. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L138).

**Source namespace:** Breakdown.Freq.

**Bound a transformed multiplier output.** The output L2 norm is bounded by the coefficient bound times square root inverse Jacobian times the input norm. Source: Breakdown.Freq.norm_fieldOp_apply_le in Breakdown.FreqTr.FieldOp, line 145. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L145).

**Bound a transformed multiplier operator.** The operator norm is bounded by the coefficient bound times the square root absolute inverse determinant. Source: Breakdown.Freq.norm_fieldOp_le in Breakdown.FreqTr.FieldOp, line 153. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L153).

**Bound a pointwise multiplier output.** For identity coordinates, the coefficient bound times the input norm bounds the output norm. Source: Breakdown.Freq.norm_fieldOp_id_apply_le in Breakdown.FreqTr.FieldOp, line 161. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L161).

**Bound a pointwise multiplier operator.** For identity coordinates, the multiplier operator norm is at most the coefficient bound. Source: Breakdown.Freq.norm_fieldOp_id_le in Breakdown.FreqTr.FieldOp, line 170. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L170).

**Compose realization formulas.** Realized operators compose with the composed coordinate map and the appropriately transported pointwise coefficient maps. Source: Breakdown.Freq.isRealizedBy_comp in Breakdown.FreqTr.FieldOp, line 175. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L175).

**The coordinate map keeps null sets.** Every continuous linear equivalence is quasi measure preserving for volume. Source: Breakdown.Freq.quasiMeasurePreserving_continuousLinearEquiv in Breakdown.FreqTr.FieldOp, line 186. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L186).

**Compose the chosen field operators.** Chosen field operators with bounded measurable coefficients compose according to the transported multiplier formula. Source: Breakdown.Freq.fieldOp_comp in Breakdown.FreqTr.FieldOp, line 190. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L190).

**Read the invariant restriction.** When an operator preserves the symbol subspace, its restriction agrees with its original L2 action. Source: Breakdown.Freq.restrictX_coe in Breakdown.FreqTr.FieldOp, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FieldOp.lean#L197).

### Breakdown.FreqTr.FreqTrConjSym

Reflection and conjugation identities show that the Fourier transform of a real L2 field has the required conjugate symmetry.

**Source namespace:** Breakdown.Freq.Internal.FreqTrConjSym.

**A real field has symmetric transform.** The Fourier transform of an integrable real field satisfies conjugate symmetry. Source: Breakdown.Freq.Internal.FreqTrConjSym.conjVec_freqTr_neg in Breakdown.FreqTr.FreqTrConjSym, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrConjSym.lean#L12).

**Evaluate reflected conjugation.** The reflected conjugation operator is almost everywhere the conjugate of the value at negative frequency. Source: Breakdown.Freq.Internal.FreqTrConjSym.reflConj_ae in Breakdown.FreqTr.FreqTrConjSym, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrConjSym.lean#L27).

**Complexify a Schwartz L2 class.** Complexifying a real Schwartz L2 class equals the L2 class of its pointwise complexification. Source: Breakdown.Freq.Internal.FreqTrConjSym.complexify_toLp in Breakdown.FreqTr.FreqTrConjSym, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrConjSym.lean#L32).

**Transform a Schwartz L2 class.** The L2 Fourier transform of a Schwartz class is the class of its Schwartz Fourier transform. Source: Breakdown.Freq.Internal.FreqTrConjSym.freqTrR_toLp in Breakdown.FreqTr.FreqTrConjSym, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrConjSym.lean#L40).

**Real Schwartz transforms obey reflection.** The transformed class of a real Schwartz field is fixed by reflected conjugation. Source: Breakdown.Freq.Internal.FreqTrConjSym.reflConj_freqTr_rapid in Breakdown.FreqTr.FreqTrConjSym, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrConjSym.lean#L43).

**Source namespace:** Breakdown.Freq.

**Prove Fourier conjugate symmetry.** The theorem discharges conjugate symmetry of the Fourier transform of real L2 fields. Source: Breakdown.Freq.freqTrConjSym in Breakdown.FreqTr.FreqTrConjSym, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrConjSym.lean#L63).

### Breakdown.FreqTr.FreqTrL1

The ordinary integral Fourier transforms and their L2 extensions agree almost everywhere for fields belonging to both spaces.

**Source namespace:** Breakdown.Freq.

**Compare weak forward transform values.** The L2 and ordinary Fourier transforms of an L1 and L2 field have equal pairings with every Schwartz scalar test. Source: Breakdown.Freq.integral_smul_freqTrL2_eq in Breakdown.FreqTr.FreqTrL1, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrL1.lean#L12).

**Compare weak inverse transform values.** The inverse L2 and ordinary inverse transforms of an L1 and L2 field have equal Schwartz pairings. Source: Breakdown.Freq.integral_smul_freqTrL2_symm_eq in Breakdown.FreqTr.FreqTrL1, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrL1.lean#L29).

**The two forward transforms agree.** For an L1 and L2 field, the L2 Fourier transform equals the ordinary transform almost everywhere. Source: Breakdown.Freq.freqTrL2_ae_eq in Breakdown.FreqTr.FreqTrL1, line 49. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrL1.lean#L49).

**The two inverse transforms agree.** For an L1 and L2 field, the inverse L2 transform equals the ordinary inverse transform almost everywhere. Source: Breakdown.Freq.freqTrL2_symm_ae_eq in Breakdown.FreqTr.FreqTrL1, line 61. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrL1.lean#L61).

**Prove L1 and L2 consistency.** The theorem supplies both forward and inverse consistency between ordinary and L2 Fourier transforms. Source: Breakdown.Freq.freqTrL1L2 in Breakdown.FreqTr.FreqTrL1, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/FreqTrL1.lean#L74).

### Breakdown.FreqTr.GradCompat

Fourier differentiation and weak gradient pairings force the crossed transformed gradient components to agree.

**Source namespace:** Breakdown.Freq.Internal.GradCompat.

**Uniform bounds from spatial decay.** A decay field has a common constant controlling its velocity and its second order radially decaying derivative. Source: Breakdown.Freq.Internal.GradCompat.decay_bounds in Breakdown.FreqTr.GradCompat, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L14).

**The partial decay field belongs to L2.** Each coordinate derivative of a decay field is square integrable. Source: Breakdown.Freq.Internal.GradCompat.memLp_partialField in Breakdown.FreqTr.GradCompat, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L31).

**The complex gradient representative.** The L2 complexified partial field equals its pointwise complexification almost everywhere. Source: Breakdown.Freq.Internal.GradCompat.coe_gradLp in Breakdown.FreqTr.GradCompat, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L54).

**Move Fourier through an integral.** A Schwartz scalar pairing with the L2 transform equals the pairing of its transform with the original L2 field. Source: Breakdown.Freq.Internal.GradCompat.pair_freqTr in Breakdown.FreqTr.GradCompat, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L64).

**Schwartz mixed derivatives commute.** The two coordinate derivatives of a Schwartz function commute. Source: Breakdown.Freq.Internal.GradCompat.snd_symm in Breakdown.FreqTr.GradCompat, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L71).

**Integrate one derivative by parts.** Pairing a decay field derivative against a Schwartz scalar moves that derivative to the scalar with a negative sign. Source: Breakdown.Freq.Internal.GradCompat.ibp_key in Breakdown.FreqTr.GradCompat, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L87).

**Exchange derivatives in a pairing.** Integration by parts makes the two crossed derivative pairings equal. Source: Breakdown.Freq.Internal.GradCompat.ibp_symm in Breakdown.FreqTr.GradCompat, line 134. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L134).

**Pair the transformed derivative.** The frequency coordinate weighted gradient pairing equals the stated physical derivative pairing with its Fourier factor. Source: Breakdown.Freq.Internal.GradCompat.pair_grad in Breakdown.FreqTr.GradCompat, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L139).

**Symmetry of transformed gradients.** Crossed frequency coordinate pairings of transformed partial fields are equal. Source: Breakdown.Freq.Internal.GradCompat.pair_sym in Breakdown.FreqTr.GradCompat, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L156).

**Source namespace:** Breakdown.Freq.

**Prove gradient compatibility.** The theorem proves the frequency compatibility relations between the transformed coordinate derivatives. Source: Breakdown.Freq.gradCompatible in Breakdown.FreqTr.GradCompat, line 168. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradCompat.lean#L168).

### Breakdown.FreqTr.GradSixDecay

Radial cutoff approximations and derivative decay estimates extend the gradient-to-L6 bound to the decay field class.

**Source namespace:** Breakdown.Freq.Internal.GradSixDecay.

**Bound an operator by three directions.** The operator norm is bounded by three times the square root of the sum of its squared basis values. Source: Breakdown.Freq.Internal.GradSixDecay.opNorm_le_three_mul in Breakdown.FreqTr.GradSixDecay, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L13).

**A smooth cutoff between two balls.** The bump equals one on the unit ball and vanishes outside the ball of radius two. Source: Breakdown.Freq.Internal.GradSixDecay.unitBump in Breakdown.FreqTr.GradSixDecay, line 34. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L34).

**A cutoff at radius R.** The radial cutoff evaluates the fixed bump at the point divided by its radius parameter. Source: Breakdown.Freq.Internal.GradSixDecay.cutoff in Breakdown.FreqTr.GradSixDecay, line 36. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L36).

**The radial cutoff is smooth.** Every rescaled radial cutoff is smooth. Source: Breakdown.Freq.Internal.GradSixDecay.cutoff_contDiff in Breakdown.FreqTr.GradSixDecay, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L38).

**The cutoff equals one inside.** For positive radius, the cutoff is one on the closed ball of that radius. Source: Breakdown.Freq.Internal.GradSixDecay.cutoff_eq_one in Breakdown.FreqTr.GradSixDecay, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L41).

**The cutoff vanishes beyond its ball.** For positive radius, the cutoff is zero at and beyond twice that radius. Source: Breakdown.Freq.Internal.GradSixDecay.cutoff_eq_zero in Breakdown.FreqTr.GradSixDecay, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L47).

**The cutoff is nonnegative.** The radial cutoff is nonnegative. Source: Breakdown.Freq.Internal.GradSixDecay.cutoff_nonneg in Breakdown.FreqTr.GradSixDecay, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L53).

**The cutoff is at most one.** The radial cutoff never exceeds one. Source: Breakdown.Freq.Internal.GradSixDecay.cutoff_le_one in Breakdown.FreqTr.GradSixDecay, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L55).

**The cutoff derivative loses one radius.** The cutoff derivative is uniformly bounded by a fixed nonnegative constant divided by its positive radius. Source: Breakdown.Freq.Internal.GradSixDecay.exists_fderiv_cutoff_le in Breakdown.FreqTr.GradSixDecay, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L57).

**The cutoff derivative vanishes inside.** The derivative vanishes strictly inside the ball where the cutoff is one. Source: Breakdown.Freq.Internal.GradSixDecay.fderiv_cutoff_eq_zero_of_lt in Breakdown.FreqTr.GradSixDecay, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L78).

**The cutoff derivative vanishes outside.** The derivative vanishes strictly beyond twice the cutoff radius. Source: Breakdown.Freq.Internal.GradSixDecay.fderiv_cutoff_eq_zero_of_gt in Breakdown.FreqTr.GradSixDecay, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L86).

**Convert a negative integer power.** A negative integer real power of one plus radius equals the reciprocal of its ordinary integer power. Source: Breakdown.Freq.Internal.GradSixDecay.one_add_norm_rpow_neg_natCast in Breakdown.FreqTr.GradSixDecay, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L93).

**Integrable radial decay in dimension 3.** A negative radial power is integrable in three dimensions when its decay exponent exceeds three. Source: Breakdown.Freq.Internal.GradSixDecay.integrable_one_add_norm_rpow in Breakdown.FreqTr.GradSixDecay, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L97).

**Coordinate unit vectors have norm one.** Each coordinate unit vector has norm one. Source: Breakdown.Freq.Internal.GradSixDecay.norm_unitVector in Breakdown.FreqTr.GradSixDecay, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L101).

**The squared gradient is integrable.** Second order derivative decay makes the sum of squared coordinate derivative norms integrable. Source: Breakdown.Freq.Internal.GradSixDecay.integrable_sum_sq_fderiv in Breakdown.FreqTr.GradSixDecay, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L104).

**The radial Lp integrability threshold.** A finite nonzero Lp exponent admits the radial decay function when exponent times decay order exceeds three. Source: Breakdown.Freq.Internal.GradSixDecay.memLp_one_add_norm_rpow in Breakdown.FreqTr.GradSixDecay, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L121).

**First order decay gives L6.** A continuous vector field with inverse first order radial decay belongs to L6. Source: Breakdown.Freq.Internal.GradSixDecay.memLp_six_of_le in Breakdown.FreqTr.GradSixDecay, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L133).

**Differentiate the cutoff product.** The derivative norm of the cutoff field is at most the original derivative norm plus the cutoff derivative times the field norm. Source: Breakdown.Freq.Internal.GradSixDecay.norm_fderiv_cutoff_smul_le in Breakdown.FreqTr.GradSixDecay, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L142).

**Localize the cutoff error.** The cutoff derivative error is bounded by the indicated constant on the ball of twice the radius and vanishes outside it. Source: Breakdown.Freq.Internal.GradSixDecay.cross_le_indicator in Breakdown.FreqTr.GradSixDecay, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L149).

**A Sobolev bound with a cutoff error.** The L6 norm of the cutoff field is controlled by the original gradient L2 norm plus the explicit cutoff error. Source: Breakdown.Freq.Internal.GradSixDecay.eLpNorm_cutoff_smul_le in Breakdown.FreqTr.GradSixDecay, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L166).

**The cutoff error tends to zero.** The stated volume weighted cutoff error tends to zero along the chosen growing radii. Source: Breakdown.Freq.Internal.GradSixDecay.tendsto_cross_bound in Breakdown.FreqTr.GradSixDecay, line 207. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L207).

**Bound the full gradient L2 norm.** The L2 norm of the operator derivative is bounded by three times the square root of the integrated coordinate derivative squares. Source: Breakdown.Freq.Internal.GradSixDecay.eLpNorm_fderiv_le in Breakdown.FreqTr.GradSixDecay, line 235. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L235).

**The Sobolev bound for decay fields.** The L6 norm of a smooth decay field is bounded by the Sobolev constant times its gradient L2 norm. Source: Breakdown.Freq.Internal.GradSixDecay.eLpNorm_six_le in Breakdown.FreqTr.GradSixDecay, line 260. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/GradSixDecay.lean#L260).

### Breakdown.FreqTr.H1Consistency

Real H1 fields and their Fourier gradients are matched to the symbol-space realization through symmetry, transversality and inverse transformation.

**Source namespace:** Breakdown.Freq.Internal.H1Consistency.

**Read an L2 conversion.** For a square integrable field, the total L2 conversion represents that field almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.toLpOrZero_ae in Breakdown.FreqTr.H1Consistency, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L14).

**Recover a field from its transform.** Taking the physical inverse transform of the complexified Fourier transform recovers the real L2 field almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.toPhys_freqTr_complexify in Breakdown.FreqTr.H1Consistency, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L19).

**The complex scalar operator bound.** The complex multiplication operator norm is bounded by the scalar norm. Source: Breakdown.Freq.Internal.H1Consistency.norm_cmul_le in Breakdown.FreqTr.H1Consistency, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L31).

**Continuous scalar multiplication.** The map from a complex scalar to its multiplication operator is continuous. Source: Breakdown.Freq.Internal.H1Consistency.continuous_cmul in Breakdown.FreqTr.H1Consistency, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L36).

**A normalized coordinate has unit bound.** A frequency coordinate divided by the frequency norm has complex norm at most one. Source: Breakdown.Freq.Internal.H1Consistency.coord_div_norm_le in Breakdown.FreqTr.H1Consistency, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L41).

**Read a bounded scalar symbol operator.** A measurable complex symbol bounded by one acts as pointwise multiplication almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.symbol_ae in Breakdown.FreqTr.H1Consistency, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L48).

**Read the gradient symbol operator.** The embedding gradient operator equals multiplication by its scalar symbol almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.gradSymbol_ae in Breakdown.FreqTr.H1Consistency, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L55).

**Read the derivative symbol operator.** The recovery derivative operator equals multiplication by its scalar symbol almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.derivSymbol_ae in Breakdown.FreqTr.H1Consistency, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L63).

**Nonzero frequency almost everywhere.** The zero frequency is a null set for volume measure. Source: Breakdown.Freq.Internal.H1Consistency.ae_ne_zero in Breakdown.FreqTr.H1Consistency, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L71).

**The norm square is the coordinate sum.** The squared frequency norm equals the sum of squared real coordinates. Source: Breakdown.Freq.Internal.H1Consistency.norm_sq_eq in Breakdown.FreqTr.H1Consistency, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L76).

**Integrability of a Schwartz product.** A Schwartz scalar times an L2 vector field is integrable. Source: Breakdown.Freq.Internal.H1Consistency.integrable_rapid_smul in Breakdown.FreqTr.H1Consistency, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L80).

**Read the complexified L2 representative.** Complexifying an L2 field gives pointwise complexification almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.coe_complexify_ae in Breakdown.FreqTr.H1Consistency, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L85).

**Read the complexified converted field.** Converting and complexifying a square integrable real field gives its pointwise complexification almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.complexify_toLp_ae in Breakdown.FreqTr.H1Consistency, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L89).

**L2 complexification preserves membership.** Pointwise complexification preserves square integrability. Source: Breakdown.Freq.Internal.H1Consistency.memLp_complexify in Breakdown.FreqTr.H1Consistency, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L94).

**Differentiate the H1 distribution.** The distributional coordinate derivative of an H1 field is the tempered distribution of its classical partial field. Source: Breakdown.Freq.Internal.H1Consistency.lineDeriv_eq in Breakdown.FreqTr.H1Consistency, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L98).

**Schwartz tests detect vector zero.** A locally integrable vector field annihilating every Schwartz scalar test is zero almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.ae_zero_of_rapid in Breakdown.FreqTr.H1Consistency, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L133).

**Transform the H1 coordinate derivative.** The transform of an H1 coordinate derivative is the corresponding imaginary frequency multiplier times the original transform almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.freqTr_partial_ae in Breakdown.FreqTr.H1Consistency, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L142).

**Schwartz tests detect scalar zero.** A locally integrable scalar field annihilating every Schwartz scalar test is zero almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.ae_zero_of_rapid_scalar in Breakdown.FreqTr.H1Consistency, line 188. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L188).

**Move the transform to the test scalar.** The Schwartz pairing allows the Fourier transform to move from the L2 field to the scalar test. Source: Breakdown.Freq.Internal.H1Consistency.integral_freqTr_swap in Breakdown.FreqTr.H1Consistency, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L197).

**Integrate a coordinate.** Taking a coordinate commutes with the integral of an integrable vector field. Source: Breakdown.Freq.Internal.H1Consistency.integral_coord in Breakdown.FreqTr.H1Consistency, line 203. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L203).

**The transformed H1 divergence is zero.** For an H1 field, the matching coordinate sum of transformed partial fields vanishes almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.div_freqTr_ae in Breakdown.FreqTr.H1Consistency, line 207. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L207).

**The frequency inclusion preserves norm.** The complexified frequency has the original real norm. Source: Breakdown.Freq.Internal.H1Consistency.norm_freqVec in Breakdown.FreqTr.H1Consistency, line 252. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L252).

**Evaluate the longitudinal projection.** The longitudinal projection is inverse squared radius times the frequency pairing times the frequency vector. Source: Breakdown.Freq.Internal.H1Consistency.longitudinal_apply in Breakdown.FreqTr.H1Consistency, line 255. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L255).

**The longitudinal map has unit bound.** The longitudinal projection has operator norm at most one. Source: Breakdown.Freq.Internal.H1Consistency.norm_longitudinal_le in Breakdown.FreqTr.H1Consistency, line 258. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L258).

**The longitudinal map is measurable.** The operator valued longitudinal projection is almost everywhere strongly measurable. Source: Breakdown.Freq.Internal.H1Consistency.aesm_longitudinal in Breakdown.FreqTr.H1Consistency, line 272. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L272).

**Longitudinal projection pointwise.** The L2 longitudinal operator acts by its pointwise projection almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.longitudinal_ae in Breakdown.FreqTr.H1Consistency, line 283. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L283).

**The reflected symbol representative.** Reflected conjugation acts by conjugating the value at negative frequency almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.reflConj_ae in Breakdown.FreqTr.H1Consistency, line 287. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L287).

**Reflection preserves null set equality.** Almost everywhere equality remains true after frequency reflection. Source: Breakdown.Freq.Internal.H1Consistency.ae_comp_neg in Breakdown.FreqTr.H1Consistency, line 292. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L292).

**The two state space constraints.** Membership in the symbol subspace is equivalent to conjugate reflection symmetry and zero longitudinal part. Source: Breakdown.Freq.Internal.H1Consistency.mem_sig_iff in Breakdown.FreqTr.H1Consistency, line 296. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L296).

**Even multipliers keep the state space.** An almost everywhere even real scalar multiple of a state symbol remains in the symbol subspace. Source: Breakdown.Freq.Internal.H1Consistency.mem_sig_of_ae in Breakdown.FreqTr.H1Consistency, line 300. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L300).

**The product of derivative factors.** The gradient embedding factor times a derivative factor simplifies to the stated coordinate square over radius. Source: Breakdown.Freq.Internal.H1Consistency.grad_term in Breakdown.FreqTr.H1Consistency, line 318. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L318).

**Sum the gradient embedding factors.** At nonzero frequency the sum of the embedding and derivative factor products is two pi times radius. Source: Breakdown.Freq.Internal.H1Consistency.grad_sum in Breakdown.FreqTr.H1Consistency, line 325. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L325).

**Cancel the derivative normalization.** At nonzero frequency multiplying the derivative symbol by two pi times radius gives the standard Fourier derivative factor. Source: Breakdown.Freq.Internal.H1Consistency.deriv_mul in Breakdown.FreqTr.H1Consistency, line 336. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L336).

**A finite sum representative formula.** The representative of a three term L2 sum is their pointwise sum almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.coe_sum_three in Breakdown.FreqTr.H1Consistency, line 343. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L343).

**The H1 embedding symbol formula.** The gradient representation of an H1 field is two pi times radius times its ordinary Fourier transform almost everywhere. Source: Breakdown.Freq.Internal.H1Consistency.ofGrad_ae in Breakdown.FreqTr.H1Consistency, line 349. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L349).

**The H1 transform is a state symbol.** The Fourier transform of an H1 solenoidal real field satisfies the symbol subspace constraints. Source: Breakdown.Freq.Internal.H1Consistency.hat_mem_sig in Breakdown.FreqTr.H1Consistency, line 359. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L359).

**Source namespace:** Breakdown.Freq.

**Prove the H1 physical realization.** The theorem discharges the H1 consistency interface from multiplier realization, Fourier symmetry and half Laplacian velocity inversion. Source: Breakdown.Freq.h1Consistency in Breakdown.FreqTr.H1Consistency, line 386. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/H1Consistency.lean#L386).

### Breakdown.FreqTr.Heat

The Fourier heat multiplier yields the state semigroup, contraction, initial value and time-continuity properties.

**Source namespace:** Breakdown.Freq.Internal.Heat.

**Strict positivity of the heat factor.** The heat factor is strictly positive. Source: Breakdown.Freq.Internal.Heat.heatFactor_pos in Breakdown.FreqTr.Heat, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L12).

**The heat factor does not exceed one.** The heat factor is at most one. Source: Breakdown.Freq.Internal.Heat.heatFactor_le_one in Breakdown.FreqTr.Heat, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L14).

**Frequency continuity of heat.** For fixed time the heat factor is continuous in frequency. Source: Breakdown.Freq.Internal.Heat.continuous_heatFactor in Breakdown.FreqTr.Heat, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L21).

**Time continuity of heat.** For fixed frequency the heat factor is continuous in time. Source: Breakdown.Freq.Internal.Heat.continuous_heatFactor_time in Breakdown.FreqTr.Heat, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L25).

**The heat factors form a semigroup.** At nonnegative times the heat factor at their sum is the product of the two factors. Source: Breakdown.Freq.Internal.Heat.heatFactor_add in Breakdown.FreqTr.Heat, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L29).

**Realize the L2 heat multiplier.** The L2 heat operator realizes its scalar frequency multiplication formula. Source: Breakdown.Freq.Internal.Heat.heat_realized in Breakdown.FreqTr.Heat, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L36).

**The pointwise L2 heat formula.** The heat operator multiplies the representative by the heat factor almost everywhere. Source: Breakdown.Freq.Internal.Heat.heat_ae in Breakdown.FreqTr.Heat, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L53).

**Commute heat with compatible operators.** Heat commutes with a realized operator whose frequency map preserves the heat factor. Source: Breakdown.Freq.Internal.Heat.heat_comm in Breakdown.FreqTr.Heat, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L59).

**Reflection is quasi measure preserving.** Frequency negation preserves volume null sets. Source: Breakdown.Freq.Internal.Heat.quasiMeasurePreserving_neg in Breakdown.FreqTr.Heat, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L78).

**Heat preserves the symbol constraints.** The L2 heat operator preserves the symbol subspace. Source: Breakdown.Freq.Internal.Heat.heat_mem in Breakdown.FreqTr.Heat, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L83).

**The state heat operator is a restriction.** The state heat evolution agrees with ambient L2 heat on its underlying symbol. Source: Breakdown.Freq.Internal.Heat.heatX_coe in Breakdown.FreqTr.Heat, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L104).

**Strong continuity of L2 heat.** For every L2 field, heat evolution is continuous in time. Source: Breakdown.Freq.Internal.Heat.heatL2_continuous in Breakdown.FreqTr.Heat, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L109).

**Source namespace:** Breakdown.Freq.

**Prove the heat semigroup interface.** The theorem establishes the state heat semigroup, contraction and continuity requirements. Source: Breakdown.Freq.heatSemigroup in Breakdown.FreqTr.Heat, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Heat.lean#L154).

### Breakdown.FreqTr.MildOfWeak

Testing against dense embedded fields and regularizing with heat converts the integrated weak state equation into the mild Duhamel identity.

**Source namespace:** Breakdown.Freq.Internal.MildOfWeak.

**The heat smoothed Laplacian.** The state operator is the restricted multiplier by the Laplacian factor times the heat factor. Source: Breakdown.Freq.Internal.MildOfWeak.sspHeatX in Breakdown.FreqTr.MildOfWeak, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L16).

**A regularised square root Laplacian.** The auxiliary multiplier divides two pi times radius by one plus the Laplacian factor. Source: Breakdown.Freq.Internal.MildOfWeak.halfFactor in Breakdown.FreqTr.MildOfWeak, line 19. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L19).

**The regularised multiplier on states.** The auxiliary state operator restricts multiplication by the regularised square root Laplacian factor. Source: Breakdown.Freq.Internal.MildOfWeak.halfX in Breakdown.FreqTr.MildOfWeak, line 21. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L21).

**Nonnegativity of the Laplacian factor.** The Laplacian frequency factor is nonnegative. Source: Breakdown.Freq.Internal.MildOfWeak.sspFactor_nonneg in Breakdown.FreqTr.MildOfWeak, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L24).

**Continuity of the regularised factor.** The auxiliary half Laplacian factor is continuous. Source: Breakdown.Freq.Internal.MildOfWeak.continuous_halfFactor in Breakdown.FreqTr.MildOfWeak, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L26).

**The regularised factor has unit bound.** The absolute auxiliary half Laplacian factor is at most one. Source: Breakdown.Freq.Internal.MildOfWeak.abs_halfFactor_le in Breakdown.FreqTr.MildOfWeak, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L31).

**The regularised factor is even.** Negating frequency leaves the auxiliary half Laplacian factor unchanged. Source: Breakdown.Freq.Internal.MildOfWeak.halfFactor_neg in Breakdown.FreqTr.MildOfWeak, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L38).

**Read the regularised state operator.** The auxiliary state operator agrees with its ambient pointwise L2 multiplier. Source: Breakdown.Freq.Internal.MildOfWeak.halfX_coe in Breakdown.FreqTr.MildOfWeak, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L41).

**A regularised multiplier formula.** The auxiliary state operator multiplies the state representative by its scalar factor almost everywhere. Source: Breakdown.Freq.Internal.MildOfWeak.halfX_ae in Breakdown.FreqTr.MildOfWeak, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L47).

**The regularised state operator contracts.** The auxiliary state operator does not increase the norm. Source: Breakdown.Freq.Internal.MildOfWeak.norm_halfX_le in Breakdown.FreqTr.MildOfWeak, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L52).

**Construct a half Laplacian predecessor.** For a Laplacian related pair, applying the auxiliary operator to their sum gives the required half Laplacian predecessor. Source: Breakdown.Freq.Internal.MildOfWeak.isHalfSspOf_half in Breakdown.FreqTr.MildOfWeak, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L57).

**An L2 bound for a Laplacian pair.** The velocity of the Laplacian state is square integrable with the stated bound by the two state norms. Source: Breakdown.Freq.Internal.MildOfWeak.vel_two in Breakdown.FreqTr.MildOfWeak, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L71).

**The velocity L6 bound.** Every recovered velocity belongs to L6 and has norm bounded by the velocity operator norm times the state norm. Source: Breakdown.Freq.Internal.MildOfWeak.vel_six in Breakdown.FreqTr.MildOfWeak, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L81).

**Combine the two interpolated bounds.** The scalar estimate turns separate bounds for the two norms into the stated product bound for their geometric mean. Source: Breakdown.Freq.Internal.MildOfWeak.abs_le_mul_sqrt_bound in Breakdown.FreqTr.MildOfWeak, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L88).

**A graph norm trilinear estimate.** The trilinear pairing with the velocity of a Laplacian related state is bounded by the product of input norms and the sum of graph pair norms. Source: Breakdown.Freq.Internal.MildOfWeak.tri_bound in Breakdown.FreqTr.MildOfWeak, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L107).

**Subtract the velocity test input.** For Laplacian related pairs, the trilinear functional respects subtraction of their velocity tests. Source: Breakdown.Freq.Internal.MildOfWeak.tri_sub_third in Breakdown.FreqTr.MildOfWeak, line 120. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L120).

**Subtract Laplacian related pairs.** The Laplacian relation is preserved by subtracting two related pairs. Source: Breakdown.Freq.Internal.MildOfWeak.isSspOf_sub in Breakdown.FreqTr.MildOfWeak, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L133).

**Ignore null set changes in the test.** Almost everywhere equal third fields have equal trilinear pairings. Source: Breakdown.Freq.Internal.MildOfWeak.tri_congr in Breakdown.FreqTr.MildOfWeak, line 141. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L141).

**Recover the velocity specification.** The velocity existence interface makes the chosen velocity satisfy the recovery specification. Source: Breakdown.Freq.Internal.MildOfWeak.velocity_spec in Breakdown.FreqTr.MildOfWeak, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L148).

**Recover a test Laplacian velocity.** Velocity recovery of the embedded negative Laplacian of a test field equals that negative Laplacian almost everywhere. Source: Breakdown.Freq.Internal.MildOfWeak.velocity_negSsp in Breakdown.FreqTr.MildOfWeak, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L154).

**The heat Laplacian factor is even.** The product of the Laplacian and heat factors is unchanged by frequency negation. Source: Breakdown.Freq.Internal.MildOfWeak.sspHeat_neg in Breakdown.FreqTr.MildOfWeak, line 164. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L164).

**Read the heat Laplacian on states.** At positive time the state heat Laplacian has the displayed ambient L2 multiplier. Source: Breakdown.Freq.Internal.MildOfWeak.sspHeatX_coe in Breakdown.FreqTr.MildOfWeak, line 168. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L168).

**Heat supplies a Laplacian related pair.** The heated state and its heat smoothed Laplacian satisfy the Laplacian relation. Source: Breakdown.Freq.Internal.MildOfWeak.isSspOf_heat in Breakdown.FreqTr.MildOfWeak, line 175. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L175).

**Differentiate a moving inner product.** The derivative of the moving pairing adds the fixed test derivative to the pairing with the test's derivative. Source: Breakdown.Freq.Internal.MildOfWeak.hasDerivAt_inner_moving in Breakdown.FreqTr.MildOfWeak, line 186. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L186).

**Continuity of the nonlinear test pairing.** A continuous state curve gives a continuous trilinear self pairing against the velocity of a fixed Laplacian related test. Source: Breakdown.Freq.Internal.MildOfWeak.tri_continuousOn in Breakdown.FreqTr.MildOfWeak, line 214. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L214).

**Extend the weak equation to graph tests.** The weak solution identity extends from compact tests to every Laplacian related test pair through the density and trilinear estimates. Source: Breakdown.Freq.Internal.MildOfWeak.weak_ext in Breakdown.FreqTr.MildOfWeak, line 219. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L219).

**Differentiate the extended weak identity.** Inside the time interval, the extended weak pairing derivative is the negative linear plus nonlinear test pairing. Source: Breakdown.Freq.Internal.MildOfWeak.weak_deriv in Breakdown.FreqTr.MildOfWeak, line 295. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L295).

**Subtract two diagonal bilinear terms.** The difference of two diagonal bilinear terms splits into the two terms containing the state difference. Source: Breakdown.Freq.Internal.MildOfWeak.bilin_diff in Breakdown.FreqTr.MildOfWeak, line 314. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L314).

**Continuity along a bilinear trajectory.** Positive continuous smoothing time and a continuous state curve produce a continuous diagonal bilinear curve. Source: Breakdown.Freq.Internal.MildOfWeak.bilin_curve_continuousOn in Breakdown.FreqTr.MildOfWeak, line 321. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L321).

**Integrability of the Duhamel term.** A continuous state curve gives an interval integrable bilinear Duhamel integrand up to the final time. Source: Breakdown.Freq.Internal.MildOfWeak.bilin_intervalIntegrable in Breakdown.FreqTr.MildOfWeak, line 358. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L358).

**A quadratic exponential remainder.** The exponential remainder after its linear term is bounded by the square of the argument times the exponential of its absolute value. Source: Breakdown.Freq.Internal.MildOfWeak.exp_expansion_le in Breakdown.FreqTr.MildOfWeak, line 387. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L387).

**A uniform heat exponential remainder.** Near a positive reference time, the heat exponential has the displayed quadratic time remainder bound. Source: Breakdown.Freq.Internal.MildOfWeak.heat_expansion in Breakdown.FreqTr.MildOfWeak, line 405. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L405).

**A quadratic heat operator remainder.** Near positive time the heat operator's linear approximation has the stated quadratic norm bound. Source: Breakdown.Freq.Internal.MildOfWeak.heat_expansion_norm in Breakdown.FreqTr.MildOfWeak, line 440. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L440).

**Differentiate heat in positive time.** The time derivative of the heated state is its negative heat smoothed Laplacian. Source: Breakdown.Freq.Internal.MildOfWeak.heat_hasDerivAt in Breakdown.FreqTr.MildOfWeak, line 473. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L473).

**The bilinear operator pairing identity.** At positive time the bilinear operator inner product equals the interaction form. Source: Breakdown.Freq.Internal.MildOfWeak.inner_bilinX in Breakdown.FreqTr.MildOfWeak, line 489. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L489).

**Pair an interval integral.** A continuous linear inner product functional commutes with an interval integral of an integrable state curve. Source: Breakdown.Freq.Internal.MildOfWeak.inner_intervalIntegral in Breakdown.FreqTr.MildOfWeak, line 496. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L496).

**A smoothed variation of constants.** The weak solution tested against positive time heat satisfies the displayed heat plus bilinear integral identity. Source: Breakdown.Freq.Internal.MildOfWeak.varConst_inner in Breakdown.FreqTr.MildOfWeak, line 505. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L505).

**Source namespace:** Breakdown.Freq.

**Prove weak solutions are mild.** The theorem combines the weak equation, graph density, heat calculus and bilinear estimates to obtain the mild formulation. Source: Breakdown.Freq.mildOfWeak in Breakdown.FreqTr.MildOfWeak, line 552. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/MildOfWeak.lean#L552).

### Breakdown.FreqTr.NiceApprox

Cutoff curl potentials approximate smooth annular solenoidal symbols by compact physical tests while controlling both the state and its Laplacian partner.

**Source namespace:** Breakdown.Freq.Internal.NiceApprox.

**A fixed directional derivative.** The auxiliary partial operator differentiates a field in a specified spatial direction. Source: Breakdown.Freq.Internal.NiceApprox.pd in Breakdown.FreqTr.NiceApprox, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L14).

**Directional derivatives are smooth.** Every directional derivative of a smooth field is smooth. Source: Breakdown.Freq.Internal.NiceApprox.contDiff_pd in Breakdown.FreqTr.NiceApprox, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L16).

**Differentiable directional derivatives.** Every directional derivative of a smooth field is differentiable. Source: Breakdown.Freq.Internal.NiceApprox.differentiable_pd in Breakdown.FreqTr.NiceApprox, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L20).

**Read the second directional derivative.** The iterated directional derivative equals the second Fréchet derivative evaluated on the two directions. Source: Breakdown.Freq.Internal.NiceApprox.pd_pd_apply in Breakdown.FreqTr.NiceApprox, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L24).

**Smooth directional derivatives commute.** The two fixed directional derivatives of a smooth field commute. Source: Breakdown.Freq.Internal.NiceApprox.pd_comm in Breakdown.FreqTr.NiceApprox, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L32).

**Differentiate a finite family sum.** Directional differentiation distributes over a finite sum of differentiable fields. Source: Breakdown.Freq.Internal.NiceApprox.pd_sum in Breakdown.FreqTr.NiceApprox, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L40).

**Directional derivatives respect negation.** The directional derivative of a negative field is the negative derivative. Source: Breakdown.Freq.Internal.NiceApprox.pd_neg in Breakdown.FreqTr.NiceApprox, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L50).

**The zero field has zero derivative.** Every directional derivative of the zero field is zero. Source: Breakdown.Freq.Internal.NiceApprox.pd_const_zero in Breakdown.FreqTr.NiceApprox, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L54).

**Differentiate a coordinate.** Taking a coordinate commutes with the directional derivative of a differentiable vector field. Source: Breakdown.Freq.Internal.NiceApprox.pd_apply_coord in Breakdown.FreqTr.NiceApprox, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L58).

**Directional derivatives keep support.** Directional differentiation preserves compact support. Source: Breakdown.Freq.Internal.NiceApprox.hasCompactSupport_pd in Breakdown.FreqTr.NiceApprox, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L66).

**The Laplacian in directional notation.** The negative Laplacian is the negative sum of second derivatives along the three coordinate directions. Source: Breakdown.Freq.Internal.NiceApprox.negSsp_eq in Breakdown.FreqTr.NiceApprox, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L70).

**The divergence in directional notation.** Divergence is the sum of matching coordinates of the three coordinate directional derivatives. Source: Breakdown.Freq.Internal.NiceApprox.divergence_eq_sum in Breakdown.FreqTr.NiceApprox, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L80).

**Coordinates of smooth fields are smooth.** Every coordinate function of a smooth vector field is smooth. Source: Breakdown.Freq.Internal.NiceApprox.contDiff_coord in Breakdown.FreqTr.NiceApprox, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L83).

**Pointwise coordinate differentiation.** The coordinate of the derivative field equals the derivative of the coordinate function. Source: Breakdown.Freq.Internal.NiceApprox.pd_coord_fun in Breakdown.FreqTr.NiceApprox, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L87).

**The Laplacian preserves zero divergence.** The negative Laplacian of a smooth divergence free field remains divergence free. Source: Breakdown.Freq.Internal.NiceApprox.divergence_negSsp in Breakdown.FreqTr.NiceApprox, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L90).

**The Laplacian preserves test fields.** The negative Laplacian preserves smoothness, compact support and zero divergence of test fields. Source: Breakdown.Freq.Internal.NiceApprox.negSsp_isTestField in Breakdown.FreqTr.NiceApprox, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L130).

**Cross product as a linear map.** The cross product with a fixed real vector is packaged as a continuous real linear map. Source: Breakdown.Freq.Internal.NiceApprox.crossL in Breakdown.FreqTr.NiceApprox, line 149. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L149).

**Evaluate the real cross product.** The linear cross product map has the usual three coordinate formula. Source: Breakdown.Freq.Internal.NiceApprox.crossL_apply in Breakdown.FreqTr.NiceApprox, line 160. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L160).

**Curl from coordinate derivatives.** Curl is the sum of cross products of the coordinate unit vectors with the corresponding partial derivatives. Source: Breakdown.Freq.Internal.NiceApprox.curlField in Breakdown.FreqTr.NiceApprox, line 163. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L163).

**Move a linear map through a derivative.** A fixed continuous linear value map commutes with directional differentiation. Source: Breakdown.Freq.Internal.NiceApprox.pd_clm in Breakdown.FreqTr.NiceApprox, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L166).

**Curl preserves smoothness.** The curl of a smooth field is smooth. Source: Breakdown.Freq.Internal.NiceApprox.contDiff_curlField in Breakdown.FreqTr.NiceApprox, line 176. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L176).

**The divergence of a curl vanishes.** Every smooth curl has zero divergence. Source: Breakdown.Freq.Internal.NiceApprox.divergence_curlField in Breakdown.FreqTr.NiceApprox, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L179).

**Every polynomial Schwartz decay bound.** A Schwartz function is bounded by a constant divided by any chosen integer power of one plus radius. Source: Breakdown.Freq.Internal.NiceApprox.rapid_bound in Breakdown.FreqTr.NiceApprox, line 198. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L198).

**A solenoidal Schwartz field decays.** A divergence free real Schwartz field satisfies the decay field conditions. Source: Breakdown.Freq.Internal.NiceApprox.isDecayField_rapid in Breakdown.FreqTr.NiceApprox, line 207. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L207).

**Curl on Schwartz fields.** The Schwartz curl packages the sum of differentiated and cross multiplied Schwartz fields. Source: Breakdown.Freq.Internal.NiceApprox.curlS in Breakdown.FreqTr.NiceApprox, line 223. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L223).

**Read the Schwartz curl.** The Schwartz curl represents the physical curl field. Source: Breakdown.Freq.Internal.NiceApprox.curlS_apply in Breakdown.FreqTr.NiceApprox, line 226. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L226).

**The Schwartz negative Laplacian.** The Schwartz negative Laplacian is the negative sum of repeated coordinate derivative operators. Source: Breakdown.Freq.Internal.NiceApprox.negSspS in Breakdown.FreqTr.NiceApprox, line 230. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L230).

**Read the Schwartz Laplacian.** The Schwartz negative Laplacian represents the physical negative Laplacian. Source: Breakdown.Freq.Internal.NiceApprox.negSspS_apply in Breakdown.FreqTr.NiceApprox, line 233. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L233).

**Decay of a curl and its Laplacian.** A Schwartz potential's curl and the negative Laplacian of that curl are both decay fields. Source: Breakdown.Freq.Internal.NiceApprox.curl_decay in Breakdown.FreqTr.NiceApprox, line 241. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L241).

**The standard smooth radial bump.** The standard bump transitions between the unit ball and the ball of radius two. Source: Breakdown.Freq.Internal.NiceApprox.stdBump in Breakdown.FreqTr.NiceApprox, line 258. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L258).

**Cut off a vector potential.** The cutoff potential multiplies the original potential by the standard bump at the inverse scaled point. Source: Breakdown.Freq.Internal.NiceApprox.cutField in Breakdown.FreqTr.NiceApprox, line 260. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L260).

**The cutoff potential is smooth.** Cutting off a smooth potential preserves smoothness. Source: Breakdown.Freq.Internal.NiceApprox.contDiff_cutField in Breakdown.FreqTr.NiceApprox, line 262. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L262).

**The cutoff potential has compact support.** At nonzero radius the cutoff potential has compact support. Source: Breakdown.Freq.Internal.NiceApprox.hasCompactSupport_cutField in Breakdown.FreqTr.NiceApprox, line 266. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L266).

**Curl preserves compact support.** The curl of a compactly supported potential has compact support. Source: Breakdown.Freq.Internal.NiceApprox.hasCompactSupport_curlField in Breakdown.FreqTr.NiceApprox, line 272. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L272).

**Cutoff curls are test fields.** The curl of a smoothly cut off potential is a solenoidal test field at nonzero cutoff radius. Source: Breakdown.Freq.Internal.NiceApprox.cutoff_isTestField in Breakdown.FreqTr.NiceApprox, line 280. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L280).

**Differentiate a difference.** Directional derivatives respect subtraction of differentiable fields. Source: Breakdown.Freq.Internal.NiceApprox.pd_sub' in Breakdown.FreqTr.NiceApprox, line 286. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L286).

**Curl respects subtraction.** The curl of a difference is the difference of the curls for differentiable fields. Source: Breakdown.Freq.Internal.NiceApprox.curlField_sub in Breakdown.FreqTr.NiceApprox, line 294. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L294).

**The Laplacian respects subtraction.** The negative Laplacian respects subtraction of smooth fields. Source: Breakdown.Freq.Internal.NiceApprox.negSsp_sub in Breakdown.FreqTr.NiceApprox, line 299. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L299).

**Smoothness of the negative Laplacian.** The negative Laplacian of a smooth field is smooth. Source: Breakdown.Freq.Internal.NiceApprox.negSsp_isTestField_aux in Breakdown.FreqTr.NiceApprox, line 310. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L310).

**A locally zero field has zero derivative.** A field vanishing on an open set has zero directional derivative there. Source: Breakdown.Freq.Internal.NiceApprox.pd_zero_on in Breakdown.FreqTr.NiceApprox, line 314. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L314).

**A locally zero field has zero curl.** A field vanishing on an open set has zero curl there. Source: Breakdown.Freq.Internal.NiceApprox.curlField_zero_on in Breakdown.FreqTr.NiceApprox, line 324. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L324).

**A locally zero field has zero Laplacian.** A smooth field vanishing on an open set has zero negative Laplacian there. Source: Breakdown.Freq.Internal.NiceApprox.negSsp_zero_on in Breakdown.FreqTr.NiceApprox, line 329. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L329).

**The cutoff error vanishes locally.** Inside the positive cutoff radius, the cutoff potential equals the original potential. Source: Breakdown.Freq.Internal.NiceApprox.cutField_sub_zero_on in Breakdown.FreqTr.NiceApprox, line 335. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L335).

**The derivative errors eventually vanish.** At each fixed point, the gradient errors of the cutoff curl and its negative Laplacian are eventually zero as the radius grows. Source: Breakdown.Freq.Internal.NiceApprox.cutoff_eventually_zero in Breakdown.FreqTr.NiceApprox, line 348. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L348).

**Finite orders lie below infinity.** Every finite derivative order lies below the infinite smoothness index. Source: Breakdown.Freq.Internal.NiceApprox.le_infty_of_nat in Breakdown.FreqTr.NiceApprox, line 367. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L367).

**Higher directional derivative bounds.** The order n derivative of a directional derivative is bounded by the direction norm times the order n plus one derivative norm. Source: Breakdown.Freq.Internal.NiceApprox.norm_iter_pd in Breakdown.FreqTr.NiceApprox, line 370. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L370).

**Unit vector norm.** Every coordinate unit vector has norm one. Source: Breakdown.Freq.Internal.NiceApprox.norm_unitVector in Breakdown.FreqTr.NiceApprox, line 383. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L383).

**A coordinate derivative bound.** The coordinate derivative norm is at most the first iterated derivative norm. Source: Breakdown.Freq.Internal.NiceApprox.norm_pd_le in Breakdown.FreqTr.NiceApprox, line 386. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L386).

**A bound for the curl operator.** The curl constant is the sum of the norms of cross product maps with the three unit vectors. Source: Breakdown.Freq.Internal.NiceApprox.curlConst in Breakdown.FreqTr.NiceApprox, line 393. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L393).

**Bound iterated derivatives of curl.** An order n derivative of curl is bounded by the curl constant times the order n plus one derivative norm. Source: Breakdown.Freq.Internal.NiceApprox.norm_iter_curl in Breakdown.FreqTr.NiceApprox, line 395. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L395).

**Bound iterated Laplacian derivatives.** An order n derivative of the negative Laplacian is bounded by three times the order n plus two derivative norm. Source: Breakdown.Freq.Internal.NiceApprox.norm_iter_negSsp in Breakdown.FreqTr.NiceApprox, line 413. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L413).

**Uniform cutoff derivative decay.** Every derivative of the cutoff error has a uniform fourth order radial decay bound once the radius is at least one. Source: Breakdown.Freq.Internal.NiceApprox.cut_iter_bound in Breakdown.FreqTr.NiceApprox, line 434. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L434).

**The curl constant is nonnegative.** The sum defining the curl constant is nonnegative. Source: Breakdown.Freq.Internal.NiceApprox.curlConst_nonneg in Breakdown.FreqTr.NiceApprox, line 495. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L495).

**One integrable cutoff error majorant.** A single integrable function eventually dominates both squared gradient errors used in the graph norm approximation. Source: Breakdown.Freq.Internal.NiceApprox.cutoff_dominated in Breakdown.FreqTr.NiceApprox, line 497. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L497).

**Both cutoff gradient errors vanish.** The integrated squared gradient errors of the curl and its negative Laplacian tend to zero as the cutoff radius grows. Source: Breakdown.Freq.Internal.NiceApprox.cutoff_tendsto in Breakdown.FreqTr.NiceApprox, line 567. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L567).

**Approximate a Schwartz curl by tests.** A Schwartz curl admits a compact solenoidal test approximation with arbitrarily small gradient error for both the field and its Laplacian. Source: Breakdown.Freq.Internal.NiceApprox.cutoff_approx in Breakdown.FreqTr.NiceApprox, line 607. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L607).

**Compact support gives every decay order.** A continuous compactly supported function has a bound at every polynomial radial decay order. Source: Breakdown.Freq.Internal.NiceApprox.exists_bound_of_compactSupport in Breakdown.FreqTr.NiceApprox, line 634. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L634).

**Compact tests are decay fields.** Every solenoidal test field is a decay field. Source: Breakdown.Freq.Internal.NiceApprox.isDecayField_of_isTestField in Breakdown.FreqTr.NiceApprox, line 647. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L647).

**Subtract decay fields.** Subtracting two decay fields gives another decay field. Source: Breakdown.Freq.Internal.NiceApprox.isDecayField_sub in Breakdown.FreqTr.NiceApprox, line 663. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L663).

**A Fourier bound for gradient error.** A sufficiently small integrated gradient difference gives the stated L2 error between the embedded field and the target symbol. Source: Breakdown.Freq.Internal.NiceApprox.eLpNorm_embed_sub_lt in Breakdown.FreqTr.NiceApprox, line 681. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L681).

**Bound scalar multiplication.** The complex multiplication operator norm is at most the complex scalar norm. Source: Breakdown.Freq.Internal.NiceApprox.cmul_norm_le in Breakdown.FreqTr.NiceApprox, line 700. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L700).

**Continuity of the scalar operator.** The multiplication map depends continuously on its complex scalar. Source: Breakdown.Freq.Internal.NiceApprox.continuous_cmul in Breakdown.FreqTr.NiceApprox, line 705. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L705).

**A unit bound for gradient symbols.** The gradient embedding symbol has norm at most one. Source: Breakdown.Freq.Internal.NiceApprox.gradSymbol_norm_le in Breakdown.FreqTr.NiceApprox, line 713. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L713).

**Gradient symbols are measurable.** Every gradient embedding symbol is measurable. Source: Breakdown.Freq.Internal.NiceApprox.measurable_gradSymbol in Breakdown.FreqTr.NiceApprox, line 729. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L729).

**The gradient operator formula.** The realized gradient multiplier acts pointwise almost everywhere. Source: Breakdown.Freq.Internal.NiceApprox.fieldOp_grad_ae in Breakdown.FreqTr.NiceApprox, line 733. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L733).

**Collapse the gradient symbol sum.** Summing the embedding symbols against the Fourier derivative factors gives two pi times radius times the vector. Source: Breakdown.Freq.Internal.NiceApprox.scalar_identity in Breakdown.FreqTr.NiceApprox, line 744. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L744).

**Embed a solenoidal Schwartz field.** The state embedding of a solenoidal Schwartz field is two pi times radius times its Fourier transform almost everywhere. Source: Breakdown.Freq.Internal.NiceApprox.embed_rapid in Breakdown.FreqTr.NiceApprox, line 772. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L772).

**Transform a Schwartz line derivative.** Fourier transformation converts a coordinate line derivative to its imaginary frequency factor. Source: Breakdown.Freq.Internal.NiceApprox.freqTr_lineDeriv_apply in Breakdown.FreqTr.NiceApprox, line 829. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L829).

**Complexify the Schwartz Laplacian.** Complexification of the Schwartz negative Laplacian is the negative sum of the complexified second derivatives. Source: Breakdown.Freq.Internal.NiceApprox.postcomp_negSspS in Breakdown.FreqTr.NiceApprox, line 837. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L837).

**Transform the negative Laplacian.** The transform of the negative Laplacian is the Laplacian factor times the original transform. Source: Breakdown.Freq.Internal.NiceApprox.freqTr_negSsp in Breakdown.FreqTr.NiceApprox, line 854. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L854).

**Fourier transform under value maps.** A fixed complex continuous linear map commutes with Fourier transformation of a Schwartz field. Source: Breakdown.Freq.Internal.NiceApprox.freqTr_clm_apply in Breakdown.FreqTr.NiceApprox, line 884. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L884).

**Conjugate a character weighted vector.** Conjugating a Fourier character multiple negates the character phase and conjugates the vector. Source: Breakdown.Freq.Internal.NiceApprox.conjVec_circle_smul in Breakdown.FreqTr.NiceApprox, line 894. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L894).

**Two conjugations cancel.** Conjugating a complex vector twice returns the original vector. Source: Breakdown.Freq.Internal.NiceApprox.conjVec_conjVec in Breakdown.FreqTr.NiceApprox, line 907. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L907).

**A symmetric symbol has a real inverse.** The inverse transform of a conjugate symmetric Schwartz symbol is fixed by vector conjugation. Source: Breakdown.Freq.Internal.NiceApprox.freqTrInv_conj in Breakdown.FreqTr.NiceApprox, line 911. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L911).

**Recover a conjugation fixed vector.** A vector fixed by conjugation is recovered by complexifying its real part. Source: Breakdown.Freq.Internal.NiceApprox.complexify_realVec_of_conj in Breakdown.FreqTr.NiceApprox, line 924. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L924).

**The complex cross product map.** Cross product with a real vector is extended to a continuous complex linear map. Source: Breakdown.Freq.Internal.NiceApprox.crossC in Breakdown.FreqTr.NiceApprox, line 933. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L933).

**Evaluate the complex cross product.** The complex cross product map has the displayed three component formula. Source: Breakdown.Freq.Internal.NiceApprox.crossC_apply in Breakdown.FreqTr.NiceApprox, line 944. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L944).

**Complexification respects cross products.** Complexifying a real cross product equals applying the complex cross product to the complexified vector. Source: Breakdown.Freq.Internal.NiceApprox.complexify_crossL in Breakdown.FreqTr.NiceApprox, line 947. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L947).

**A Fourier vector potential.** The potential symbol is the imaginary cross product with frequency divided by four pi squared times the cubed radius. Source: Breakdown.Freq.Internal.NiceApprox.potentialSymbol in Breakdown.FreqTr.NiceApprox, line 951. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L951).

**The potential symbol is symmetric.** The potential symbol of a nice symbol satisfies conjugate symmetry. Source: Breakdown.Freq.Internal.NiceApprox.potentialSymbol_conjSym in Breakdown.FreqTr.NiceApprox, line 954. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L954).

**The potential symbol is smooth.** The potential symbol of a nice symbol is smooth, including the region where the original symbol vanishes near zero. Source: Breakdown.Freq.Internal.NiceApprox.potentialSymbol_contDiff in Breakdown.FreqTr.NiceApprox, line 961. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L961).

**The potential symbol has compact support.** The potential symbol of a nice symbol has compact support. Source: Breakdown.Freq.Internal.NiceApprox.potentialSymbol_hasCompactSupport in Breakdown.FreqTr.NiceApprox, line 991. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L991).

**A curl potential recovers the symbol.** At nonzero frequency, applying the curl and embedding multipliers to the potential symbol recovers the original nice symbol. Source: Breakdown.Freq.Internal.NiceApprox.potential_algebra in Breakdown.FreqTr.NiceApprox, line 995. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L995).

**Represent a nice symbol by a curl.** Every nice symbol is the weighted Fourier transform of the curl of a real Schwartz potential away from zero. Source: Breakdown.Freq.Internal.NiceApprox.symbol_curl_freqTr in Breakdown.FreqTr.NiceApprox, line 1026. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L1026).

**Represent the symbol and its Laplacian.** One real Schwartz potential represents both the nice symbol and its Laplacian weighted symbol through its curl. Source: Breakdown.Freq.Internal.NiceApprox.symbol_rapid in Breakdown.FreqTr.NiceApprox, line 1067. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L1067).

**Embed the Schwartz curl representation.** Every nice symbol and its Laplacian multiple are represented almost everywhere by embeddings of one Schwartz curl and its negative Laplacian. Source: Breakdown.Freq.Internal.NiceApprox.symbol_curl_embed in Breakdown.FreqTr.NiceApprox, line 1078. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceApprox.lean#L1078).

### Breakdown.FreqTr.NiceDense

Frequency cutoffs and symmetry-preserving smoothing make nice annular symbols dense simultaneously in a state and its Laplacian component.

**Source namespace:** Breakdown.Freq.Internal.NiceDense.

**The small and large frequency tails.** The outer set is the union of a shrinking ball around zero and the complement of a growing ball. Source: Breakdown.Freq.Internal.NiceDense.outerSet in Breakdown.FreqTr.NiceDense, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L12).

**Remove the longitudinal component.** The projected field subtracts the longitudinal projection from each symbol value. Source: Breakdown.Freq.Internal.NiceDense.projField in Breakdown.FreqTr.NiceDense, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L14).

**Enforce conjugate symmetry.** The symmetrised field averages each value with the conjugate value at the negative frequency. Source: Breakdown.Freq.Internal.NiceDense.symField in Breakdown.FreqTr.NiceDense, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L16).

**A bound after complexification.** The longitudinal operator norm is bounded by the square of the complexification operator norm. Source: Breakdown.Freq.Internal.NiceDense.norm_longitudinal_le in Breakdown.FreqTr.NiceDense, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L18).

**Measurability of longitudinal projection.** The longitudinal projection is almost everywhere strongly measurable. Source: Breakdown.Freq.Internal.NiceDense.aestronglyMeasurable_longitudinal in Breakdown.FreqTr.NiceDense, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L38).

**Almost everywhere state constraints.** Each state symbol satisfies conjugate reflection symmetry and zero longitudinal component almost everywhere. Source: Breakdown.Freq.Internal.NiceDense.sig_ae in Breakdown.FreqTr.NiceDense, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L52).

**Small L2 mass in the frequency tails.** The L2 norm of the shrinking low frequency and receding high frequency tails eventually falls below every positive tolerance. Source: Breakdown.Freq.Internal.NiceDense.tail_small in Breakdown.FreqTr.NiceDense, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L80).

**Approximate inside a frequency annulus.** An annularly supported L2 field has a smooth approximation supported in a slightly larger annulus with arbitrarily small L2 error. Source: Breakdown.Freq.Internal.NiceDense.smooth_annulus in Breakdown.FreqTr.NiceDense, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L130).

**The frequency inner product formula.** Pairing with the complex frequency vector is the coordinate contraction with the real frequency. Source: Breakdown.Freq.Internal.NiceDense.inner_freqVec in Breakdown.FreqTr.NiceDense, line 182. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L182).

**The frequency vector preserves radius.** The complex frequency vector norm equals the real frequency radius. Source: Breakdown.Freq.Internal.NiceDense.norm_freqVec in Breakdown.FreqTr.NiceDense, line 186. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L186).

**The explicit longitudinal formula.** The longitudinal projection is the normalized frequency inner product times the frequency vector. Source: Breakdown.Freq.Internal.NiceDense.longitudinal_eq in Breakdown.FreqTr.NiceDense, line 189. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L189).

**The projected vector is transverse.** Removing the longitudinal component gives a vector orthogonal to frequency. Source: Breakdown.Freq.Internal.NiceDense.inner_freqVec_proj in Breakdown.FreqTr.NiceDense, line 193. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L193).

**Projection does not enlarge norm.** The solenoidal projection has norm at most that of the original vector. Source: Breakdown.Freq.Internal.NiceDense.norm_proj_le in Breakdown.FreqTr.NiceDense, line 203. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L203).

**The projected symbol has zero divergence.** The coordinate contraction of the projected vector with frequency is zero. Source: Breakdown.Freq.Internal.NiceDense.div_proj in Breakdown.FreqTr.NiceDense, line 213. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L213).

**Projection preserves annular smoothness.** A smooth symbol vanishing near zero remains smooth after removing its longitudinal component. Source: Breakdown.Freq.Internal.NiceDense.contDiff_projField in Breakdown.FreqTr.NiceDense, line 217. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L217).

**Conjugation preserves vector norm.** Vector conjugation preserves the norm. Source: Breakdown.Freq.Internal.NiceDense.norm_conjVec in Breakdown.FreqTr.NiceDense, line 243. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L243).

**Symmetrisation improves the L2 error.** Conjugate symmetrisation does not increase the L2 distance to an almost everywhere symmetric target. Source: Breakdown.Freq.Internal.NiceDense.eLpNorm_symField_sub_le in Breakdown.FreqTr.NiceDense, line 246. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L246).

**Bound the band limited Laplacian.** For a symbol supported below a fixed radius, its Laplacian weighted L2 norm is bounded by four pi squared times the radius squared times its L2 norm. Source: Breakdown.Freq.Internal.NiceDense.eLpNorm_ssp_le in Breakdown.FreqTr.NiceDense, line 276. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L276).

**Conjugation is its own inverse.** Applying vector conjugation twice returns the original vector. Source: Breakdown.Freq.Internal.NiceDense.conjVec_conjVec in Breakdown.FreqTr.NiceDense, line 292. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L292).

**Construct a nice annular symbol.** Solenoidal projection followed by symmetrisation turns a smooth annular symbol into a nice symbol while retaining the outer support bound. Source: Breakdown.Freq.Internal.NiceDense.nice_symField_projField in Breakdown.FreqTr.NiceDense, line 296. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L296).

**Source namespace:** Breakdown.Freq.

**Prove graph density of nice symbols.** The theorem proves nice symbols approximate every Laplacian related pair in both components of its graph norm. Source: Breakdown.Freq.niceDense in Breakdown.FreqTr.NiceDense, line 328. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/NiceDense.lean#L328).

### Breakdown.FreqTr.PairingByParts

Coordinate integration by parts transfers a test gradient pairing to the negative Laplacian of the test field.

**Source namespace:** Breakdown.Freq.Internal.PairingByParts.

**Smooth directional derivative fields.** The derivative of a smooth field in a fixed direction is smooth. Source: Breakdown.Freq.Internal.PairingByParts.dirDeriv_contDiff in Breakdown.FreqTr.PairingByParts, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingByParts.lean#L12).

**Integrability from one compact factor.** The pairing of two continuous fields is integrable when the second has compact support. Source: Breakdown.Freq.Internal.PairingByParts.integrable_inner_of_compact in Breakdown.FreqTr.PairingByParts, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingByParts.lean#L16).

**The diagonal second derivative formula.** The second iterated derivative on a repeated direction equals the twice differentiated directional field. Source: Breakdown.Freq.Internal.PairingByParts.iteratedFDeriv_two_diag in Breakdown.FreqTr.PairingByParts, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingByParts.lean#L21).

**Two derivatives by parts.** The pairing of two directional derivatives equals the negative pairing against the second derivative when the test is compactly supported. Source: Breakdown.Freq.Internal.PairingByParts.coord_ibp in Breakdown.FreqTr.PairingByParts, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingByParts.lean#L28).

**Source namespace:** Breakdown.Freq.

**Prove the gradient pairing identity.** The theorem discharges integration by parts from the gradient pairing to the negative Laplacian field pairing. Source: Breakdown.Freq.pairingByParts in Breakdown.FreqTr.PairingByParts, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingByParts.lean#L51).

### Breakdown.FreqTr.PairingEmbed

Polarization of the embedding norm identity recovers the physical gradient pairing from the state inner product.

**Source namespace:** Breakdown.Freq.Internal.PairingEmbed.

**Add two decay fields.** The sum of two decay fields is a decay field. Source: Breakdown.Freq.Internal.PairingEmbed.decayField_add in Breakdown.FreqTr.PairingEmbed, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingEmbed.lean#L12).

**Subtract two decay fields.** The difference of two decay fields is a decay field. Source: Breakdown.Freq.Internal.PairingEmbed.decayField_sub in Breakdown.FreqTr.PairingEmbed, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingEmbed.lean#L33).

**A squared derivative is integrable.** The square norm of each coordinate derivative of a decay field is integrable. Source: Breakdown.Freq.Internal.PairingEmbed.integrable_sq_fderiv in Breakdown.FreqTr.PairingEmbed, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingEmbed.lean#L54).

**Integrability of the gradient square sum.** The finite sum of squared coordinate derivative norms of a decay field is integrable. Source: Breakdown.Freq.Internal.PairingEmbed.integrable_sum_sq_fderiv in Breakdown.FreqTr.PairingEmbed, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingEmbed.lean#L79).

**Source namespace:** Breakdown.Freq.

**Recover the physical gradient pairing.** The norm and linearity interfaces identify the state inner product of two embeddings with their physical gradient pairing. Source: Breakdown.Freq.pairingEmbed in Breakdown.FreqTr.PairingEmbed, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PairingEmbed.lean#L86).

### Breakdown.FreqTr.PartialDecay

Coordinate derivative multipliers recover classical derivatives of decay fields and give the summed square-norm bound for general states.

**Source namespace:** Breakdown.Freq.Internal.PartialDecay.

**Taking real parts contracts the norm.** The real vector part has norm no greater than the complex vector. Source: Breakdown.Freq.Internal.PartialDecay.norm_realVec_apply_le in Breakdown.FreqTr.PartialDecay, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L12).

**The Fourier L2 square norm integral.** The squared L2 norm equals the integral of the representative's squared norm. Source: Breakdown.Freq.Internal.PartialDecay.l2_norm_sq in Breakdown.FreqTr.PartialDecay, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L21).

**The coordinate norm square identity.** The squared spatial norm equals the sum of the three coordinate squares. Source: Breakdown.Freq.Internal.PartialDecay.norm_sq_space in Breakdown.FreqTr.PartialDecay, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L27).

**Almost every frequency is nonzero.** The zero frequency has volume measure zero. Source: Breakdown.Freq.Internal.PartialDecay.ae_ne_zero in Breakdown.FreqTr.PartialDecay, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L31).

**A coordinate is bounded by the norm.** The absolute value of each spatial coordinate is at most the vector norm. Source: Breakdown.Freq.Internal.PartialDecay.abs_coord_le in Breakdown.FreqTr.PartialDecay, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L36).

**Norm of the derivative multiplier.** The derivative symbol norm is the absolute frequency coordinate divided by the frequency radius. Source: Breakdown.Freq.Internal.PartialDecay.norm_derivSymbol in Breakdown.FreqTr.PartialDecay, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L43).

**Norm of the embedding multiplier.** The gradient embedding symbol norm is the absolute frequency coordinate divided by the radius. Source: Breakdown.Freq.Internal.PartialDecay.norm_gradSymbol in Breakdown.FreqTr.PartialDecay, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L46).

**A normalized coordinate is at most one.** The absolute coordinate divided by the vector norm is at most one. Source: Breakdown.Freq.Internal.PartialDecay.coord_div_le_one in Breakdown.FreqTr.PartialDecay, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L49).

**Apply a complex scalar operator.** The multiplication operator acts by complex scalar multiplication. Source: Breakdown.Freq.Internal.PartialDecay.cmul_apply in Breakdown.FreqTr.PartialDecay, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L52).

**The scalar bounds the operator norm.** The complex multiplication operator norm is at most the scalar norm. Source: Breakdown.Freq.Internal.PartialDecay.norm_cmul_le in Breakdown.FreqTr.PartialDecay, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L54).

**The scalar multiplier map is continuous.** Complex multiplication operators vary continuously with the scalar. Source: Breakdown.Freq.Internal.PartialDecay.continuous_cmul in Breakdown.FreqTr.PartialDecay, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L57).

**Measurability of derivative recovery.** The derivative recovery symbol is measurable. Source: Breakdown.Freq.Internal.PartialDecay.measurable_derivSymbol in Breakdown.FreqTr.PartialDecay, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L63).

**Measurability of gradient embedding.** The gradient embedding symbol is measurable. Source: Breakdown.Freq.Internal.PartialDecay.measurable_gradSymbol in Breakdown.FreqTr.PartialDecay, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L67).

**The partial field is square integrable.** Each partial derivative of a decay field belongs to L2. Source: Breakdown.Freq.Internal.PartialDecay.memLp_partialField in Breakdown.FreqTr.PartialDecay, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L71).

**Invert the compatible gradient symbols.** The algebraic compatibility and norm square identities make the derivative symbol recover the selected gradient component. Source: Breakdown.Freq.Internal.PartialDecay.symbol_identity in Breakdown.FreqTr.PartialDecay, line 91. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L91).

**Real parts reverse complex inclusion.** Taking real parts of a complexified real vector returns the original vector. Source: Breakdown.Freq.Internal.PartialDecay.realVec_complexifyVec in Breakdown.FreqTr.PartialDecay, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L104).

**Undo the physical Fourier round trip.** The physical inverse transform of a complexified Fourier transform equals the original real field almost everywhere. Source: Breakdown.Freq.Internal.PartialDecay.toPhys_freqTr_complexify in Breakdown.FreqTr.PartialDecay, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L108).

**The L2 representative matches its input.** For a square integrable input, the L2 conversion equals that input almost everywhere. Source: Breakdown.Freq.Internal.PartialDecay.toLpOrZero_ae in Breakdown.FreqTr.PartialDecay, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L118).

**Read the scalar symbol multiplier.** A measurable scalar symbol bounded by one acts by pointwise multiplication almost everywhere. Source: Breakdown.Freq.Internal.PartialDecay.symbolOp_ae in Breakdown.FreqTr.PartialDecay, line 124. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L124).

**Physical recovery is contractive on L2.** The real physical inverse transform does not increase the L2 norm. Source: Breakdown.Freq.Internal.PartialDecay.norm_toPhys_le in Breakdown.FreqTr.PartialDecay, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L131).

**The representative square is integrable.** The squared norm of an L2 representative is integrable. Source: Breakdown.Freq.Internal.PartialDecay.integrable_norm_sq in Breakdown.FreqTr.PartialDecay, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L140).

**The derivative square sum is at most one.** The sum of squared derivative symbol norms is at most one. Source: Breakdown.Freq.Internal.PartialDecay.sum_norm_derivSymbol_sq_le in Breakdown.FreqTr.PartialDecay, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L143).

**Prove the recovered derivative bound.** Multiplier realization gives the bound on the sum of squared recovered derivative norms. Source: Breakdown.Freq.Internal.PartialDecay.partialNormLe_of in Breakdown.FreqTr.PartialDecay, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L148).

**Recover classical decay derivatives.** The realization, gradient compatibility and embedding membership interfaces identify recovered derivatives with classical decay field derivatives. Source: Breakdown.Freq.Internal.PartialDecay.partialDecay_of in Breakdown.FreqTr.PartialDecay, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L172).

**Source namespace:** Breakdown.Freq.

**Prove derivative recovery and its bound.** The theorem supplies both the physical derivative recovery interface and its squared norm estimate. Source: Breakdown.Freq.partialDecayNorm in Breakdown.FreqTr.PartialDecay, line 219. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/PartialDecay.lean#L219).

### Breakdown.FreqTr.Phi

The smoothed derivative multiplier is realized as a velocity and satisfies the L2 and L6 heat-smoothing estimates.

**Source namespace:** Breakdown.Freq.Internal.Phi.

**A realized operator or its zero default.** The chosen field operator either satisfies its realization formula or equals zero. Source: Breakdown.Freq.Internal.Phi.fieldOp_realized_or_zero in Breakdown.FreqTr.Phi, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L12).

**The continuous scalar multiplier formula.** A bounded continuous scalar multiplier has the expected almost everywhere pointwise formula. Source: Breakdown.Freq.Internal.Phi.scalarOp_ae in Breakdown.FreqTr.Phi, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L19).

**Bound a scalar multiplier output.** A uniform bound on the scalar symbol bounds the output norm by that constant times the input norm. Source: Breakdown.Freq.Internal.Phi.scalarOp_norm_le in Breakdown.FreqTr.Phi, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L36).

**Even multipliers keep state symbols.** A bounded continuous even real multiplier preserves the symbol subspace. Source: Breakdown.Freq.Internal.Phi.scalarOp_mem in Breakdown.FreqTr.Phi, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L44).

**An exponential damping bound.** A real number times its negative exponential is at most one. Source: Breakdown.Freq.Internal.Phi.mul_exp_neg_le_one in Breakdown.FreqTr.Phi, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L84).

**Separate the heat Laplacian scale.** At positive time the heat Laplacian factor is reciprocal time times the normalized exponential expression. Source: Breakdown.Freq.Internal.Phi.sspHeat_eq in Breakdown.FreqTr.Phi, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L90).

**The heat Laplacian factor is nonnegative.** The product of the Laplacian factor and heat factor is nonnegative. Source: Breakdown.Freq.Internal.Phi.sspHeat_nonneg in Breakdown.FreqTr.Phi, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L97).

**The heat Laplacian factor bound.** At positive time the absolute heat Laplacian factor is at most reciprocal time. Source: Breakdown.Freq.Internal.Phi.sspHeat_le in Breakdown.FreqTr.Phi, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L101).

**The smoothing factor is nonnegative.** The derivative heat factor is nonnegative. Source: Breakdown.Freq.Internal.Phi.phiFactor_nonneg in Breakdown.FreqTr.Phi, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L109).

**The squared smoothing factor bound.** At positive time the squared derivative heat factor is at most reciprocal time. Source: Breakdown.Freq.Internal.Phi.phiFactor_sq_le in Breakdown.FreqTr.Phi, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L113).

**The inverse square root time bound.** At positive time the absolute derivative heat factor is bounded by time to the power negative one half. Source: Breakdown.Freq.Internal.Phi.phiFactor_le in Breakdown.FreqTr.Phi, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L128).

**The heat scalar has unit bound.** The absolute heat factor is at most one. Source: Breakdown.Freq.Internal.Phi.heatFactor_le in Breakdown.FreqTr.Phi, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L133).

**The smoothing scalar is continuous.** The derivative heat factor is continuous in frequency. Source: Breakdown.Freq.Internal.Phi.continuous_phiFactor in Breakdown.FreqTr.Phi, line 140. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L140).

**The heat scalar is continuous.** The heat factor is continuous in frequency. Source: Breakdown.Freq.Internal.Phi.continuous_heatFactor in Breakdown.FreqTr.Phi, line 144. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L144).

**The heat Laplacian scalar is continuous.** The product of the Laplacian and heat factors is continuous in frequency. Source: Breakdown.Freq.Internal.Phi.continuous_sspHeat in Breakdown.FreqTr.Phi, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L148).

**Source namespace:** Breakdown.Freq.

**Smoothing bounds and velocity identity.** The theorem supplies the L2 and L6 smoothing estimates and the relation to velocity of a heated Laplacian state. Source: Breakdown.Freq.phiBoundsVelocity in Breakdown.FreqTr.Phi, line 155. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Phi.lean#L155).

### Breakdown.FreqTr.Realization

The proved Fourier interfaces are assembled into the concrete realization used by the abstract evolution and profile arguments.

**Source namespace:** Breakdown.Freq.

**Prove embedding membership.** The theorem discharges embedding membership using the completed Fourier realization proofs. Source: Breakdown.Freq.embedMem_holds in Breakdown.FreqTr.Realization, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L60).

**Close the embedding Laplacian proof.** The theorem discharges compatibility of the embedding with the physical negative Laplacian. Source: Breakdown.Freq.embedNegSsp_holds in Breakdown.FreqTr.Realization, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L66).

**Close half Laplacian velocity inversion.** The theorem discharges the interface identifying velocity with inverse transformation of a half Laplacian predecessor. Source: Breakdown.Freq.velocityInverts_holds in Breakdown.FreqTr.Realization, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L86).

**Close both velocity covariance proofs.** The theorem supplies both rotation covariance and positive dilation covariance of velocity recovery. Source: Breakdown.Freq.velocityCov_holds in Breakdown.FreqTr.Realization, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L103).

**Close the weak state equation proof.** The theorem discharges the weak equation expressed in the Fourier state space. Source: Breakdown.Freq.weak_holds in Breakdown.FreqTr.Realization, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L121).

**Close the H1 bilinear formula proof.** The theorem discharges the physical H1 advection formula for the bilinear interaction. Source: Breakdown.Freq.bilinH1Formula_holds in Breakdown.FreqTr.Realization, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Realization.lean#L148).

### Breakdown.FreqTr.Rotation

Orthogonal frequency changes realize state rotations and prove their norm, composition, heat and dilation compatibility.

**Source namespace:** Breakdown.Freq.Internal.Rotation.

**Coordinates of complex rotation.** Each complex rotated coordinate is the rotation matrix row paired with the original complex vector. Source: Breakdown.Freq.Internal.Rotation.rotC_apply in Breakdown.FreqTr.Rotation, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L12).

**Coordinates of real rotation.** Each real rotated coordinate is the corresponding rotation matrix row paired with the original vector. Source: Breakdown.Freq.Internal.Rotation.apply_eq_sum in Breakdown.FreqTr.Rotation, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L15).

**The inverse rotation is the transpose.** The coordinate matrix of the inverse isometry is the transpose of the original isometry's matrix. Source: Breakdown.Freq.Internal.Rotation.symm_unit in Breakdown.FreqTr.Rotation, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L22).

**Inverse complex rotations cancel.** Composing the complex rotation with its inverse gives the original vector. Source: Breakdown.Freq.Internal.Rotation.rotC_rotC_symm in Breakdown.FreqTr.Rotation, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L30).

**The adjoint complex rotation.** Moving complex rotation across an inner product replaces it with the inverse rotation. Source: Breakdown.Freq.Internal.Rotation.rotC_inner in Breakdown.FreqTr.Rotation, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L48).

**Complex rotation preserves norm.** The induced complex vector rotation is an isometry. Source: Breakdown.Freq.Internal.Rotation.norm_rotC in Breakdown.FreqTr.Rotation, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L57).

**Rotate a frequency vector.** Rotating the complex frequency vector equals complexifying the rotated real frequency. Source: Breakdown.Freq.Internal.Rotation.rotC_freqVec in Breakdown.FreqTr.Rotation, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L68).

**Complex rotation respects scalars.** The induced vector rotation commutes with complex scalar multiplication. Source: Breakdown.Freq.Internal.Rotation.rotC_smul in Breakdown.FreqTr.Rotation, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L76).

**Move rotation through a pairing.** Pairing a rotated vector with frequency equals pairing the original vector with inverse rotated frequency. Source: Breakdown.Freq.Internal.Rotation.inner_freqVec_rotC in Breakdown.FreqTr.Rotation, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L81).

**Rotate the longitudinal projection.** The longitudinal projection after rotation equals rotation of the projection at inverse rotated frequency. Source: Breakdown.Freq.Internal.Rotation.longitudinal_rotC in Breakdown.FreqTr.Rotation, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L87).

**Complex rotation preserves conjugation.** Vector conjugation commutes with the induced complex rotation. Source: Breakdown.Freq.Internal.Rotation.conjVec_rotC in Breakdown.FreqTr.Rotation, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L93).

**Transport almost everywhere equality.** Composition with a quasi measure preserving frequency map preserves almost everywhere equality. Source: Breakdown.Freq.Internal.Rotation.ae_comp in Breakdown.FreqTr.Rotation, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L97).

**Spatial isometries preserve null sets.** Every spatial linear isometry is quasi measure preserving for volume. Source: Breakdown.Freq.Internal.Rotation.qmp_liso in Breakdown.FreqTr.Rotation, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L102).

**Negation preserves null sets.** Frequency negation is quasi measure preserving for volume. Source: Breakdown.Freq.Internal.Rotation.qmp_neg in Breakdown.FreqTr.Rotation, line 105. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L105).

**Nonzero dilation preserves null sets.** Nonzero scalar dilation is quasi measure preserving for volume. Source: Breakdown.Freq.Internal.Rotation.qmp_smul in Breakdown.FreqTr.Rotation, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L108).

**The field operator's two branches.** The total field operator is either zero or a realization of its prescribed pointwise action. Source: Breakdown.Freq.Internal.Rotation.fieldOp_cases in Breakdown.FreqTr.Rotation, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L112).

**Realize the rotation formula.** The L2 rotation realizes inverse frequency rotation followed by rotation of vector values. Source: Breakdown.Freq.Internal.Rotation.rotL2_realized in Breakdown.FreqTr.Rotation, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L119).

**Realize reflected conjugation.** The reflected conjugation operator realizes frequency reflection followed by conjugation of values. Source: Breakdown.Freq.Internal.Rotation.reflConj_realized in Breakdown.FreqTr.Rotation, line 123. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L123).

**L2 rotation preserves norm.** The L2 rotation operator preserves the norm. Source: Breakdown.Freq.Internal.Rotation.norm_rotL2 in Breakdown.FreqTr.Rotation, line 127. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L127).

**Inverse L2 rotations cancel.** Composing an L2 rotation with its inverse gives the original L2 field. Source: Breakdown.Freq.Internal.Rotation.rotL2_rotL2_symm in Breakdown.FreqTr.Rotation, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L135).

**Rotation preserves the symbol subspace.** The L2 rotation preserves conjugate symmetry and zero longitudinal component. Source: Breakdown.Freq.Internal.Rotation.rot_mem_sig in Breakdown.FreqTr.Rotation, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L143).

**The linear rotation on states.** Restricting L2 rotation to its invariant symbol subspace defines a real linear state map. Source: Breakdown.Freq.Internal.Rotation.rotSig in Breakdown.FreqTr.Rotation, line 169. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L169).

**The state rotation isometry.** The norm preserving state rotation is packaged as a linear isometry. Source: Breakdown.Freq.Internal.Rotation.rotIso in Breakdown.FreqTr.Rotation, line 172. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L172).

**The invertible state rotation.** The surjective state isometry is packaged as a linear isometric equivalence. Source: Breakdown.Freq.Internal.Rotation.rotEquiv in Breakdown.FreqTr.Rotation, line 175. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L175).

**Read the constructed state rotation.** The constructed state rotation equivalence has the same ambient value as the L2 rotation. Source: Breakdown.Freq.Internal.Rotation.rotEquiv_apply in Breakdown.FreqTr.Rotation, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L179).

**Read the chosen state rotation.** The chosen state rotation agrees with L2 rotation on its underlying symbol. Source: Breakdown.Freq.Internal.Rotation.rotX_coe in Breakdown.FreqTr.Rotation, line 182. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L182).

**Rotation commutes with heat.** L2 rotation commutes with the heat operator. Source: Breakdown.Freq.Internal.Rotation.rotL2_heatL2 in Breakdown.FreqTr.Rotation, line 189. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L189).

**Rotation commutes with positive dilation.** L2 rotation commutes with dilation at a positive parameter. Source: Breakdown.Freq.Internal.Rotation.rotL2_dilL2 in Breakdown.FreqTr.Rotation, line 202. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L202).

**Source namespace:** Breakdown.Freq.

**Prove the rotation algebra.** The theorem supplies the ambient formula and commutation with heat and dilation for state rotations. Source: Breakdown.Freq.rotationAlgebra in Breakdown.FreqTr.Rotation, line 219. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Rotation.lean#L219).

### Breakdown.FreqTr.Statements

Proposition-valued interfaces record the analytic obligations for embedding, velocity recovery, heat smoothing, graph density and bilinear evolution.

**Source namespace:** Breakdown.Freq.

**Continuous state dilation.** This proposition requires state dilation to vary continuously on positive parameters for each state. Source: Breakdown.Freq.DilationContinuous in Breakdown.FreqTr.Statements, line 29. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L29).

**Rotation compatibility requirements.** This proposition requires the state rotation to have the L2 formula and commute with heat and dilation. Source: Breakdown.Freq.RotationAlgebra in Breakdown.FreqTr.Statements, line 31. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L31).

**Embedding membership requirement.** This proposition requires every decay field's gradient representation to belong to the symbol subspace. Source: Breakdown.Freq.EmbedMem in Breakdown.FreqTr.Statements, line 37. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L37).

**The embedding detects nonzero fields.** This proposition requires every nonzero decay field to have nonzero state embedding. Source: Breakdown.Freq.EmbedNeZero in Breakdown.FreqTr.Statements, line 47. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L47).

**Embedding respects spatial rotation.** This proposition requires rotation of an embedded decay field to equal the embedding of its pushforward. Source: Breakdown.Freq.EmbedRot in Breakdown.FreqTr.Statements, line 49. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L49).

**Embedding respects the Laplacian.** This proposition requires embedded test fields and their negative Laplacians to satisfy the state Laplacian relation. Source: Breakdown.Freq.EmbedNegSsp in Breakdown.FreqTr.Statements, line 55. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L55).

**Density in the Laplacian graph norm.** This proposition requires test embeddings to approximate both members of every Laplacian related state pair. Source: Breakdown.Freq.TestDenseGraph in Breakdown.FreqTr.Statements, line 57. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L57).

**The test span contains actual tests.** This proposition requires every vector in the span of test embeddings to itself be one test field's embedding. Source: Breakdown.Freq.TestSpanSpec in Breakdown.FreqTr.Statements, line 63. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L63).

**Existence of velocity recovery.** This proposition asks for a continuous velocity recovery map satisfying the test field specification. Source: Breakdown.Freq.VelocityExists in Breakdown.FreqTr.Statements, line 69. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L69).

**The recovered derivative square bound.** This proposition bounds the sum of squared recovered derivative norms by the original state norm squared. Source: Breakdown.Freq.PartialNormLe in Breakdown.FreqTr.Statements, line 77. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L77).

**Velocity inverts the half Laplacian.** This proposition identifies velocity of a half Laplacian state with the physical inverse transform of its predecessor almost everywhere. Source: Breakdown.Freq.VelocityInvertsHalfSsp in Breakdown.FreqTr.Statements, line 79. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L79).

**The interpolated trilinear bound.** This proposition requires integrability and a trilinear estimate using the geometric mean of the third field's L2 and L6 norms. Source: Breakdown.Freq.TrilinearBound in Breakdown.FreqTr.Statements, line 82. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L82).

**The two heat smoothing bounds.** This proposition requires the smoothed derivative to satisfy L2 and L6 bounds with time powers negative one half and negative one. Source: Breakdown.Freq.PhiBounds in Breakdown.FreqTr.Statements, line 89. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L89).

**The smoothed derivative is a velocity.** This proposition identifies derivative smoothing with the velocity of a state Laplacian of the heated input. Source: Breakdown.Freq.PhiVelocity in Breakdown.FreqTr.Statements, line 94. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L94).

**The bilinear time shift.** This proposition requires heat after bilinear interaction to add its nonnegative time to the positive interaction time. Source: Breakdown.Freq.BilinShift in Breakdown.FreqTr.Statements, line 103. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L103).

**Bilinear continuity in positive time.** This proposition requires the bilinear interaction of fixed states to be continuous on positive times. Source: Breakdown.Freq.BilinContinuous in Breakdown.FreqTr.Statements, line 106. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L106).

**The bilinear dilation identity.** This proposition requires the scaled interaction and two dilated inputs to agree with the displayed parameter factor. Source: Breakdown.Freq.BilinDilate in Breakdown.FreqTr.Statements, line 108. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L108).

**The bilinear rotation identity.** This proposition requires rotation to commute with the bilinear interaction. Source: Breakdown.Freq.BilinRotate in Breakdown.FreqTr.Statements, line 112. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L112).

**The state gradient pairing identity.** This proposition identifies the inner product of two embedded decay fields with their physical gradient pairing. Source: Breakdown.Freq.PairingEmbed in Breakdown.FreqTr.Statements, line 118. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L118).

**Integration by parts for the embedding.** This proposition identifies the gradient pairing against a test field with the pairing against its negative Laplacian. Source: Breakdown.Freq.PairingByParts in Breakdown.FreqTr.Statements, line 121. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L121).

**The physical advection pairing.** This proposition identifies advection against a test field with the trilinear self pairing of the embedded decay field. Source: Breakdown.Freq.AdvectionTrilinear in Breakdown.FreqTr.Statements, line 124. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L124).

**The weak equation in state space.** This proposition requires the embedded weak solution to satisfy the integrated linear plus trilinear test identity. Source: Breakdown.Freq.WeakInX in Breakdown.FreqTr.Statements, line 138. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L138).

**The concrete mild state equation.** The mild predicate combines continuity, Duhamel integrability and equality to heat evolution plus the bilinear time integral. Source: Breakdown.Freq.IsMildX in Breakdown.FreqTr.Statements, line 146. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L146).

**The transformed partial field.** The transformed partial field is the Fourier transform of the complexified L2 class of a coordinate derivative. Source: Breakdown.Freq.gradHat in Breakdown.FreqTr.Statements, line 154. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L154).

**Compatibility of transformed gradients.** This proposition requires crossed frequency coordinates of transformed gradient components to agree almost everywhere. Source: Breakdown.Freq.GradCompatible in Breakdown.FreqTr.Statements, line 156. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L156).

**Conjugate symmetry of real transforms.** This proposition requires the Fourier transform of every real L2 field to be fixed by reflected conjugation. Source: Breakdown.Freq.FreqTrConjSym in Breakdown.FreqTr.Statements, line 160. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L160).

**A smooth annular solenoidal symbol.** A nice symbol is smooth, compactly supported away from zero, conjugate symmetric and orthogonal to frequency. Source: Breakdown.Freq.IsNiceSymbol in Breakdown.FreqTr.Statements, line 162. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L162).

**Nice symbols are graph dense.** This proposition requires nice symbols to approximate a Laplacian related state pair in both L2 components. Source: Breakdown.Freq.NiceDense in Breakdown.FreqTr.Statements, line 166. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L166).

**Approximate nice symbols by test fields.** This proposition requires a test field embedding and its negative Laplacian embedding to approximate a nice symbol and its Laplacian multiple. Source: Breakdown.Freq.NiceApprox in Breakdown.FreqTr.Statements, line 171. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L171).

**Forward L1 and L2 consistency.** This proposition identifies the ordinary and L2 forward transforms almost everywhere for fields in both L1 and L2. Source: Breakdown.Freq.FreqTrL1L2 in Breakdown.FreqTr.Statements, line 176. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L176).

**Inverse L1 and L2 consistency.** This proposition identifies the ordinary and L2 inverse transforms almost everywhere for fields in both L1 and L2. Source: Breakdown.Freq.FreqTrInvL1L2 in Breakdown.FreqTr.Statements, line 180. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L180).

**Project onto the state symbol subspace.** The state projection is the orthogonal projection from ambient complex L2 onto the symbol subspace. Source: Breakdown.Freq.projX in Breakdown.FreqTr.Statements, line 184. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L184).

**The symmetrised test advection field.** The field sums the test velocity times state derivatives and state velocity times test derivatives, then takes its total L2 class. Source: Breakdown.Freq.advectTest in Breakdown.FreqTr.Statements, line 189. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L189).

**The interaction with an embedded test.** This proposition identifies interaction with an embedded test as negative one half the projected heat of symmetrised test advection. Source: Breakdown.Freq.BilinTestFormula in Breakdown.FreqTr.Statements, line 193. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L193).

**Velocity respects spatial rotation.** This proposition requires velocity after state rotation to equal the pushforward of the original velocity almost everywhere. Source: Breakdown.Freq.VelocityRotate in Breakdown.FreqTr.Statements, line 199. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L199).

**Velocity respects positive dilation.** This proposition requires velocity after positive state dilation to equal the corresponding physical dilation almost everywhere. Source: Breakdown.Freq.VelocityDilate in Breakdown.FreqTr.Statements, line 203. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Statements.lean#L203).

### Breakdown.FreqTr.StatementsBilinFormula

The H1 formula interface requires the abstract diagonal interaction to agree with negative projected heat of physical advection.

**Source namespace:** Breakdown.Freq.

**The H1 physical interaction formula.** This proposition identifies diagonal interaction of a bounded H1 field with negative projected heat of its physical advection. Source: Breakdown.Freq.BilinH1Formula in Breakdown.FreqTr.StatementsBilinFormula, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/StatementsBilinFormula.lean#L10).

### Breakdown.FreqTr.StatementsExport

The exported solenoidal H1 predicate fixes the smoothness, zero-divergence and square-integrability requirements for physical velocity and derivatives.

**Source namespace:** Breakdown.Freq.

**The smooth solenoidal H1 class.** The H1 field predicate requires smoothness, zero divergence, square integrable velocity and square integrable coordinate derivatives. Source: Breakdown.Freq.IsH1Field in Breakdown.FreqTr.StatementsExport, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/StatementsExport.lean#L10).

### Breakdown.FreqTr.TestDense

Nice-symbol approximation is converted into simultaneous test approximation of Laplacian-related states and density of the test span.

**Source namespace:** Breakdown.Freq.Internal.TestDense.

**The total operator branch distinction.** The chosen field operator is zero or realizes its specified pointwise formula. Source: Breakdown.Freq.Internal.TestDense.fieldOp_eq_zero_or_realized in Breakdown.FreqTr.TestDense, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L12).

**Negation transports almost equality.** Frequency negation preserves almost everywhere equality. Source: Breakdown.Freq.Internal.TestDense.ae_comp_neg in Breakdown.FreqTr.TestDense, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L19).

**Even rescaling keeps symbol constraints.** An almost everywhere even real multiple of a state symbol belongs to the symbol subspace. Source: Breakdown.Freq.Internal.TestDense.mem_sig_of_ae in Breakdown.FreqTr.TestDense, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L23).

**Bounded scalar factors preserve L2.** A bounded measurable real scalar factor times an L2 field remains square integrable. Source: Breakdown.Freq.Internal.TestDense.memLp_smul_of_bounded in Breakdown.FreqTr.TestDense, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L59).

**The norm of a class minus a field.** The L2 norm of the class difference equals the real value of the extended L2 norm of their representative difference. Source: Breakdown.Freq.Internal.TestDense.norm_sub_toLp in Breakdown.FreqTr.TestDense, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L66).

**The norm of a field minus a class.** The reversed L2 difference is also read as the extended L2 norm of its representative difference. Source: Breakdown.Freq.Internal.TestDense.norm_toLp_sub in Breakdown.FreqTr.TestDense, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L74).

**Continuity of the Laplacian factor.** The Laplacian frequency factor is continuous. Source: Breakdown.Freq.Internal.TestDense.continuous_sspFactor in Breakdown.FreqTr.TestDense, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L82).

**Combine the two graph approximations.** Nice symbol density and test approximation together give density of test fields in the Laplacian graph norm. Source: Breakdown.Freq.Internal.TestDense.testDenseGraph_of in Breakdown.FreqTr.TestDense, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L85).

**A radial cutoff preserves evenness.** Restricting an even scalar function to a closed ball centered at zero preserves evenness. Source: Breakdown.Freq.Internal.TestDense.closedBall_indicator_even in Breakdown.FreqTr.TestDense, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L114).

**The Laplacian factor is even.** Frequency negation leaves the Laplacian factor unchanged. Source: Breakdown.Freq.Internal.TestDense.sspFactor_neg in Breakdown.FreqTr.TestDense, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L119).

**Graph density implies state density.** Density in the Laplacian graph norm implies density of the span of embedded test fields in the state space. Source: Breakdown.Freq.Internal.TestDense.testDense_of in Breakdown.FreqTr.TestDense, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L122).

**Source namespace:** Breakdown.Freq.

**Prove both test density interfaces.** The theorem supplies both graph density of test fields and ordinary density of their span. Source: Breakdown.Freq.testDenseGraphDense in Breakdown.FreqTr.TestDense, line 180. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestDense.lean#L180).

### Breakdown.FreqTr.TestSpan

Closure of compact solenoidal tests under linear combinations identifies their embedded linear span with actual embedded test fields.

**Source namespace:** Breakdown.Freq.

**A test field is differentiable.** A test field is differentiable at every point. Source: Breakdown.Freq.diffAt_test in Breakdown.FreqTr.TestSpan, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestSpan.lean#L10).

**Test fields are closed under addition.** Adding two solenoidal test fields gives another solenoidal test field. Source: Breakdown.Freq.test_add in Breakdown.FreqTr.TestSpan, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestSpan.lean#L14).

**Test fields are closed under scaling.** Real scalar multiplication preserves the test field conditions. Source: Breakdown.Freq.test_smul in Breakdown.FreqTr.TestSpan, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestSpan.lean#L25).

**The zero field is a test field.** The zero vector field satisfies the test field conditions. Source: Breakdown.Freq.test_zero in Breakdown.FreqTr.TestSpan, line 34. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestSpan.lean#L34).

**Test fields have spatial decay.** Every test field satisfies the decay field conditions. Source: Breakdown.Freq.decay_of_test in Breakdown.FreqTr.TestSpan, line 39. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestSpan.lean#L39).

**Represent the whole test span.** Linearity of the embedding makes every vector in the test span the embedding of a single test field. Source: Breakdown.Freq.testSpanSpec in Breakdown.FreqTr.TestSpan, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/TestSpan.lean#L73).

### Breakdown.FreqTr.Trilinear

Hölder and interpolation estimates make the recovered-velocity trilinear form integrable and quantitatively bounded.

**Source namespace:** Breakdown.Freq.Internal.Trilinear.

**Bound a trilinear coordinate sum.** The absolute coordinate sum is bounded by the sum of the products of the three vector norms. Source: Breakdown.Freq.Internal.Trilinear.norm_sum_le_pointwise in Breakdown.FreqTr.Trilinear, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Trilinear.lean#L12).

**The extended norm coordinate bound.** The same coordinate product estimate holds for extended nonnegative norms. Source: Breakdown.Freq.Internal.Trilinear.enorm_sum_le_pointwise in Breakdown.FreqTr.Trilinear, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Trilinear.lean#L18).

**A three factor integral estimate.** Hölder and interpolation bound the triple product integral by the displayed L6, L2 and mixed L2/L6 factors. Source: Breakdown.Freq.Internal.Trilinear.lintegral_mul_three_le in Breakdown.FreqTr.Trilinear, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Trilinear.lean#L27).

**The vector norm product estimate.** The integral of the three vector norms is bounded by the L6 first norm, L2 second norm and geometric mean of the third L2 and L6 norms. Source: Breakdown.Freq.Internal.Trilinear.lintegral_enorm_mul_three_le in Breakdown.FreqTr.Trilinear, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Trilinear.lean#L52).

**Source namespace:** Breakdown.Freq.

**Prove the trilinear estimate.** The recovered derivative norm bound yields integrability and the interpolated L2/L6 trilinear estimate. Source: Breakdown.Freq.trilinearBound in Breakdown.FreqTr.Trilinear, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/Trilinear.lean#L68).

### Breakdown.FreqTr.VelocityDecay

Approximation by compact tests extends the velocity recovery identity to every decay field.

**Source namespace:** Breakdown.Freq.Internal.VelocityDecay.

**Compact support gives weighted bounds.** A continuous compactly supported field admits a bound with every chosen polynomial radial decay weight. Source: Breakdown.Freq.Internal.VelocityDecay.weightBound in Breakdown.FreqTr.VelocityDecay, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityDecay.lean#L12).

**Test fields have the required decay.** Every solenoidal test field satisfies the decay field conditions. Source: Breakdown.Freq.Internal.VelocityDecay.isDecayField_of_isTestField in Breakdown.FreqTr.VelocityDecay, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityDecay.lean#L28).

**Subtracting preserves spatial decay.** The difference of two decay fields is a decay field. Source: Breakdown.Freq.Internal.VelocityDecay.isDecayField_sub in Breakdown.FreqTr.VelocityDecay, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityDecay.lean#L43).

**Source namespace:** Breakdown.Freq.

**Recover every decay field velocity.** The density, embedding and Sobolev interfaces extend velocity recovery from compact tests to all decay fields. Source: Breakdown.Freq.velocityDecay in Breakdown.FreqTr.VelocityDecay, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityDecay.lean#L69).

### Breakdown.FreqTr.VelocityExists

The bounded test-field recovery map is extended across the dense test span to construct the continuous L6 velocity operator.

**Source namespace:** Breakdown.Freq.Internal.VelocityExists.

**Differentiability of test fields.** Every test field is differentiable at each point. Source: Breakdown.Freq.Internal.VelocityExists.differentiableAt_of_isTestField in Breakdown.FreqTr.VelocityExists, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L12).

**Add solenoidal test fields.** The sum of two solenoidal test fields is a solenoidal test field. Source: Breakdown.Freq.Internal.VelocityExists.isTestField_add in Breakdown.FreqTr.VelocityExists, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L16).

**Subtract solenoidal test fields.** The difference of two solenoidal test fields is a solenoidal test field. Source: Breakdown.Freq.Internal.VelocityExists.isTestField_sub in Breakdown.FreqTr.VelocityExists, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L27).

**Scale a solenoidal test field.** Real scalar multiplication preserves the test field conditions. Source: Breakdown.Freq.Internal.VelocityExists.isTestField_smul in Breakdown.FreqTr.VelocityExists, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L38).

**A test field is a decay field.** Smooth compact support supplies the required spatial decay bounds. Source: Breakdown.Freq.Internal.VelocityExists.isDecayField_of_isTestField in Breakdown.FreqTr.VelocityExists, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L48).

**The conversion takes its valid branch.** For an Lp field, the total conversion equals the class constructed from its Lp membership proof. Source: Breakdown.Freq.Internal.VelocityExists.toLpOrZero_eq in Breakdown.FreqTr.VelocityExists, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L83).

**Lp conversion respects addition.** For inputs in Lp with exponent at least one, the total conversion respects addition. Source: Breakdown.Freq.Internal.VelocityExists.toLpOrZero_add in Breakdown.FreqTr.VelocityExists, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L88).

**Lp conversion respects subtraction.** For inputs in Lp with exponent at least one, the total conversion respects subtraction. Source: Breakdown.Freq.Internal.VelocityExists.toLpOrZero_sub in Breakdown.FreqTr.VelocityExists, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L93).

**Scalar multiplication in Lp.** For an Lp input with exponent at least one, the total conversion commutes with real scalar multiplication. Source: Breakdown.Freq.Internal.VelocityExists.toLpOrZero_smul in Breakdown.FreqTr.VelocityExists, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L98).

**The extension agrees on dense inputs.** The continuous extension of a bounded map from a dense subspace agrees with the original map on that subspace. Source: Breakdown.Freq.Internal.VelocityExists.extend_subtypeL_apply in Breakdown.FreqTr.VelocityExists, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L103).

**Source namespace:** Breakdown.Freq.

**Construct the velocity recovery map.** Test density, embedding linearity and the gradient Sobolev bound construct the continuous L6 velocity recovery map. Source: Breakdown.Freq.velocityExists in Breakdown.FreqTr.VelocityExists, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityExists.lean#L112).

### Breakdown.FreqTr.VelocityInjective

Laplacian test pairings and dense embeddings show that zero recovered velocity forces the Fourier state itself to vanish.

**Source namespace:** Breakdown.Freq.Internal.VelocityInjective.

**The Laplacian is a second trace.** The negative Laplacian is the negative diagonal trace of the second iterated derivative. Source: Breakdown.Freq.Internal.VelocityInjective.negSsp_eq in Breakdown.FreqTr.VelocityInjective, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L23).

**Continuity of a test Laplacian.** The negative Laplacian of a test field is continuous. Source: Breakdown.Freq.Internal.VelocityInjective.negSsp_continuous in Breakdown.FreqTr.VelocityInjective, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L28).

**Compact support of a test Laplacian.** The negative Laplacian of a test field has compact support. Source: Breakdown.Freq.Internal.VelocityInjective.negSsp_hasCompactSupport in Breakdown.FreqTr.VelocityInjective, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L33).

**Continuity of a test derivative.** Every coordinate derivative of a test field is continuous. Source: Breakdown.Freq.Internal.VelocityInjective.partialField_continuous in Breakdown.FreqTr.VelocityInjective, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L38).

**Compact support of a test derivative.** Every coordinate derivative of a test field has compact support. Source: Breakdown.Freq.Internal.VelocityInjective.partialField_hasCompactSupport in Breakdown.FreqTr.VelocityInjective, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L44).

**Decay of a test field.** Every test field satisfies the decay field conditions. Source: Breakdown.Freq.Internal.VelocityInjective.isDecayField_of_test in Breakdown.FreqTr.VelocityInjective, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L51).

**A pairing inherits compact support.** The inner product field has compact support when its first factor does. Source: Breakdown.Freq.Internal.VelocityInjective.hasCompactSupport_inner_left in Breakdown.FreqTr.VelocityInjective, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L83).

**The repeated directional derivative.** Two derivatives in one fixed direction equal the second iterated derivative on that repeated direction. Source: Breakdown.Freq.Internal.VelocityInjective.second_partial_eq in Breakdown.FreqTr.VelocityInjective, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L87).

**Integrate one test derivative by parts.** The integral of matching coordinate derivatives equals the negative pairing against the second derivative of the test. Source: Breakdown.Freq.Internal.VelocityInjective.ibp_one in Breakdown.FreqTr.VelocityInjective, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L94).

**The full test gradient by parts.** The summed gradient pairing of two test fields equals the field pairing with the negative Laplacian of the second. Source: Breakdown.Freq.Internal.VelocityInjective.ibp_test in Breakdown.FreqTr.VelocityInjective, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L122).

**The complex multiplication formula.** Complex multiplication is the scalar multiple of the complex identity restricted to real scalars. Source: Breakdown.Freq.Internal.VelocityInjective.cmul_eq in Breakdown.FreqTr.VelocityInjective, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L146).

**Continuity of the multiplication formula.** The complex multiplication map is continuous in its scalar. Source: Breakdown.Freq.Internal.VelocityInjective.cmul_continuous in Breakdown.FreqTr.VelocityInjective, line 149. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L149).

**The multiplication norm estimate.** The complex multiplication operator norm is bounded by the scalar norm. Source: Breakdown.Freq.Internal.VelocityInjective.norm_cmul_le in Breakdown.FreqTr.VelocityInjective, line 152. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L152).

**Bound the gradient embedding factor.** The gradient embedding symbol has norm at most one. Source: Breakdown.Freq.Internal.VelocityInjective.norm_gradSymbol_le in Breakdown.FreqTr.VelocityInjective, line 156. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L156).

**Measurability of the gradient factor.** The gradient embedding symbol is measurable. Source: Breakdown.Freq.Internal.VelocityInjective.gradSymbol_measurable in Breakdown.FreqTr.VelocityInjective, line 162. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L162).

**Realize the gradient multiplier.** The chosen gradient multiplier satisfies its almost everywhere realization specification. Source: Breakdown.Freq.Internal.VelocityInjective.realized_grad in Breakdown.FreqTr.VelocityInjective, line 165. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L165).

**The gradient embedding representative.** The embedded gradient has the displayed sum of transformed coordinate derivative terms almost everywhere. Source: Breakdown.Freq.Internal.VelocityInjective.ofGrad_ae in Breakdown.FreqTr.VelocityInjective, line 171. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L171).

**Pair two gradient symbols.** The conjugate product of two gradient symbols is the product of their frequency coordinates divided by the squared radius. Source: Breakdown.Freq.Internal.VelocityInjective.gradSymbol_pair in Breakdown.FreqTr.VelocityInjective, line 184. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L184).

**Pair compatible gradient sums.** At nonzero frequency, pairing the embedded gradient sums reduces to the sum of component pairings under the compatibility condition. Source: Breakdown.Freq.Internal.VelocityInjective.inner_grad_sum in Breakdown.FreqTr.VelocityInjective, line 192. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L192).

**Complex inclusion preserves real pairing.** The real part of the complex inner product of two real inclusions equals their real inner product. Source: Breakdown.Freq.Internal.VelocityInjective.complexifyVec_inner in Breakdown.FreqTr.VelocityInjective, line 220. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L220).

**The real inner product inside complex L2.** The real L2 inner product is the real part of the complex L2 inner product. Source: Breakdown.Freq.Internal.VelocityInjective.l2c_real_inner in Breakdown.FreqTr.VelocityInjective, line 224. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L224).

**Complexification keeps the L2 pairing.** Complexifying both real L2 fields preserves their real inner product. Source: Breakdown.Freq.Internal.VelocityInjective.complexify_inner in Breakdown.FreqTr.VelocityInjective, line 228. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L228).

**The Fourier map keeps real pairings.** Applying the Fourier transform to both L2 inputs preserves their real inner product. Source: Breakdown.Freq.Internal.VelocityInjective.freqTrR_inner in Breakdown.FreqTr.VelocityInjective, line 237. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L237).

**The Fourier gradient inner product.** The inner product of two gradient representations equals the sum of integrals of their physical partial derivative pairings. Source: Breakdown.Freq.Internal.VelocityInjective.inner_ofGrad in Breakdown.FreqTr.VelocityInjective, line 241. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L241).

**The state Laplacian test pairing.** The inner product of two test embeddings equals the physical pairing of the first test with the negative Laplacian of the second. Source: Breakdown.Freq.Internal.VelocityInjective.pairing_test in Breakdown.FreqTr.VelocityInjective, line 269. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L269).

**Read the L6 class of a test field.** The L6 class obtained from a test field agrees with that field almost everywhere. Source: Breakdown.Freq.Internal.VelocityInjective.toLp6_test in Breakdown.FreqTr.VelocityInjective, line 288. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L288).

**Source namespace:** Breakdown.Freq.

**Prove velocity recovery is injective.** Test density and the physical pairing identities show that a state with zero velocity is zero. Source: Breakdown.Freq.velocityInjective in Breakdown.FreqTr.VelocityInjective, line 296. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInjective.lean#L296).

### Breakdown.FreqTr.VelocityInvert

Fourier pairing identities identify recovered velocity with inverse transformation of the state preceding a half Laplacian.

**Source namespace:** Breakdown.Freq.Internal.VelocityInvert.

**Pointwise complexification of a field.** The complex field includes each real vector value into complex space. Source: Breakdown.Freq.Internal.VelocityInvert.cplxField in Breakdown.FreqTr.VelocityInvert, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L14).

**Complexification preserves smoothness.** Pointwise complexification of a smooth real field is smooth. Source: Breakdown.Freq.Internal.VelocityInvert.cplxField_contDiff in Breakdown.FreqTr.VelocityInvert, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L16).

**Complexification keeps support.** Pointwise complexification preserves compact support. Source: Breakdown.Freq.Internal.VelocityInvert.cplxField_hasCompactSupport in Breakdown.FreqTr.VelocityInvert, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L20).

**A compact test as a Schwartz field.** A smooth compact real field is complexified and packaged as a Schwartz function. Source: Breakdown.Freq.Internal.VelocityInvert.cplxRapid in Breakdown.FreqTr.VelocityInvert, line 24. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L24).

**A half Laplacian test predecessor.** The test symbol divides the Fourier transform of the compact test by two pi times frequency radius. Source: Breakdown.Freq.Internal.VelocityInvert.thetaFun in Breakdown.FreqTr.VelocityInvert, line 28. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L28).

**Schwartz functions are bounded.** A Schwartz vector function has a finite nonnegative uniform norm bound. Source: Breakdown.Freq.Internal.VelocityInvert.rapid_norm_bounded in Breakdown.FreqTr.VelocityInvert, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L32).

**The test predecessor belongs to L2.** The frequency test divided by two pi times radius is square integrable. Source: Breakdown.Freq.Internal.VelocityInvert.memLp_thetaFun in Breakdown.FreqTr.VelocityInvert, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L39).

**Fourier preserves the real pairing.** The L2 Fourier isometry preserves the real inner product. Source: Breakdown.Freq.Internal.VelocityInvert.l2Iso_inner_map in Breakdown.FreqTr.VelocityInvert, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L83).

**Pair a complex vector with a real one.** Pairing a complex vector with an included real vector equals pairing its real part with that real vector. Source: Breakdown.Freq.Internal.VelocityInvert.l2Iso_realVec_inner in Breakdown.FreqTr.VelocityInvert, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L88).

**The physical inverse representative.** Physical recovery equals the real part of the inverse L2 transform almost everywhere. Source: Breakdown.Freq.Internal.VelocityInvert.l2Iso_toPhys_ae in Breakdown.FreqTr.VelocityInvert, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L92).

**A physical form of the test pairing.** The L2 pairing with the transformed compact test equals the physical integral against that test. Source: Breakdown.Freq.Internal.VelocityInvert.inner_freqTr_cplx in Breakdown.FreqTr.VelocityInvert, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L96).

**Recover a compact test by inversion.** The physical inverse transform of the transformed complex compact test recovers the original test almost everywhere. Source: Breakdown.Freq.Internal.VelocityInvert.toPhys_freqTr_cplx in Breakdown.FreqTr.VelocityInvert, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L110).

**Move the half Laplacian across a pairing.** The half Laplacian frequency relation moves its radial factor from the state to the inverse weighted test symbol. Source: Breakdown.Freq.Internal.VelocityInvert.inner_thetaFun in Breakdown.FreqTr.VelocityInvert, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L118).

**A test field has decay.** A solenoidal test field satisfies the decay field conditions. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_decay in Breakdown.FreqTr.VelocityInvert, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L135).

**Read the test embedding as its gradient.** The test field embedding has the same ambient L2 value as its gradient representation. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_embed_eq in Breakdown.FreqTr.VelocityInvert, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L158).

**The classical and Schwartz partial agree.** A test field's coordinate derivative equals the corresponding Schwartz line derivative. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_partial_eq in Breakdown.FreqTr.VelocityInvert, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L163).

**Complexify the test derivative class.** The complexified L2 class of the test derivative equals the class of its complex Schwartz derivative. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_cplx_deriv in Breakdown.FreqTr.VelocityInvert, line 169. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L169).

**Schwartz representatives in L2.** Transforming a Schwartz L2 class equals taking the L2 class of the Schwartz transform. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_freqTr_toLp in Breakdown.FreqTr.VelocityInvert, line 193. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L193).

**Evaluate the multiplication operator.** The complex multiplication map applies the scalar to the vector. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_cmul_apply in Breakdown.FreqTr.VelocityInvert, line 196. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L196).

**Cancel one gradient embedding factor.** The embedding symbol times the transformed partial factor reduces to two pi times the coordinate square divided by radius. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_term in Breakdown.FreqTr.VelocityInvert, line 198. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L198).

**Sum the three coordinate factors.** The sum of the three normalized coordinate squares is two pi times the frequency radius. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_sum in Breakdown.FreqTr.VelocityInvert, line 212. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L212).

**The gradient operator has unit bound.** Every pointwise gradient embedding multiplier has norm at most one. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_symbol_bound in Breakdown.FreqTr.VelocityInvert, line 221. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L221).

**Multiplication as a scalar identity.** The multiplication operator is the scalar multiple of the complex identity map restricted to real scalars. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_cmul_eq in Breakdown.FreqTr.VelocityInvert, line 233. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L233).

**Measurability of gradient operators.** The operator valued gradient embedding multiplier is almost everywhere strongly measurable. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_symbol_meas in Breakdown.FreqTr.VelocityInvert, line 239. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L239).

**Read the chosen gradient operator.** The chosen gradient multiplier has its pointwise representative almost everywhere. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_fieldOp_ae in Breakdown.FreqTr.VelocityInvert, line 249. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L249).

**One transformed gradient term.** Each transformed partial embedding contribution equals its coordinate square weight times the Fourier test symbol almost everywhere. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_term_ae in Breakdown.FreqTr.VelocityInvert, line 255. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L255).

**Add three representatives.** The sum of three L2 classes has the sum of their almost everywhere representatives. Source: Breakdown.Freq.Internal.VelocityInvert.ofgrad_add3 in Breakdown.FreqTr.VelocityInvert, line 269. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L269).

**The embedding is a half Laplacian.** The embedding of a test field is two pi times frequency radius times the Fourier transform of its complex L2 class almost everywhere. Source: Breakdown.Freq.Internal.VelocityInvert.embedX_halfSsp in Breakdown.FreqTr.VelocityInvert, line 275. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L275).

**Pair an L6 field with a compact test.** The inner product of an L6 field with a smooth compact test is integrable. Source: Breakdown.Freq.Internal.VelocityInvert.pairing_integrable in Breakdown.FreqTr.VelocityInvert, line 290. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L290).

**Bound the compact test pairing.** Hölder bounds the test pairing by the L6 field norm times the test's conjugate exponent norm. Source: Breakdown.Freq.Internal.VelocityInvert.pairing_bound in Breakdown.FreqTr.VelocityInvert, line 300. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L300).

**The velocity recovers an embedded test.** The velocity of a test embedding equals the test field almost everywhere. Source: Breakdown.Freq.Internal.VelocityInvert.velocity_embedX_test in Breakdown.FreqTr.VelocityInvert, line 314. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L314).

**Continuity of velocity test pairings.** Pairing recovered velocity against a fixed smooth compact test is continuous in the state. Source: Breakdown.Freq.Internal.VelocityInvert.continuous_velocity_pairing in Breakdown.FreqTr.VelocityInvert, line 327. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L327).

**Compact tests identify two fields.** An L6 field and an L2 field with equal pairings against all smooth compact tests agree almost everywhere. Source: Breakdown.Freq.Internal.VelocityInvert.ae_eq_of_pairing in Breakdown.FreqTr.VelocityInvert, line 344. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L344).

**Source namespace:** Breakdown.Freq.

**Prove half Laplacian inversion.** The theorem identifies velocity of a half Laplacian state with the physical inverse transform of its predecessor. Source: Breakdown.Freq.velocityInvertsHalfSsp in Breakdown.FreqTr.VelocityInvert, line 367. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityInvert.lean#L367).

### Breakdown.FreqTr.VelocityRotate

Transformed test pairings and uniqueness of recovery establish the almost-everywhere rotation and positive-dilation laws for velocity.

**Source namespace:** Breakdown.Freq.Internal.VelocityRotate.

**Scaled coordinate changes preserve L6.** The measure scaling hypothesis and finite scale preserve L6 membership under coordinate composition and a bounded linear value map. Source: Breakdown.Freq.Internal.VelocityRotate.memLp_comp in Breakdown.FreqTr.VelocityRotate, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L14).

**Transport almost everywhere equality.** Composition with the specified measure scaling coordinate map preserves almost everywhere equality. Source: Breakdown.Freq.Internal.VelocityRotate.ae_comp in Breakdown.FreqTr.VelocityRotate, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L19).

**The L6 coordinate change bound.** The transformed L6 norm is bounded by the value map norm times the sixth root measure factor times the original norm. Source: Breakdown.Freq.Internal.VelocityRotate.eLpNorm_comp_le in Breakdown.FreqTr.VelocityRotate, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L23).

**A transformed operator on L6 fields.** The construction packages coordinate composition and a fixed value map as a continuous real linear operator on L6. Source: Breakdown.Freq.Internal.VelocityRotate.compOp in Breakdown.FreqTr.VelocityRotate, line 36. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L36).

**Read the L6 composition operator.** The constructed L6 operator agrees almost everywhere with its coordinate and value transformation formula. Source: Breakdown.Freq.Internal.VelocityRotate.compOp_ae in Breakdown.FreqTr.VelocityRotate, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L73).

**Transform a valid L6 field class.** Applying the L6 composition operator to a field class gives the class of its transformed field. Source: Breakdown.Freq.Internal.VelocityRotate.compOp_toLp in Breakdown.FreqTr.VelocityRotate, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L77).

**Test fields meet the decay hypotheses.** A test field satisfies the decay field conditions. Source: Breakdown.Freq.Internal.VelocityRotate.decay_of_test in Breakdown.FreqTr.VelocityRotate, line 87. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L87).

**Test fields belong to L6.** Every test field is sixth power integrable. Source: Breakdown.Freq.Internal.VelocityRotate.memLp_test in Breakdown.FreqTr.VelocityRotate, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L109).

**Read coordinates by a unit pairing.** A vector coordinate equals its inner product with the corresponding unit vector. Source: Breakdown.Freq.Internal.VelocityRotate.coord_eq_inner in Breakdown.FreqTr.VelocityRotate, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L112).

**Rotation preserves the second trace.** The coordinate trace of a linear map is unchanged by conjugation with a spatial isometry. Source: Breakdown.Freq.Internal.VelocityRotate.sum_rot in Breakdown.FreqTr.VelocityRotate, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L115).

**Rotations preserve test fields.** Pushing a test field forward by a spatial isometry preserves its test field conditions. Source: Breakdown.Freq.Internal.VelocityRotate.test_pushForward in Breakdown.FreqTr.VelocityRotate, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L130).

**Positive dilations preserve test fields.** The physical dilation of a test field at positive scale is a test field. Source: Breakdown.Freq.Internal.VelocityRotate.test_dilate in Breakdown.FreqTr.VelocityRotate, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L150).

**Velocity has the test property.** The velocity existence interface implies that the chosen velocity satisfies the test field recovery specification. Source: Breakdown.Freq.Internal.VelocityRotate.velocity_spec in Breakdown.FreqTr.VelocityRotate, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L172).

**Extend an identity from dense tests.** A continuous state transformation identity for velocity extends from test embeddings to every state by density. Source: Breakdown.Freq.Internal.VelocityRotate.eq_of_test in Breakdown.FreqTr.VelocityRotate, line 177. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L177).

**Source namespace:** Breakdown.Freq.

**Velocity rotation and dilation laws.** The theorem derives both physical covariance identities for velocity recovery from test density and embedding covariance. Source: Breakdown.Freq.velocityRotateDilate in Breakdown.FreqTr.VelocityRotate, line 189. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/VelocityRotate.lean#L189).

### Breakdown.FreqTr.WeakInX

Test-field closure, integration by parts and the advection identity translate the physical weak equation into its Fourier state formulation.

**Source namespace:** Breakdown.Freq.Internal.WeakInX.

**Evaluate the second Fréchet derivative.** Differentiating a first directional derivative evaluates the second Fréchet derivative on the two directions. Source: Breakdown.Freq.Internal.WeakInX.fderiv_dir_eq in Breakdown.FreqTr.WeakInX, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L12).

**Partial fields retain smoothness.** Coordinate derivatives of a smooth vector field are smooth. Source: Breakdown.Freq.Internal.WeakInX.smooth_partial in Breakdown.FreqTr.WeakInX, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L19).

**The two partial derivatives commute.** Mixed coordinate derivatives of a smooth field commute. Source: Breakdown.Freq.Internal.WeakInX.partial_comm in Breakdown.FreqTr.WeakInX, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L23).

**Differentiate a coordinate sum.** The derivative of the sum of matching coordinates equals the sum of their matching derivative coordinates. Source: Breakdown.Freq.Internal.WeakInX.fderiv_sum_comp in Breakdown.FreqTr.WeakInX, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L32).

**Expand the test Laplacian.** The negative Laplacian of a smooth field is the negative sum of its second coordinate partials. Source: Breakdown.Freq.Internal.WeakInX.negSsp_eq in Breakdown.FreqTr.WeakInX, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L42).

**Zero divergence survives the Laplacian.** The negative Laplacian of a smooth divergence free field remains divergence free. Source: Breakdown.Freq.Internal.WeakInX.divergence_negSsp in Breakdown.FreqTr.WeakInX, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L52).

**Source namespace:** Breakdown.Freq.

**Test fields decay.** Every test field satisfies the spatial decay field predicate. Source: Breakdown.Freq.isDecayField_of_isTestField in Breakdown.FreqTr.WeakInX, line 91. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L91).

**The negative Laplacian stays a test.** Applying the negative Laplacian preserves the test field conditions. Source: Breakdown.Freq.isTestField_negSsp in Breakdown.FreqTr.WeakInX, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L114).

**Source namespace:** Breakdown.Freq.Internal.WeakInX.

**Subtract the first trilinear state.** For a test in both L2 and L6, the trilinear estimate permits subtraction in the first state input. Source: Breakdown.Freq.Internal.WeakInX.trilinear_sub_left in Breakdown.FreqTr.WeakInX, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L130).

**Subtract the second trilinear state.** For a test in both L2 and L6, the trilinear estimate permits subtraction in the second state input. Source: Breakdown.Freq.Internal.WeakInX.trilinear_sub_right in Breakdown.FreqTr.WeakInX, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L142).

**Continuity of the diagonal trilinear map.** The diagonal trilinear pairing with a fixed L2 and L6 test is continuous in the state. Source: Breakdown.Freq.Internal.WeakInX.continuous_trilinear_diag in Breakdown.FreqTr.WeakInX, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L158).

**Source namespace:** Breakdown.Freq.

**Prove the weak state formulation.** The embedding, integration by parts and advection pairing interfaces translate the physical weak equation into the state space identity. Source: Breakdown.Freq.weakInX in Breakdown.FreqTr.WeakInX, line 185. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FreqTr/WeakInX.lean#L185).
<!-- /passage:sec-breakdown-freqtr -->

## Breakdown/Held

<!-- passage:sec-breakdown-held -->

### Breakdown.Held.AdjointEnclosure

Finite Cauchy–Schwarz estimates support the adjoint enclosure bound on the held multiplier coordinates.

**Source namespace:** Breakdown.Held.

**Finite Cauchy Schwarz.** The absolute dot product is bounded by the product of the square roots of the two sums of squares. Source: Breakdown.Held.abs_sum_mul_le_sqrt_mul_sqrt in Breakdown.Held.AdjointEnclosure, line 7. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/AdjointEnclosure.lean#L7).

### Breakdown.Held.ConvexCompactFixedPoint

Nonexpansiveness of nearest-point projection allows a box fixed-point result to supply the compact convex fixed-point theorem.

**Source namespace:** Breakdown.FracInternal.

**The nearest point map is nonexpansive.** A map into the set satisfying the projection variational inequality is Lipschitz with constant one. Source: Breakdown.FracInternal.nearestPoint_nonexpansive in Breakdown.Held.ConvexCompactFixedPoint, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/ConvexCompactFixedPoint.lean#L10).

### Breakdown.Held.Statements

The mixed box and weighted ellipsoid parameter set is defined alongside the compact convex fixed-point obligation.

**Source namespace:** Breakdown.Held.

**The mixed box and ellipsoid test set.** The test set combines coordinate bounds on selected indices with a weighted square sum bound on the complementary indices. Source: Breakdown.Held.testSet in Breakdown.Held.Statements, line 9. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/Statements.lean#L9).

**A compact convex fixed point requirement.** This proposition requires every continuous self map of a nonempty compact convex finite dimensional set to have a fixed point. Source: Breakdown.Held.ConvexCompactFixedPointStatement in Breakdown.Held.Statements, line 21. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/Statements.lean#L21).

### Breakdown.Held.TestSetZero

Convexity, closedness, boundedness and containment of zero prepare the parameter test set for the held multiplier zero argument.

**Source namespace:** Breakdown.Held.Internal.

**Convexity of a weighted square sum.** A finite sum of weighted coordinate squares is convex on the whole parameter space. Source: Breakdown.Held.Internal.convexOn_sum_sq in Breakdown.Held.TestSetZero, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L12).

**The parameter test set is convex.** The mixed coordinate box and weighted ellipsoid test set is convex. Source: Breakdown.Held.Internal.convex_testSet in Breakdown.Held.TestSetZero, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L29).

**The parameter test set is closed.** The mixed coordinate box and weighted ellipsoid test set is closed. Source: Breakdown.Held.Internal.isClosed_testSet in Breakdown.Held.TestSetZero, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L43).

**The parameter test set is bounded.** Nonzero coordinate weights and nonnegative ellipsoid radius make the parameter test set bounded. Source: Breakdown.Held.Internal.isBounded_testSet in Breakdown.Held.TestSetZero, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L56).

**The parameter test set contains zero.** Nonnegative bounds on the boxed coordinates ensure that zero belongs to the parameter test set. Source: Breakdown.Held.Internal.zero_mem_testSet in Breakdown.Held.TestSetZero, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Held/TestSetZero.lean#L82).
<!-- /passage:sec-breakdown-held -->

## Breakdown/Profile

<!-- passage:sec-breakdown-profile -->

### Breakdown.Profile.ChangeOfVariables

The exponential similarity-time substitution is justified for vector-valued interval integrals with its exact Jacobian factor.

**Source namespace:** Breakdown.

**Differentiate the exponential time map.** The derivative of one minus the shifted negative exponential is that shifted exponential. Source: Breakdown.expShift_hasDerivAt in Breakdown.Profile.ChangeOfVariables, line 9. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/ChangeOfVariables.lean#L9).

**The exponential time interval image.** The exponential change of variables sends the stated half open similarity time interval to its corresponding physical time interval. Source: Breakdown.expShift_image in Breakdown.Profile.ChangeOfVariables, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/ChangeOfVariables.lean#L15).

**Prove the exponential substitution.** The theorem discharges the Banach valued integral substitution for the exponential time change. Source: Breakdown.expChangeOfVariables_holds in Breakdown.Profile.ChangeOfVariables, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/ChangeOfVariables.lean#L41).

### Breakdown.Profile.Difference

The physical time derivative bound controls differences of profile-derived physical fields on compact time intervals before one.

**Source namespace:** Breakdown.

**Bound the physical scale before blowup.** Between time zero and a fixed time below one, the physical scale lies between one and its value at that final time. Source: Breakdown.physicalScale_bounds in Breakdown.Profile.Difference, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Difference.lean#L10).

### Breakdown.Profile.Dilate

Derivative and algebraic identities for physical scaling connect the similarity profile to the abstract dilation operations.

**Source namespace:** Breakdown.

**Differentiate the scaled field.** The derivative of an amplitude scaled and spatially scaled field gains the product of the two scaling constants. Source: Breakdown.fderiv_smul_comp_smul in Breakdown.Profile.Dilate, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Dilate.lean#L10).

**Differentiate the physical dilation.** The derivative of the physical dilation gains the square of its square root factor and evaluates at the scaled point. Source: Breakdown.fderiv_dilateField in Breakdown.Profile.Dilate, line 18. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Dilate.lean#L18).

**Differentiate the dilation twice.** The second derivative of the physical dilation gains the cube of its square root factor. Source: Breakdown.fderiv_fderiv_dilateField in Breakdown.Profile.Dilate, line 23. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Dilate.lean#L23).

**Close subtraction of decay fields.** The theorem discharges closure of decay fields under subtraction. Source: Breakdown.decayFieldSub_holds in Breakdown.Profile.Dilate, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Dilate.lean#L30).

**Prove the physical dilation calculus.** The theorem discharges the derivative, Laplacian and advection identities under physical dilation. Source: Breakdown.dilateCalculus_holds in Breakdown.Profile.Dilate, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Dilate.lean#L58).

**Prove scalar gradient scaling.** The theorem discharges the chain rule for a scalar field gradient under spatial dilation. Source: Breakdown.gradientScale_holds in Breakdown.Profile.Dilate, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Dilate.lean#L72).

### Breakdown.Profile.DilateDecay

Physical dilation preserves the decay field class with the required rescaled derivative estimates.

**Source namespace:** Breakdown.

**Compare inverse radial weights.** A positive radial rescaling changes the inverse first order weight by at most the displayed maximum factor. Source: Breakdown.inv_shift_le in Breakdown.Profile.DilateDecay, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/DilateDecay.lean#L10).

**Compare inverse squared radial weights.** A positive radial rescaling changes the inverse squared weight by at most the displayed squared maximum factor. Source: Breakdown.inv_shift_sq_le in Breakdown.Profile.DilateDecay, line 20. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/DilateDecay.lean#L20).

### Breakdown.Profile.FlowMild

Dilation covariance of the kernel and the exponential time substitution convert physical mild evolution into the rescaled flow identity.

**Source namespace:** Breakdown.

**Convert the mild flow to similarity time.** Kernel dilation and exponential substitution give the similarity time integral equation from physical mild flow. Source: Breakdown.flowOfMild_holds in Breakdown.Profile.FlowMild, line 9. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/FlowMild.lean#L9).

### Breakdown.Profile.FrameAlgebra

Similarity-frame differentiation is simplified into the scaling and time factors needed by the physical profile equation.

**Source namespace:** Breakdown.

**Prove joint dilation continuity.** The theorem proves the abstract dilation acts jointly continuously on positive scales and states. Source: Breakdown.dilateJointContinuous_holds in Breakdown.Profile.FrameAlgebra, line 9. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/FrameAlgebra.lean#L9).

**Prove the dilated kernel identity.** The theorem derives the displayed bilinear kernel dilation identity from the abstract framework laws. Source: Breakdown.kernelDilate_holds in Breakdown.Profile.FrameAlgebra, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/FrameAlgebra.lean#L61).

### Breakdown.Profile.L2

Inverse cubic spatial decay turns physical time differences into square-integrable fields with quantitative bounds.

**Source namespace:** Breakdown.

**Continuity of a physical profile slice.** A jointly smooth similarity profile gives a continuous physical field at each fixed time. Source: Breakdown.physicalField_continuous in Breakdown.Profile.L2, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/L2.lean#L10).

**Sixth order radial decay is integrable.** The negative sixth radial power is integrable in three spatial dimensions. Source: Breakdown.integrable_one_add_norm_rpow_neg_six in Breakdown.Profile.L2, line 18. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/L2.lean#L18).

**Square the time difference bound.** Squaring the third order radial difference estimate gives the sixth order integrable majorant. Source: Breakdown.sq_norm_le_of_le in Breakdown.Profile.L2, line 24. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/L2.lean#L24).

### Breakdown.Profile.Mild

Decay, square-integrable differences, the weak equation and dilation continuity establish mild evolution of the physical profile field.

**Source namespace:** Breakdown.

**Assemble the physical mild profile.** The decay, L2 difference, weak equation and dilation continuity interfaces imply that the physical profile flow is mild. Source: Breakdown.physicalMild_holds in Breakdown.Profile.Mild, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Mild.lean#L11).

### Breakdown.Profile.Momentum

The transformed pressure gradient is scaled consistently with the physical momentum equation.

**Source namespace:** Breakdown.

**A constant in the pressure gradient.** Multiplying a smooth scalar field by a constant multiplies its gradient by that constant. Source: Breakdown.gradientAt_const_mul in Breakdown.Profile.Momentum, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Momentum.lean#L10).

### Breakdown.Profile.OrbitParts

Slice decay, gradient continuity, physical mildness and the flow conversion assemble the nonzero recurrent embedded profile orbit.

**Source namespace:** Breakdown.

**Assemble the embedded profile orbit.** The five analytic profile inputs produce a continuous, nonzero embedded orbit with rotational recurrence and the rescaled mild evolution identity. Source: Breakdown.embeddedOrbitOfParts_holds in Breakdown.Profile.OrbitParts, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/OrbitParts.lean#L10).

**Assemble the profile orbit interface.** The five analytic profile inputs convert the smooth recurrent profile premise into a recurrent mild orbit for any physical realization. Source: Breakdown.orbitOfParts_holds in Breakdown.Profile.OrbitParts, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/OrbitParts.lean#L57).

### Breakdown.Profile.PairingDeriv

Local scaling bounds and integrable test majorants justify differentiating the physical field pairing under the integral sign.

**Source namespace:** Breakdown.

**The full similarity time derivative.** The similarity derivative adds the profile time derivative, one half of the field and one half of its radial derivative. Source: Breakdown.similarityDeriv in Breakdown.Profile.PairingDeriv, line 10. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L10).

**A smooth profile has smooth slices.** Each fixed time slice of a jointly smooth vector profile is smooth. Source: Breakdown.slice_contDiff in Breakdown.Profile.PairingDeriv, line 13. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L13).

**Continuity of the transformed slice.** The physical rescaling of a jointly smooth profile is continuous in space. Source: Breakdown.physicalField_continuous in Breakdown.Profile.PairingDeriv, line 17. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L17).

**The scale is monotone before one.** The physical scale increases with time as long as the later time is below one. Source: Breakdown.physicalScale_le in Breakdown.Profile.PairingDeriv, line 25. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L25).

**The physical scale is nonnegative.** The physical scale is nonnegative at every real argument. Source: Breakdown.physicalScale_nonneg in Breakdown.Profile.PairingDeriv, line 31. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L31).

**A measurable similarity derivative.** For a jointly smooth profile, the full similarity derivative is measurable in space. Source: Breakdown.similarityDeriv_measurable in Breakdown.Profile.PairingDeriv, line 33. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L33).

**An elementary cubic weight bound.** A scalar divided by the cubed radial weight is at most the scalar's absolute value. Source: Breakdown.div_cube_le_abs in Breakdown.Profile.PairingDeriv, line 53. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L53).

**Differentiate the physical test pairing.** The time derivative, momentum and decay interfaces justify differentiating the physical field pairing against a test. Source: Breakdown.physicalPairingDeriv_holds in Breakdown.Profile.PairingDeriv, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/PairingDeriv.lean#L59).

### Breakdown.Profile.Parts

Smooth directional derivatives and compact test support supply the integration-by-parts identities used in the weak profile calculation.

**Source namespace:** Breakdown.

**Smooth vector directional derivatives.** A fixed directional derivative of a smooth vector field is smooth. Source: Breakdown.smooth_dir in Breakdown.Profile.Parts, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L10).

**Smooth scalar directional derivatives.** A fixed directional derivative of a smooth scalar field is smooth. Source: Breakdown.smooth_dir_scalar in Breakdown.Profile.Parts, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L14).

**Pair integrably with a vector test.** The pairing of continuous vector fields is integrable when the second field has compact support. Source: Breakdown.integrable_inner_right in Breakdown.Profile.Parts, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L18).

**Pair integrably with a scalar test.** The product of continuous scalar functions is integrable when the second has compact support. Source: Breakdown.integrable_mul_right in Breakdown.Profile.Parts, line 27. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L27).

**The second derivative on one direction.** The second iterated derivative on a repeated direction equals the corresponding second directional derivative. Source: Breakdown.second_dir in Breakdown.Profile.Parts, line 36. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L36).

**Expand the sum of second partials.** The Laplacian trace is the sum of the second directional derivatives along the coordinate axes. Source: Breakdown.sumSecondPartials_eq in Breakdown.Profile.Parts, line 43. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L43).

**Move one second derivative onto the test.** Pairing a second coordinate derivative with a test equals the negative pairing of their first derivatives. Source: Breakdown.one_pair in Breakdown.Profile.Parts, line 49. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L49).

**Smoothness of test coordinates.** Every coordinate of a smooth vector field is smooth. Source: Breakdown.coord_smooth in Breakdown.Profile.Parts, line 68. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L68).

**Differentiate a coordinate projection.** Differentiating a coordinate function extracts the corresponding coordinate of the vector derivative. Source: Breakdown.coord_dir in Breakdown.Profile.Parts, line 72. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L72).

**Expand the scalar gradient pairing.** The inner product of a scalar gradient with a vector is the sum of its coordinate directional derivatives times vector coordinates. Source: Breakdown.gradient_inner in Breakdown.Profile.Parts, line 82. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L82).

**A scalar gradient component by parts.** A scalar derivative paired with a compact test coordinate transfers to that test coordinate with a negative sign. Source: Breakdown.one_grad in Breakdown.Profile.Parts, line 90. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L90).

**Prove the Laplacian pairing formula.** The theorem discharges the identity between the Laplacian test pairing and negative gradient pairing. Source: Breakdown.sumSecondPartialsPairing_holds in Breakdown.Profile.Parts, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Parts.lean#L107).

### Breakdown.Profile.Slice

Joint profile smoothness and derivative decay imply the spatial decay and similarity-derivative bounds of each time slice.

**Source namespace:** Breakdown.

**Smooth vector profile slices.** Fixing time in a jointly smooth vector profile gives a smooth spatial slice. Source: Breakdown.slice_contDiff in Breakdown.Profile.Slice, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Slice.lean#L10).

**Smooth pressure slices.** Fixing time in a jointly smooth scalar pressure gives a smooth spatial slice. Source: Breakdown.slice_contDiff_scalar in Breakdown.Profile.Slice, line 15. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Slice.lean#L15).

**Unit vector normalization.** Every coordinate unit vector has norm one. Source: Breakdown.norm_unitVector in Breakdown.Profile.Slice, line 20. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Slice.lean#L20).

**Bound the Laplacian by derivatives.** The norm of the componentwise Laplacian is at most three times the norm of the second iterated derivative. Source: Breakdown.norm_sumSecondPartialsAt_le in Breakdown.Profile.Slice, line 23. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Slice.lean#L23).

**Bound the gradient by the derivative.** The scalar gradient norm is at most three times the scalar derivative operator norm. Source: Breakdown.norm_gradientAt_le in Breakdown.Profile.Slice, line 38. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Slice.lean#L38).

**Bound the advection term.** The advection norm is bounded by the derivative operator norm times the velocity norm. Source: Breakdown.norm_advectionAt_le in Breakdown.Profile.Slice, line 52. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Slice.lean#L52).

**Prove similarity derivative decay.** The profile equation and derivative estimates give the required third order radial bound on the full similarity derivative. Source: Breakdown.similarityDerivBound_holds in Breakdown.Profile.Slice, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Slice.lean#L65).

### Breakdown.Profile.SliceContinuity

A common integrable derivative majorant makes the embedded gradient square difference tend to zero as slice time varies.

**Source namespace:** Breakdown.

**Read a slice as a composition.** A fixed time profile slice is the joint profile composed with the map inserting that time. Source: Breakdown.slice_eq_comp in Breakdown.Profile.SliceContinuity, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/SliceContinuity.lean#L10).

**Smoothness of a fixed time slice.** Each slice of a jointly smooth profile is smooth. Source: Breakdown.slice_contDiff in Breakdown.Profile.SliceContinuity, line 13. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/SliceContinuity.lean#L13).

**Differentiability of a fixed time slice.** Each slice of a jointly smooth profile is differentiable. Source: Breakdown.slice_differentiable in Breakdown.Profile.SliceContinuity, line 19. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/SliceContinuity.lean#L19).

**Read the joint derivative on a slice.** The spatial slice derivative is the joint derivative evaluated on a direction with zero time component. Source: Breakdown.slice_fderiv_apply in Breakdown.Profile.SliceContinuity, line 24. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/SliceContinuity.lean#L24).

**Time continuity of a spatial derivative.** The derivative of a jointly smooth profile at fixed point and direction depends continuously on time. Source: Breakdown.slice_fderiv_continuous in Breakdown.Profile.SliceContinuity, line 33. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/SliceContinuity.lean#L33).

**Dominate slice derivative differences.** The squared coordinate derivative difference between two profile slices has the stated fourth order radial majorant. Source: Breakdown.slice_fderiv_diff_sq_le in Breakdown.Profile.SliceContinuity, line 44. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/SliceContinuity.lean#L44).

### Breakdown.Profile.StatementsEmbed

The embedded-orbit interface specifies the five analytic profile inputs that produce a recurrent orbit in an arbitrary physical realization.

**Source namespace:** Breakdown.

**The embedded orbit assembly implication.** This proposition requires subtraction, slice decay, slice continuity, physical mild flow and the time conversion to imply an embedded profile orbit. Source: Breakdown.EmbeddedOrbitOfParts in Breakdown.Profile.StatementsEmbed, line 18. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsEmbed.lean#L18).

### Breakdown.Profile.StatementsField

The field-calculus interfaces require decay closure, dilation derivative formulas, pressure-gradient scaling and integration by parts against tests.

**Source namespace:** Breakdown.

**Subtraction preserves decay fields.** This proposition requires differences of decay fields to remain decay fields. Source: Breakdown.DecayFieldSub in Breakdown.Profile.StatementsField, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsField.lean#L10).

**Positive dilation preserves decay fields.** This proposition requires positive physical dilation to preserve the decay field conditions. Source: Breakdown.DecayFieldDilate in Breakdown.Profile.StatementsField, line 13. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsField.lean#L13).

**The three dilation calculus identities.** This proposition packages the gradient, Laplacian and advection scaling identities for smooth fields. Source: Breakdown.DilateCalculus in Breakdown.Profile.StatementsField, line 16. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsField.lean#L16).

**The gradient under spatial scaling.** This proposition requires scalar gradient to scale by the spatial dilation factor. Source: Breakdown.GradientScale in Breakdown.Profile.StatementsField, line 22. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsField.lean#L22).

**The Laplacian test pairing identity.** This proposition equates the Laplacian pairing against a test field with the negative gradient pairing. Source: Breakdown.SumSecondPartialsPairing in Breakdown.Profile.StatementsField, line 26. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsField.lean#L26).

### Breakdown.Profile.StatementsFlow

Joint dilation continuity, kernel scaling and the exponential integral substitution specify the conversion between physical and rescaled mild evolution.

**Source namespace:** Breakdown.

**Joint continuity of state dilation.** This proposition requires dilation in any mild framework to depend jointly continuously on positive scale and state. Source: Breakdown.DilateJointContinuous in Breakdown.Profile.StatementsFlow, line 9. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsFlow.lean#L9).

**The abstract kernel dilation identity.** This proposition specifies how a bilinear kernel with inversely dilated inputs transforms under an outer dilation. Source: Breakdown.KernelDilate in Breakdown.Profile.StatementsFlow, line 13. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsFlow.lean#L13).

**The exponential time substitution.** This proposition requires the exponential time change to preserve interval integrability and obey the displayed weighted integral equality. Source: Breakdown.ExpChangeOfVariables in Breakdown.Profile.StatementsFlow, line 18. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsFlow.lean#L18).

### Breakdown.Profile.StatementsOrbit

The profile-orbit assembly proposition records how five analytic inputs turn the existential smooth profile premise into a recurrent abstract orbit.

**Source namespace:** Breakdown.

**The profile orbit assembly implication.** This proposition combines the five analytic profile interfaces into the abstract profile orbit statement. Source: Breakdown.OrbitOfParts in Breakdown.Profile.StatementsOrbit, line 10. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsOrbit.lean#L10).

### Breakdown.Profile.StatementsPhysical

The physical derivative, momentum, time-difference decay and differentiated pairing obligations encode the profile-to-PDE change of variables.

**Source namespace:** Breakdown.

**The physical profile time derivative.** This proposition gives the cubic scale factor times the complete similarity derivative for the physical field before time one. Source: Breakdown.PhysicalTimeDeriv in Breakdown.Profile.StatementsPhysical, line 20. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L20).

**The physical momentum equation.** This proposition requires a similarity profile's physical field to satisfy the Navier Stokes momentum equation with its transformed pressure. Source: Breakdown.PhysicalMomentum in Breakdown.Profile.StatementsPhysical, line 30. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L30).

**Decay of physical time differences.** This proposition bounds physical field differences by elapsed time times an inverse cubic radial weight on each compact interval before one. Source: Breakdown.PhysicalDifference in Breakdown.Profile.StatementsPhysical, line 37. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L37).

**The differentiated physical pairing.** This proposition differentiates the physical field pairing into the test pairing with Laplacian, advection and pressure gradient terms. Source: Breakdown.PhysicalPairingDeriv in Breakdown.Profile.StatementsPhysical, line 51. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsPhysical.lean#L51).

### Breakdown.Profile.StatementsSlice

The slice interfaces require spatial decay of every profile slice and uniform inverse cubic decay of the complete similarity derivative.

**Source namespace:** Breakdown.

**Every similarity profile slice decays.** This proposition requires each time slice of a similarity profile to satisfy the decay field conditions. Source: Breakdown.SliceDecay in Breakdown.Profile.StatementsSlice, line 18. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsSlice.lean#L18).

**The full similarity derivative decays.** This proposition requires the full similarity derivative to have a uniform inverse cubic radial bound. Source: Breakdown.SimilarityDerivBound in Breakdown.Profile.StatementsSlice, line 22. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/StatementsSlice.lean#L22).

### Breakdown.Profile.TimeDeriv

The derivatives of the physical scale and similarity time supply the exact cubic and square scale factors before time one.

**Source namespace:** Breakdown.

**Differentiate the physical scale.** Before time one the derivative of the physical scale is half its cube. Source: Breakdown.hasDerivAt_physicalScale in Breakdown.Profile.TimeDeriv, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/TimeDeriv.lean#L10).

**Differentiate the physical time change.** Before time one the derivative of the physical time map is the square of the physical scale. Source: Breakdown.hasDerivAt_physicalTime in Breakdown.Profile.TimeDeriv, line 32. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/TimeDeriv.lean#L32).

### Breakdown.Profile.Weak

Smooth slices and continuous Laplacian, advection and pressure-gradient fields justify the weak physical profile equation against compact tests.

**Source namespace:** Breakdown.

**Smoothness of velocity slices.** Each time slice of a jointly smooth vector profile is smooth. Source: Breakdown.slice_contDiff in Breakdown.Profile.Weak, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Weak.lean#L10).

**Smoothness of pressure slices.** Each time slice of a jointly smooth pressure profile is smooth. Source: Breakdown.pressure_slice_contDiff in Breakdown.Profile.Weak, line 14. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Weak.lean#L14).

**Pair a continuous field with a test.** The pairing of a continuous field with a test field is integrable. Source: Breakdown.integrable_inner_of_continuous in Breakdown.Profile.Weak, line 18. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Weak.lean#L18).

**Continuity of the Laplacian field.** The componentwise Laplacian of a smooth vector field is continuous. Source: Breakdown.continuous_sumSecondPartialsAt in Breakdown.Profile.Weak, line 26. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Weak.lean#L26).

**Continuity of the advection field.** The advection field of a smooth vector field is continuous. Source: Breakdown.continuous_advectionAt in Breakdown.Profile.Weak, line 33. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Weak.lean#L33).

**Continuity of the pressure gradient.** The gradient of a smooth scalar field is continuous. Source: Breakdown.continuous_gradientAt in Breakdown.Profile.Weak, line 38. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Profile/Weak.lean#L38).
<!-- /passage:sec-breakdown-profile -->

## Breakdown/Spectral

<!-- passage:sec-breakdown-spectral -->

### Breakdown.Spectral.CompactPart

Contour integration preserves compactness and shows that the complement of the inner spectral projection is compact for a small-plus-compact operator.

**Source namespace:** Breakdown.Spectral.

**Integrate a compact operator family.** A continuous circle family of compact operators has a compact circle integral. Source: Breakdown.Spectral.isCompactOperator_circleIntegral in Breakdown.Spectral.CompactPart, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/CompactPart.lean#L11).

**The outer spectral projection is compact.** For a compact perturbation of a smaller norm operator, the complement of the contour projection is compact when the contour lies in the resolvent set. Source: Breakdown.Spectral.isCompactOperator_one_sub_specProj in Breakdown.Spectral.CompactPart, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/CompactPart.lean#L45).

### Breakdown.Spectral.Complexify

A real Hilbert space is equipped with a concrete complexification, including its scalar action, norm, completeness and conjugation.

**Source namespace:** Breakdown.Spectral.

**The complexification of a real space.** The complexification stores a real part and an imaginary part from the original space. Source: Breakdown.Spectral.Complexification in Breakdown.Spectral.Complexify, line 7. [Data structure](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L7).

**Source namespace:** Breakdown.Spectral.Complexification.

**Two parts determine a complex vector.** Complexified vectors with equal real and imaginary parts are equal. Source: Breakdown.Spectral.Complexification.ext in Breakdown.Spectral.Complexify, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L16).

**Zero in the complexification.** The zero complexified vector has both components zero. Source: anonymous instance in Breakdown.Spectral.Complexify, line 23. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L23).

**Addition in the complexification.** Addition of complexified vectors is componentwise. Source: anonymous instance in Breakdown.Spectral.Complexify, line 24. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L24).

**Negation in the complexification.** Negation of complexified vectors is componentwise. Source: anonymous instance in Breakdown.Spectral.Complexify, line 25. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L25).

**Subtraction in the complexification.** Subtraction of complexified vectors is componentwise. Source: anonymous instance in Breakdown.Spectral.Complexify, line 26. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L26).

**Natural scalar multiplication.** Natural number scalar multiplication acts on both components of a complexified vector. Source: anonymous instance in Breakdown.Spectral.Complexify, line 27. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L27).

**Integer scalar multiplication.** Integer scalar multiplication acts on both components of a complexified vector. Source: anonymous instance in Breakdown.Spectral.Complexify, line 28. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L28).

**Real part of zero.** The real component of the zero complexified vector is zero. Source: Breakdown.Spectral.Complexification.zero_re in Breakdown.Spectral.Complexify, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L30).

**Imaginary part of zero.** The imaginary component of the zero complexified vector is zero. Source: Breakdown.Spectral.Complexification.zero_im in Breakdown.Spectral.Complexify, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L31).

**Real part of a sum.** The real part of a complexified sum is the sum of the real parts. Source: Breakdown.Spectral.Complexification.add_re in Breakdown.Spectral.Complexify, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L32).

**Imaginary part of a sum.** The imaginary part of a complexified sum is the sum of the imaginary parts. Source: Breakdown.Spectral.Complexification.add_im in Breakdown.Spectral.Complexify, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L33).

**Real part of a negative vector.** The real part of a negative complexified vector is the negative real part. Source: Breakdown.Spectral.Complexification.neg_re in Breakdown.Spectral.Complexify, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L34).

**Imaginary part of a negative vector.** The imaginary part of a negative complexified vector is the negative imaginary part. Source: Breakdown.Spectral.Complexification.neg_im in Breakdown.Spectral.Complexify, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L35).

**Real part of a difference.** The real part of a complexified difference is the difference of real parts. Source: Breakdown.Spectral.Complexification.sub_re in Breakdown.Spectral.Complexify, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L36).

**Imaginary part of a difference.** The imaginary part of a complexified difference is the difference of imaginary parts. Source: Breakdown.Spectral.Complexification.sub_im in Breakdown.Spectral.Complexify, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L37).

**The pair underlying complexification.** The map records a complexified vector as its ordered pair of real and imaginary parts. Source: Breakdown.Spectral.Complexification.toProd in Breakdown.Spectral.Complexify, line 39. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L39).

**The underlying pair map is injective.** The real and imaginary pair uniquely identifies the complexified vector. Source: Breakdown.Spectral.Complexification.toProd_injective in Breakdown.Spectral.Complexify, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L41).

**The complexified additive group.** The componentwise operations give the complexification a commutative additive group structure. Source: anonymous instance in Breakdown.Spectral.Complexify, line 46. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L46).

**Complex scalar multiplication.** Complex scalar multiplication acts by the usual real and imaginary component formula. Source: anonymous instance in Breakdown.Spectral.Complexify, line 56. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L56).

**Real part of a complex multiple.** The real part is scalar real part times vector real part minus scalar imaginary part times vector imaginary part. Source: Breakdown.Spectral.Complexification.smul_re in Breakdown.Spectral.Complexify, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L59).

**Imaginary part of a complex multiple.** The imaginary part is scalar imaginary part times vector real part plus scalar real part times vector imaginary part. Source: Breakdown.Spectral.Complexification.smul_im in Breakdown.Spectral.Complexify, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L61).

**The complex module structure.** The componentwise complex scalar action satisfies the complex module laws. Source: anonymous instance in Breakdown.Spectral.Complexify, line 64. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L64).

**Real scalar action on the real part.** Real scalar multiplication scales the real component by that scalar. Source: Breakdown.Spectral.Complexification.real_smul_re in Breakdown.Spectral.Complexify, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L75).

**Real scalar action on the imaginary part.** Real scalar multiplication scales the imaginary component by that scalar. Source: Breakdown.Spectral.Complexification.real_smul_im in Breakdown.Spectral.Complexify, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L78).

**The complexification inner product.** The Hermitian inner product combines the two real inner products and their antisymmetric cross terms. Source: Breakdown.Spectral.Complexification.innerStruct in Breakdown.Spectral.Complexify, line 87. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L87).

**The complexification normed group.** The inner product core supplies the normed additive group structure on the complexification. Source: anonymous instance in Breakdown.Spectral.Complexify, line 113. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L113).

**The complex Hilbert space inner product.** The inner product core gives the complexification its complex inner product space structure. Source: anonymous instance in Breakdown.Spectral.Complexify, line 116. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L116).

**The norm square splits into two parts.** The squared complexification norm is the sum of the squared real and imaginary component norms. Source: Breakdown.Spectral.Complexification.norm_sq_eq in Breakdown.Spectral.Complexify, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L119).

**Bound the real component norm.** The real component norm is at most the full complexified norm. Source: Breakdown.Spectral.Complexification.norm_re_le in Breakdown.Spectral.Complexify, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L125).

**Bound the imaginary component norm.** The imaginary component norm is at most the full complexified norm. Source: Breakdown.Spectral.Complexification.norm_im_le in Breakdown.Spectral.Complexify, line 129. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L129).

**Bound the full norm by component norms.** The complexification norm is at most the sum of the two component norms. Source: Breakdown.Spectral.Complexification.norm_le_norm_re_add_norm_im in Breakdown.Spectral.Complexify, line 133. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L133).

**Norm of a purely real vector.** The complexified vector with zero imaginary component has the original real norm. Source: Breakdown.Spectral.Complexification.norm_mk_zero in Breakdown.Spectral.Complexify, line 139. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L139).

**Completeness of the complexification.** Completeness of the original real space implies completeness of its complexification. Source: anonymous instance in Breakdown.Spectral.Complexify, line 144. [Anonymous instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L144).

**Include the real space.** The continuous real linear inclusion places a real vector in the real component and sets the imaginary component to zero. Source: Breakdown.Spectral.Complexification.ofReal in Breakdown.Spectral.Complexify, line 177. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L177).

**The inclusion retains the real part.** The real component of the included vector is the original vector. Source: Breakdown.Spectral.Complexification.ofReal_re in Breakdown.Spectral.Complexify, line 184. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L184).

**The inclusion has zero imaginary part.** The imaginary component of an included real vector is zero. Source: Breakdown.Spectral.Complexification.ofReal_im in Breakdown.Spectral.Complexify, line 185. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L185).

**The real inclusion preserves norm.** The real space inclusion into its complexification preserves the norm. Source: Breakdown.Spectral.Complexification.norm_ofReal in Breakdown.Spectral.Complexify, line 187. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L187).

**The continuous real part projection.** The real part map is packaged as a continuous real linear map from the complexification. Source: Breakdown.Spectral.Complexification.reCLM in Breakdown.Spectral.Complexify, line 190. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L190).

**Evaluate the real part projection.** The continuous real part map returns the real component. Source: Breakdown.Spectral.Complexification.reCLM_apply in Breakdown.Spectral.Complexify, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L197).

**Conjugation on the complexification.** Conjugation keeps the real component and negates the imaginary component as an additive map. Source: Breakdown.Spectral.Complexification.conj in Breakdown.Spectral.Complexify, line 199. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L199).

**Conjugation keeps the real part.** The real component is unchanged by conjugation. Source: Breakdown.Spectral.Complexification.conj_re in Breakdown.Spectral.Complexify, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L204).

**Conjugation negates the imaginary part.** The imaginary component changes sign under conjugation. Source: Breakdown.Spectral.Complexification.conj_im in Breakdown.Spectral.Complexify, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L205).

**Conjugation preserves the norm.** Complexification conjugation is norm preserving. Source: Breakdown.Spectral.Complexification.norm_conj in Breakdown.Spectral.Complexify, line 207. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L207).

**Conjugation fixes included real vectors.** Conjugation fixes every vector in the image of the real inclusion. Source: Breakdown.Spectral.Complexification.conj_ofReal in Breakdown.Spectral.Complexify, line 212. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L212).

**Every conjugation fixed vector is real.** A complexified vector fixed by conjugation equals the inclusion of its real component. Source: Breakdown.Spectral.Complexification.eq_ofReal_of_conj_eq in Breakdown.Spectral.Complexify, line 215. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Complexify.lean#L215).

### Breakdown.Spectral.ComplexifyMap

Real bounded linear maps are extended to the complexification with formulas for components, norms, composition and compactness.

**Source namespace:** Breakdown.Spectral.Complexification.

**Bound the complexified operator output.** Applying the same real operator to both components is bounded by its operator norm times the complexified vector norm. Source: Breakdown.Spectral.Complexification.norm_mk_le in Breakdown.Spectral.ComplexifyMap, line 11. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L11).

**Complexify a real operator.** The complexified operator applies the original real operator independently to the real and imaginary parts. Source: Breakdown.Spectral.Complexification.map in Breakdown.Spectral.ComplexifyMap, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L25).

**Real part of the complexified operator.** The complexified operator's real component is the original operator applied to the real component. Source: Breakdown.Spectral.Complexification.map_re in Breakdown.Spectral.ComplexifyMap, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L32).

**The imaginary part of an operator.** The complexified operator's imaginary component is the original operator applied to the imaginary component. Source: Breakdown.Spectral.Complexification.map_im in Breakdown.Spectral.ComplexifyMap, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L33).

**Complexification respects operator sums.** Complexifying a sum of real operators gives the sum of their complexifications. Source: Breakdown.Spectral.Complexification.map_add in Breakdown.Spectral.ComplexifyMap, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L35).

**Complexification respects composition.** Complexifying a product of real operators gives the product of their complexifications. Source: Breakdown.Spectral.Complexification.map_mul in Breakdown.Spectral.ComplexifyMap, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L38).

**Complexify the identity operator.** The complexification of the identity operator is the identity. Source: Breakdown.Spectral.Complexification.map_one in Breakdown.Spectral.ComplexifyMap, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L41).

**Complexification respects powers.** Complexification commutes with every natural operator power. Source: Breakdown.Spectral.Complexification.map_pow in Breakdown.Spectral.ComplexifyMap, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L44).

**Bound the complexified operator norm.** The norm of the complexified operator is at most the original real operator norm. Source: Breakdown.Spectral.Complexification.norm_map_le in Breakdown.Spectral.ComplexifyMap, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L49).

**Continuity of the imaginary projection.** The imaginary component map on the complexification is continuous. Source: Breakdown.Spectral.Complexification.continuous_im' in Breakdown.Spectral.ComplexifyMap, line 52. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L52).

**Continuity of pair construction.** Forming a complexified vector from a pair of real vectors is continuous. Source: Breakdown.Spectral.Complexification.continuous_mk' in Breakdown.Spectral.ComplexifyMap, line 59. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L59).

**Complexification preserves compactness.** The complexification of a compact real operator is compact. Source: Breakdown.Spectral.Complexification.isCompactOperator_map in Breakdown.Spectral.ComplexifyMap, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L69).

**The operator respects the real inclusion.** Applying a complexified operator to an included real vector equals including its original image. Source: Breakdown.Spectral.Complexification.map_ofReal in Breakdown.Spectral.ComplexifyMap, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L86).

**The operator commutes with conjugation.** Complexified real operators commute with complexification conjugation. Source: Breakdown.Spectral.Complexification.conj_map in Breakdown.Spectral.ComplexifyMap, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ComplexifyMap.lean#L89).

### Breakdown.Spectral.FiniteSpectrum

Power separation and compactness isolate a spectrum-free annulus beyond the norm bound of the unperturbed operator.

**Source namespace:** Breakdown.Spectral.

**Separate two exponential rates.** For nonnegative smaller rate, some positive integer power makes four times its power smaller than the larger rate's power. Source: Breakdown.Spectral.exists_pow_gap in Breakdown.Spectral.FiniteSpectrum, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/FiniteSpectrum.lean#L10).

**A nonzero power has finite fibers.** The preimage of a complex value under a positive integer power map is finite. Source: Breakdown.Spectral.finite_pow_fiber in Breakdown.Spectral.FiniteSpectrum, line 24. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/FiniteSpectrum.lean#L24).

**Choose a spectrum free annulus.** A compact perturbation of a norm bounded operator admits a closed resolvent annulus between the stated radii above that bound. Source: Breakdown.Spectral.exists_annulus in Breakdown.Spectral.FiniteSpectrum, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/FiniteSpectrum.lean#L70).

### Breakdown.Spectral.ProjectionAlgebra

Separated forward and backward growth estimates force the contour splitting map to be a projection and preserve commuting symmetries.

**Source namespace:** Breakdown.Spectral.

**A strict rate ratio tends to zero.** The product of the smaller exponential growth bound and larger reciprocal decay bound tends to zero. Source: Breakdown.Spectral.tendsto_bound_prod in Breakdown.Spectral.ProjectionAlgebra, line 7. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ProjectionAlgebra.lean#L7).

**Two incompatible rate bounds force zero.** A vector bounded by every term of the vanishing rate product must be zero. Source: Breakdown.Spectral.eq_zero_of_bounds in Breakdown.Spectral.ProjectionAlgebra, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ProjectionAlgebra.lean#L20).

**The rate bounds force a projection.** The forward and backward rate bounds together with the algebraic identities imply that the candidate projection is idempotent. Source: Breakdown.Spectral.idempotent_of_bounds in Breakdown.Spectral.ProjectionAlgebra, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ProjectionAlgebra.lean#L27).

**Commutation extends to operator powers.** An additive map commuting with an operator commutes with every natural power of that operator. Source: Breakdown.Spectral.iterate_comm in Breakdown.Spectral.ProjectionAlgebra, line 45. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ProjectionAlgebra.lean#L45).

**Symmetries commute with the projection.** A norm preserving additive symmetry commuting with the evolution operator also commutes with the projection determined by the two rate bounds. Source: Breakdown.Spectral.map_comm_of_bounds in Breakdown.Spectral.ProjectionAlgebra, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/ProjectionAlgebra.lean#L56).

### Breakdown.Spectral.RealDichotomy

The complex contour split is transported back to the real Hilbert space to assemble the abstract spectral dichotomy.

**Source namespace:** Breakdown.Spectral.

**The real inclusion is injective.** The inclusion of a real space into its complexification is injective. Source: Breakdown.Spectral.ofReal_injective_aux in Breakdown.Spectral.RealDichotomy, line 11. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/RealDichotomy.lean#L11).

### Breakdown.Spectral.Resolvent

Resolvent inverse identities, norm bounds and contour algebra provide the analytic calculus for the spectral projection.

**Source namespace:** Breakdown.Spectral.

**The resolvent is a left inverse.** At a resolvent point, the resolvent times the shifted operator equals the identity. Source: Breakdown.Spectral.resolvent_mul_sub in Breakdown.Spectral.Resolvent, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L11).

**The resolvent is a right inverse.** At a resolvent point, the shifted operator times the resolvent equals the identity. Source: Breakdown.Spectral.sub_mul_resolvent in Breakdown.Spectral.Resolvent, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L18).

**Commutation with the resolvent.** An operator commuting with the original operator also commutes with its resolvent. Source: Breakdown.Spectral.commute_resolvent in Breakdown.Spectral.Resolvent, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L25).

**Multiply the resolvent by the operator.** The operator times its resolvent is the spectral parameter times the resolvent minus the identity. Source: Breakdown.Spectral.mul_resolvent in Breakdown.Spectral.Resolvent, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L38).

**Multiply the resolvent by a power.** An operator power times its resolvent equals the corresponding scalar power times the resolvent minus the finite lower power sum. Source: Breakdown.Spectral.pow_mul_resolvent in Breakdown.Spectral.Resolvent, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L45).

**Continuity on the resolvent set.** The resolvent map is continuous on the resolvent set. Source: Breakdown.Spectral.continuousOn_resolvent in Breakdown.Spectral.Resolvent, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L63).

**Complex derivative of the resolvent.** The resolvent is complex differentiable at each point of the resolvent set. Source: Breakdown.Spectral.differentiableAt_resolvent in Breakdown.Spectral.Resolvent, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L67).

**Resolvent beyond the operator norm.** A complex parameter whose norm exceeds the operator norm bound lies in the resolvent set. Source: Breakdown.Spectral.mem_resolventSet_of_norm_le_lt in Breakdown.Spectral.Resolvent, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L71).

**A lower bound for the shifted operator.** The norm of the shifted operator applied to a vector is at least the parameter norm minus the operator bound times the vector norm. Source: Breakdown.Spectral.norm_le_of_sub_apply in Breakdown.Spectral.Resolvent, line 79. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L79).

**The resolvent norm estimate.** Outside the norm bound the resolvent norm is at most the reciprocal distance from that bound. Source: Breakdown.Spectral.norm_resolvent_le in Breakdown.Spectral.Resolvent, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L89).

**Left multiplication under the contour.** A fixed left operator factor can be moved outside a circle integral of an integrable operator family. Source: Breakdown.Spectral.circleIntegral_mul_left in Breakdown.Spectral.Resolvent, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L103).

**Right multiplication under the contour.** A fixed right operator factor can be moved outside a circle integral of an integrable operator family. Source: Breakdown.Spectral.circleIntegral_mul_right in Breakdown.Spectral.Resolvent, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L110).

**Commutation with the contour integral.** An operator commuting with every member of the integrand family commutes with its circle integral. Source: Breakdown.Spectral.commute_circleIntegral in Breakdown.Spectral.Resolvent, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L117).

**Polynomial contour integrals vanish.** The circle integral of a nonnegative integer power times a fixed operator is zero. Source: Breakdown.Spectral.circleIntegral_pow_smul_const in Breakdown.Spectral.Resolvent, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L128).

**The inverse power contour integral.** The circle integral of the inverse power has the two pi imaginary residue only for the first inverse power and is zero for higher powers. Source: Breakdown.Spectral.circleIntegral_inv_pow_smul_const in Breakdown.Spectral.Resolvent, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Resolvent.lean#L135).

### Breakdown.Spectral.Separation

Separated eigenvalue images and compactness prevent an excessive family of spectral directions outside the unperturbed norm bound.

**Source namespace:** Breakdown.Spectral.

**Separate a new span direction.** A linearly independent sequence supplies a unit bounded vector in each growing span at distance at least one half from the earlier span. Source: Breakdown.Spectral.exists_far_in_span in Breakdown.Spectral.Separation, line 9. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Separation.lean#L9).

**Eigenvalues give separated images.** Distinct eigenvalues yield a bounded vector sequence whose operator images are separated by the stated eigenvalue dependent distance. Source: Breakdown.Spectral.exists_separated_of_eigen in Breakdown.Spectral.Separation, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Separation.lean#L26).

**Compactness forbids excess separation.** A compact perturbation of a norm bounded operator cannot send a unit bounded sequence to images separated by more than twice that bound. Source: Breakdown.Spectral.not_separated_of_compact in Breakdown.Spectral.Separation, line 74. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/Separation.lean#L74).

### Breakdown.Spectral.SpectralPowers

Weighted resolvent contours control forward powers on the inner projection and inverse powers on its complementary spectral part.

**Source namespace:** Breakdown.Spectral.Internal.

**Read the norm on a centered circle.** A point on the circle centered at zero has norm equal to the circle's radius. Source: Breakdown.Spectral.Internal.norm_eq_of_mem_sphere in Breakdown.Spectral.SpectralPowers, line 11. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L11).

**A positive circle avoids zero.** Every point on a positive radius circle centered at zero is nonzero. Source: Breakdown.Spectral.Internal.ne_zero_of_mem_sphere in Breakdown.Spectral.SpectralPowers, line 15. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L15).

**Continuity of inverse powers on a circle.** Inverse integer powers are continuous on every positive radius circle centered at zero. Source: Breakdown.Spectral.Internal.continuousOn_inv_pow in Breakdown.Spectral.SpectralPowers, line 21. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L21).

**A resolvent bound on a compact circle.** If the circle lies in the resolvent set, the resolvent norm has a uniform nonnegative bound on it. Source: Breakdown.Spectral.Internal.exists_bound_resolvent in Breakdown.Spectral.SpectralPowers, line 25. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L25).

**An operator power under the contour.** Multiplying the inverse power weighted resolvent integral by the operator power yields the displayed resolvent integral and residue correction. Source: Breakdown.Spectral.Internal.pow_mul_inv_pow_integral in Breakdown.Spectral.SpectralPowers, line 32. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L32).

**Source namespace:** Breakdown.Spectral.

**The projected powers contour formula.** The operator power times the spectral projection is the normalized contour integral of the corresponding scalar power times the resolvent. Source: Breakdown.Spectral.pow_mul_specProj in Breakdown.Spectral.SpectralPowers, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L67).

**Backward inversion on the complement.** Multiplying the backward contour operator by the forward power gives the complement of the spectral projection. Source: Breakdown.Spectral.pow_mul_backProj in Breakdown.Spectral.SpectralPowers, line 88. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L88).

**Bound the projected forward powers.** The projected forward powers are bounded by a positive constant times the contour radius to that power. Source: Breakdown.Spectral.norm_pow_mul_specProj_le in Breakdown.Spectral.SpectralPowers, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L100).

**Source namespace:** Breakdown.Spectral.Internal.

**Bound the inverse power contour integral.** The normalized inverse power contour integral is bounded by the radius times its inverse power times the resolvent bound. Source: Breakdown.Spectral.Internal.norm_inv_pow_integral_le in Breakdown.Spectral.SpectralPowers, line 118. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L118).

**Source namespace:** Breakdown.Spectral.

**Bound the backward contour operators.** The backward contour operators are bounded by a positive constant times the inverse inner radius to the corresponding power. Source: Breakdown.Spectral.norm_backProj_le in Breakdown.Spectral.SpectralPowers, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralPowers.lean#L126).

### Breakdown.Spectral.SpectralProjection

Contour definitions, annular deformation and large-circle normalization establish the spectral projection and backward operator identities.

**Source namespace:** Breakdown.Spectral.

**The backward contour operator.** The backward operator is the normalized difference of inverse power weighted resolvent integrals over outer and inner circles. Source: Breakdown.Spectral.backProj in Breakdown.Spectral.SpectralProjection, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralProjection.lean#L14).

**An integrable weighted contour.** A continuous scalar weight times the resolvent is circle integrable when the contour lies in the resolvent set. Source: Breakdown.Spectral.circleIntegrable_resolvent in Breakdown.Spectral.SpectralProjection, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralProjection.lean#L18).

**Move the contour through an annulus.** The spectral projection is unchanged when its circle moves through an annulus entirely in the resolvent set. Source: Breakdown.Spectral.specProj_eq_of_annulus in Breakdown.Spectral.SpectralProjection, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralProjection.lean#L26).

**Bound the large contour projection error.** Beyond the operator norm, the projection's distance from the identity has the displayed reciprocal gap bound. Source: Breakdown.Spectral.norm_specProj_sub_one_le in Breakdown.Spectral.SpectralProjection, line 46. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralProjection.lean#L46).

**The large contour equals identity.** The spectral projection equals the identity when the contour radius exceeds the operator norm. Source: Breakdown.Spectral.specProj_large in Breakdown.Spectral.SpectralProjection, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralProjection.lean#L97).

**Commutation with the projection.** Every operator commuting with the original operator commutes with its spectral projection. Source: Breakdown.Spectral.commute_specProj in Breakdown.Spectral.SpectralProjection, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralProjection.lean#L112).

**Commutation with the backward map.** Every operator commuting with the original operator commutes with its backward contour operator. Source: Breakdown.Spectral.commute_backProj in Breakdown.Spectral.SpectralProjection, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectralProjection.lean#L117).

### Breakdown.Spectral.SpectrumEigen

Outside the small operator norm bound, spectral points of its compact perturbation are eigenvalues, and compactness persists through taking powers.

**Source namespace:** Breakdown.Spectral.

**Outer spectral points are eigenvalues.** For a compact perturbation, each spectral point outside the unperturbed norm bound is an eigenvalue. Source: Breakdown.Spectral.hasEigenvalue_of_mem_spectrum in Breakdown.Spectral.SpectrumEigen, line 9. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectrumEigen.lean#L9).

**Powers retain the compact perturbation.** The difference between the perturbed and unperturbed operator powers is compact. Source: Breakdown.Spectral.isCompactOperator_pow_sub_pow in Breakdown.Spectral.SpectrumEigen, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectrumEigen.lean#L50).

**Eigenvalues pass to powers.** An eigenvalue of an operator gives its corresponding power as an eigenvalue of the operator power. Source: Breakdown.Spectral.hasEigenvalue_pow in Breakdown.Spectral.SpectrumEigen, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Spectral/SpectrumEigen.lean#L62).
<!-- /passage:sec-breakdown-spectral -->

