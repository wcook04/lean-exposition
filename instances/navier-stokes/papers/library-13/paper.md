
<!-- passage:front -->
# Library guide 13: Breakdown/CertTorus

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) **13** [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.CertTorus.BilinKernel` to `Breakdown.CertTorus.WindowResidual` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.CertTorus.BilinKernel

This file extends the Leray-kernel representation of the bilinear term from test fields to L6 fields using the L6 times L6 to L3 tensor estimate. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**The Hölder exponents six, six and three.** Proved result. Exponents six and six form the Hölder triple with product exponent three. (`holderTriple_six_six_three`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L14)).

**Tensor-product norms multiply.** Proved result. For vectors p,q ∈ R³, the norm of the tensor with entries pⱼqₖ is at most |p||q|. (`norm_tensor_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L20)).

**The tensor-product map is continuous.** Proved result. The map sending two real vectors p,q to their tensor with entries pⱼqₖ is continuous. (`continuous_tensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L26)).

**Tensor fields are a.e. measurable.** Proved result. Tensor fields are almost-everywhere measurable. (`tensorField_aestronglyMeasurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L32)).

**The pointwise tensor-product norm bound.** Proved result. Almost everywhere, the tensor-product norm is bounded by the product of the two vector norms. (`tensor_nnnorm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L37)).

**The L6 to L3 tensor-product bound.** Proved result. Tensor L3 norms obey the L6 product bound. (`eLpNorm_tensorField_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L45)).

**Two L6 fields give an L3 tensor.** Proved result. If a,b ∈ L⁶(R³;R³), their tensor product a⊗b belongs to L³(R³). (`tensorField_memLp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L54)).

**Kernel convolution preserves subtraction.** Proved result. If the Leray-kernel integrals for tensors F and G are integrable in every output component, convolution with F−G equals the convolution with F minus that with G. (`kernelConv_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L59)).

**Convolutions agree for a.e. equal fields.** Proved result. Almost-equal fields give equal convolutions. (`kernelConv_tensor_congr_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L72)).

**Bilinear splitting of tensor differences.** Proved result. Quadratic tensor differences split bilinearly. (`tensor_sub_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L81)).

**Tensor differences obey an L3 estimate.** Proved result. For w,v ∈ L⁶, the tensor difference obeys ‖w⊗w−v⊗v‖₃ ≤ ‖w−v‖₆(‖w‖₆+‖v‖₆). (`toReal_eLpNorm_tensor_sub_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L87)).

**L6 convergence gives kernel convergence.** Proved result. If Leray-kernel convolution maps every L³ tensor to an integrable pointwise value bounded by Cτ⁻¹ times its L³ norm, convergence wₙ → v in L⁶ implies pointwise convergence of the convolutions of wₙ⊗wₙ to that of v⊗v. (`kernelConv_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L117)).

**From test kernels to the bilinear map.** Proved result. Test-kernel equality extends to the bilinear map. (`bilinKernel_of_test_decay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinKernel.lean#L152)).

### Breakdown.CertTorus.BilinLeibnizOfShift

This file derives the bilinear Leibniz rule from translation covariance and convergence of translation difference quotients. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Continuity from quotient convergence.** Proved result. Difference-quotient convergence gives continuity. (`tendsto_of_quotient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinLeibnizOfShift.lean#L12)).

**Bilinear Leibniz rules from covariance.** Proved result. Covariance gives the bilinear Leibniz rule. (`leibniz_of_covariant`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinLeibnizOfShift.lean#L25)).

**Leibniz rules for shift derivatives.** Proved result. Translation covariance and difference-quotient differentiation imply the bilinear Leibniz rule. (`bilinLeibnizOfShift_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinLeibnizOfShift.lean#L47)).

### Breakdown.CertTorus.BilinSymbol

This file identifies the physical bilinear operator with its Fourier velocity symbol and establishes the integrability and conjugate symmetry needed for that identification. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Fourier symmetry and solenoidality a.e..** Proved result. Almost everywhere, each Fourier representative has conjugate symmetry and zero longitudinal projection. (`sig_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L22)).

**The inverse-frequency velocity symbol.** Proved result. Almost everywhere in frequency space, the velocity symbol is the Fourier representative divided by 2π times frequency radius. (`velSymbol_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L44)).

**Recovering the Fourier symbol a.e..** Proved result. Multiplying the velocity symbol by 2π times frequency radius recovers the Fourier representative almost everywhere. (`smul_velSymbol_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L52)).

**Velocity symbols are a.e. measurable.** Proved result. Velocity symbols are almost-everywhere measurable. (`aestronglyMeasurable_velSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L60)).

**Weighted integrability of symbols.** Proved result. Velocity symbols have weighted integrability. (`memLp_weight_velSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L67)).

**Velocity symbols are solenoidal.** Proved result. For each real divergence-free velocity in the homogeneous H¹ space, the chosen Fourier representative f satisfies ξ·f(ξ) = 0 and f(−ξ) = conj f(ξ) at every frequency. (`isSolenoidal_velSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L74)).

**Integrability of weighted symbols.** Proved result. Frequency-weighted velocity symbols are integrable. (`integrable_freq_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L88)).

**Frequency multipliers for derivatives.** Proved result. Spatial derivatives are frequency multipliers. (`derivSymbol_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L93)).

**Coordinate velocity multipliers are L2.** Proved result. For each coordinate, 2πi times that frequency coordinate times the velocity Fourier symbol is square integrable. (`memLp_two_freq_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L107)).

**Physical and abstract derivatives a.e..** Proved result. Under the Wiener and smoothness assumptions, the abstract first derivative equals the physical coordinate derivative almost everywhere. (`partialX_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L111)).

**Squaring a half power.** Proved result. Squaring the half power recovers its value. (`rpow_half_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L135)).

**The half power of a square.** Proved result. The half power of a square recovers its value. (`sq_rpow_half`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L139)).

**Weighted bounds for convolution squares.** Proved result. Convolution squares obey a weighted bound. (`enorm_convC_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L143)).

**Convolution keeps square integrability.** Proved result. Convolution preserves square integrability. (`memLp_two_convC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L167)).

**Advection symbol is square integrable.** Proved result. If a vector-valued Fourier symbol is integrable and each coordinate multiplier 2πiηⱼf(η) lies in L², its advection symbol lies in L². (`memLp_two_advectionSymbol_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L217)).

**Advection symbol has conjugate symmetry.** Proved result. If a Fourier symbol is divergence free and satisfies the conjugate symmetry for a real field, its advection symbol satisfies the same symmetry: A(−ξ) = conj A(ξ). (`advectionSymbol_herm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L245)).

**Bilinear operator represents its form.** Proved result. For τ > 0 and u,v,ψ in the homogeneous H¹ space, the inner product of the bilinear heat-flow operator Bτ(u,v) with ψ equals its defining bilinear form evaluated at (u,v,ψ). (`bilinX_inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L256)).

**Advection from directional derivatives.** Proved result. Advection is the sum of directional derivatives. (`advectionAt_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L263)).

**The bilinear velocity symbol.** Proved result. The bilinear form's velocity symbol is the projected Fourier advection symbol under the source's integrability assumptions. (`bilinSymbolOfVelocity_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinSymbol.lean#L275)).

### Breakdown.CertTorus.BilinTestKernel

This file matches the Leray-kernel pairing with the bilinear test form by integration by parts against divergence-free test fields. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Test pairings determine the field.** Proved result. Two elements of the homogeneous H¹ space are equal if they have the same inner product with every embedded smooth compactly supported divergence-free test field. (`eq_of_inner_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L14)).

**Heat evolution of the test Laplacian.** Proved result. Heat evolution transports the test Laplacian. (`isLapOf_heat_embed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L28)).

**The heat test-field representation a.e..** Proved result. The transformed test field equals the heat convolution of the negative scalar Laplacian of the test field almost everywhere. (`phi_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L45)).

**Bilinear pairing as the transport form.** Proved result. The bilinear test pairing is the transport form. (`inner_bilin_test`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L53)).

**Coordinate map respects derivatives.** Proved result. Coordinate projection commutes with derivatives. (`coord_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L75)).

**Inner products are coordinate sums.** Proved result. For u,v ∈ R³, the Euclidean inner product equals ∑ⱼuⱼvⱼ. (`inner_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L80)).

**Integration by parts for transport.** Proved result. Divergence-free transport integrates by parts. (`advect_by_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L83)).

**Selecting coordinates by unit vectors.** Proved result. Pairing with a unit vector selects a coordinate. (`inner_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L139)).

**Pairing kernels with test fields.** Proved result. Under the kernel assumptions, pairing the quadratic kernel convolution with a test field equals minus the transport pairing with the heat-evolved test field's derivative. (`kernel_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L142)).

**The bilinear test-kernel identity.** Proved result. The heat-test, kernel-contraction, decay, oddness, boundedness, and measurability assumptions imply the bilinear test-kernel identity. (`bilinTestKernel_of_kernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/BilinTestKernel.lean#L248)).

### Breakdown.CertTorus.ClassFormOfWeights

This file converts weighted velocity, derivative and pressure estimates into the decay class used by the smooth periodic-profile theorem. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Weighted bounds give inverse-power decay.** Proved result. A uniform weighted bound with natural exponent k gives pointwise norm at most A/(1+radius)ᵏ at every time. (`norm_le_of_weightedBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/ClassFormOfWeights.lean#L9)).

**Coordinate is bounded by the vector norm.** Proved result. The absolute value of any coordinate is at most the Euclidean norm of the vector. (`abs_coord_le_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/ClassFormOfWeights.lean#L18)).

**Vectors as coordinate basis sums.** Proved result. Every vector v ∈ R³ equals the sum ∑ⱼvⱼeⱼ of its Cartesian components times the coordinate unit vectors. (`eq_sum_coord_smul_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/ClassFormOfWeights.lean#L25)).

**Coordinate bounds control operator norm.** Proved result. If a real linear functional is bounded by B on each coordinate unit vector, its operator norm is at most 3B. (`norm_le_three_mul_of_coords`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/ClassFormOfWeights.lean#L29)).

**Decay classes from weighted bounds.** Proved result. Weighted velocity, gradient, Hessian, and pressure-gradient estimates imply the decay-class bound with their respective inverse-radius powers. (`classFormOfWeights_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/ClassFormOfWeights.lean#L54)).

### Breakdown.CertTorus.DecayStatements

This file states the kernel-integral, derivative-bootstrap and Newtonian-pressure estimates that turn a regular profile into a profile with quantitative spatial decay. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**A tensor shifted by similarity variables.** Definition. The tensor similarity shift subtracts log(1+τ) from time and divides spatial coordinates by the square root of 1+τ. (`tensorShift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L11)).

**The weighted profile integral operator.** Definition. The profile operator is the negative positive-time integral of the kernel convolution of the similarity-shifted tensor, weighted by (1+τ) to the power −β. (`profileOp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L14)).

**The time-dependent tensor product.** Definition. The paired tensor at each time is the pointwise outer product of the two vector fields. (`pairTensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L17)).

**A directional derivative of a tensor.** Definition. The directional tensor differentiates each time slice in the chosen spatial direction. (`directionalTensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L20)).

**Bounded jointly measurable tensor fields.** Proposition definition. A bounded measurable tensor has joint time-space measurability and one norm bound valid at every time and point. (`IsBoundedMeasurableTensor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L24)).

**The spatial weighted kernel integral.** Definition. The weighted kernel integral combines fourth-power decay in distance plus square-root time with a radial source weight at the similarity scale. (`kernelWeightIntegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L27)).

**The outer-region kernel majorant.** Definition. The far majorant is inverse square-root time multiplied by the smaller of one and the similarity-scale-to-radius ratio to power γ. (`farMajorant`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L30)).

**The near-region kernel majorant.** Definition. The near majorant is R³/(R+√τ)⁴ multiplied by the smaller of one and the similarity-scale-to-radius ratio to power min(γ,3). (`nearMajorant`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L33)).

**The quadratic source for pressure.** Definition. The pressure source is the double coordinate sum of each velocity derivative times the transposed derivative entry. (`pressureSource`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L36)).

**The double divergence of a tensor.** Definition. The double-divergence source sums the matching second spatial partials of all tensor components. (`divDivSource`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L40)).

**A component of the Newtonian gradient.** Definition. A Newtonian gradient component convolves the corresponding fundamental-solution kernel derivative with the scalar source. (`newtonGradientComp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L43)).

**A smooth ball cutoff.** Definition. The ball cutoff applies the smooth transition to 2 minus squared radius divided by the cutoff radius squared. (`ballCutoff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L46)).

**A cutoff near the observation point.** Definition. The near cutoff applies the smooth transition around the observation point at a scale determined by the larger of one and its radius. (`nearCutoff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L49)).

**The kernel mass bound.** Proposition definition. This proposition requires the fourth-power kernel majorant to be integrable and have mass at most five divided by square-root time for positive time. (`KernelMassBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L52)).

**The integral bound for radial weights.** Proposition definition. For nonnegative γ different from three, this proposition bounds the radial weight integral on a ball by its volume scale times the appropriate minimum power. (`RadialWeightBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L57)).

**Splitting the weighted kernel integral.** Proposition definition. For nonnegative γ different from three, this proposition requires integrability and bounds the weighted kernel integral by inverse square-root time and by the far-plus-near split at large radius. (`InnerSplitBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L61)).

**The far-majorant time integral bound.** Proposition definition. For derivative orders at most two and γ different from order plus one, this proposition bounds the far-majorant time integral by radius to the negative minimum decay order. (`OuterFarBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L68)).

**The near-majorant time integral bound.** Proposition definition. For derivative orders at most two, this proposition bounds the near-majorant time integral by radius to the negative minimum of γ and order plus one. (`OuterNearBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L74)).

**Integrability of the small-time kernel.** Proposition definition. This proposition requires the inverse-square-root small-time weight with its additional large-time decay to be integrable over all positive times. (`SmallTimeIntegrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L80)).

**Weighted decay of the profile operator.** Proposition definition. Under the Leray kernel bound and excluding the two critical exponents, this proposition transfers tensor decay γ to profile-operator decay min(γ,n+1) for orders n at most two. (`OpWeightedBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L83)).

**Linearity of the profile operator.** Proposition definition. Under the kernel bound, this proposition requires additivity of the profile operator on bounded measurable tensors for β at least one and scalar homogeneity. (`OpLinear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L88)).

**Measurability of the profile operator.** Proposition definition. This proposition requires joint measurability of a tensor to imply joint measurability of its weighted profile integral. (`OpMeasurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L96)).

**Decay orders add in tensor products.** Proposition definition. This proposition adds the two nonnegative decay exponents and multiplies their constants when taking a tensor product. (`TensorWeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L100)).

**The first three-quarter-power decay gain.** Proposition definition. Under the kernel bound, this proposition requires a bounded measurable, uniformly vanishing solution of the nonlinear profile equation to gain decay of order three quarters. (`NeumannDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L104)).

**Differentiation under kernel convolution.** Proposition definition. Under the kernel bound, this proposition moves spatial differentiation through positive-time kernel convolution of a C¹ tensor with bounded value and derivative. (`KernelConvDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L109)).

**Differentiate the profile integral.** Proposition definition. Under the kernel bound and beta at least one, a bounded C1 tensor with bounded spatial derivative has a differentiable profile operator whose derivative uses the directional tensor and raises beta by one half. (`ProfileOpDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L115)).

**Weighted integrals for derivatives.** Proposition definition. Under the kernel bound, this proposition represents first and second derivatives of a regular orbit field by profile integrals with weights three halves and two. (`DerivRepresentation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L122)).

**The first-derivative decay bootstrap.** Proposition definition. Under the kernel bound, this proposition uses smoothness, uniform derivative bounds, order-one field decay, and the derivative representation to obtain order-two gradient decay. (`FirstDerivBootstrap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L129)).

**The second-derivative decay bootstrap.** Proposition definition. Under the kernel bound, this proposition combines smoothness, bounded derivatives, orders one and two decay, and the second-derivative representation to obtain order-three Hessian decay. (`SecondDerivBootstrap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L135)).

**Pressure has the negative source.** Proposition definition. This proposition requires the pressure Laplacian of a smooth orbit field to equal the negative quadratic velocity-gradient source. (`PressureSumSecondPartials`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L143)).

**Pressure source is a double divergence.** Proposition definition. This proposition identifies the quadratic pressure source with the double divergence of the velocity tensor for a smooth orbit field. (`PressureSourceDivDiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L147)).

**Pressure source has fourth-order decay.** Proposition definition. This proposition turns order-two velocity-gradient decay into order-four decay of the smooth pressure source. (`PressureSourceBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L151)).

**Tensor derivatives decay to order two.** Proposition definition. This proposition requires velocity decay through derivative order two to give tensor derivative decay of orders two, three, and four. (`TensorDerivDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L157)).

**The harmonic mean-value identity.** Proposition definition. This proposition requires a smooth harmonic function to equal each smaller-radius mollified average centered inside its harmonic ball. (`HarmonicMeanValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L164)).

**An L2 bound for the harmonic gradient.** Proposition definition. This proposition bounds the gradient of a smooth harmonic function at a ball center by its L2 gradient norm on the ball times radius to the power −3/2. (`HarmonicGradientBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L169)).

**Truncated Newtonian gradients converge.** Proposition definition. For a smooth source with fourth-order decay, this proposition requires truncated Newtonian gradients to have uniform second-order decay and converge componentwise to the full Newtonian gradient. (`TruncatedNewton`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L175)).

**The signed Newtonian pressure gradient.** Proposition definition. This proposition identifies the gradient of a smooth pressure with the negative Newtonian gradient when its Laplacian is the negative source, its gradient is L2, and the source has fourth-order decay. (`PressureIdentification`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L183)).

**The near Newtonian term has cubic decay.** Proposition definition. This proposition requires the near-cutoff Newtonian gradient of a continuous fourth-order-decaying source to be integrable and decay cubically. (`NewtonNear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L189)).

**The far Newtonian term has cubic decay.** Proposition definition. This proposition requires the far Newtonian term of a C² tensor with derivative decay orders two through four to be integrable and decay cubically. (`NewtonFar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L195)).

**The far Newtonian kernel weight.** Definition. The far kernel weight is the Newtonian gradient kernel multiplied by one minus the near cutoff. (`farWeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L203)).

**Two far-term integrations by parts.** Proposition definition. For a C² tensor with the required decay, this proposition transfers both divergence derivatives onto the far kernel by integration by parts. (`NewtonFarIdentity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L206)).

**The differentiated far-kernel estimate.** Proposition definition. This proposition bounds the second-derivative far-kernel pairing with a second-order-decaying tensor by cubic inverse-radius decay. (`NewtonFarEstimate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L215)).

**Weighted bounds imply the decay class.** Proposition definition. This proposition turns weighted velocity derivative bounds of orders one, two, and three and cubic pressure-gradient decay into the target decay class. (`ClassFormOfWeights`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L222)).

**The weighted bilinear profile operator.** Proved result. The bilinear profile operator equals the weighted profile operator at weight one applied to the paired tensor. (`profileBilin_eq_profileOp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DecayStatements.lean#L229)).

### Breakdown.CertTorus.Defs

This file defines the heat-Leray kernel, the similarity-profile bilinear operator and the weighted bounds used by the torus route. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**The three-dimensional heat kernel.** Definition. The three-dimensional heat kernel is the Gaussian with normalization (4πτ) to the power −3/2 and exponent −|x|²/(4τ). (`heatKernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L14)).

**The third derivative of the heat kernel.** Definition. The third heat-kernel derivative combines the three Kronecker-delta linear terms over 4ρ² and subtracts the cubic coordinate product over 8ρ³, all multiplied by the heat kernel. (`heatKernelThird`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L17)).

**The heat-Leray derivative kernel.** Definition. The heat-Leray derivative kernel adds the appropriate first Gaussian derivative to the positive-tail time integral of its third derivative. (`lerayKernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L22)).

**Contracting kernels with tensor fields.** Definition. Kernel convolution contracts the three-index Leray kernel with both tensor indices and integrates each resulting vector component over space. (`kernelConv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L25)).

**Pointwise tensor product of two fields.** Definition. The tensor product has component j,k equal to the j component of the first field times the k component of the second. (`tensorField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L28)).

**The similarity shift of a field.** Definition. The field similarity shift subtracts log(1+τ) from time and rescales space by the reciprocal square root of 1+τ. (`similarityShift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L30)).

**The bilinear similarity-profile operator.** Definition. The bilinear profile map is the negative positive-time kernel integral of the two shifted fields' tensor product with weight 1/(1+τ). (`profileBilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L33)).

**Uniform spatially weighted bounds.** Proposition definition. A weighted bound requires (1+radius) to power γ times the field norm to stay below one constant uniformly in time and space. (`WeightedBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L36)).

**Uniform spatial derivative bounds.** Proposition definition. A uniform derivative bound controls every spatial derivative from order zero through n at every time and point. (`UniformDerivBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L39)).

**Uniform vanishing at spatial infinity.** Proposition definition. Uniform tail vanishing requires one radius beyond which the field norm is at most ε at every time. (`TailVanishes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L42)).

**Orbit fields with the profile identity.** Proposition structure. A regular orbit field extends the smooth orbit assumptions by requiring the field to equal its nonlinear bilinear profile integral. (`IsRegularOrbitField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/Defs.lean#L58)).

### Breakdown.CertTorus.DerivAlgebra

This file records algebraic rules for coordinate derivative multipliers, including permutation and concatenation of derivative indices. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Affine Fourier sums almost everywhere.** Proved result. Fourier representatives preserve affine sums almost everywhere. (`symX_add_smul_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivAlgebra.lean#L11)).

**Zero-order derivative multiplier is one.** Proved result. The Fourier multiplier corresponding to a derivative of order zero is the constant 1 at every frequency. (`monoSymbol_fin_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivAlgebra.lean#L18)).

**Derivative permutations keep the symbol.** Proved result. Permuting derivatives preserves the multiplier. (`monoSymbol_comp_perm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivAlgebra.lean#L21)).

**Appending derivatives multiplies symbols.** Proved result. Concatenating two lists of coordinate derivatives multiplies their Fourier multipliers: mαβ(ξ) = mα(ξ)mβ(ξ). (`monoSymbol_append`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivAlgebra.lean#L26)).

**The algebra of abstract derivatives.** Proved result. Abstract derivatives are unique, include order zero, respect affine combinations and permutations, and compose by appending coordinate directions. (`derivAlgebra_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivAlgebra.lean#L32)).

### Breakdown.CertTorus.DerivClosed

This file proves that the abstract derivative relation is closed under convergence in the underlying Hilbert space. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Passing convergence to ambient L2.** Proved result. Convergence passes to the ambient L2 space. (`tendsto_coe_of_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivClosed.lean#L14)).

**Fourier constraints pass to a.e. limits.** Proved result. Almost-everywhere limits preserve Fourier constraints. (`mem_sig_of_ae_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivClosed.lean#L18)).

**Bounded derivatives survive a limit.** Proved result. If a sequence of fields converges in norm and a fixed iterated coordinate derivative has a uniform norm bound along the sequence, the limit has that derivative with the same bound. (`derivClosed_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivClosed.lean#L67)).

### Breakdown.CertTorus.DerivHeat

This file realizes derivatives of heat evolution as bounded Fourier multipliers and obtains the factorial short-time derivative estimate. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Conjugation conjugates a scalar factor.** Proved result. Complex conjugation of a scalar multiple satisfies conj(cz) = conj(c)conj(z) for every complex scalar and vector. (`conjVec_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L16)).

**Longitudinal projection respects scalars.** Proved result. Projection onto the frequency direction ξ commutes with multiplication of a complex vector by any complex scalar. (`longitudinal_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L20)).

**Symbol obeying constraints lies in Sig.** Proved result. A symbol satisfying constraints lies in Sig. (`mem_sig_of_symbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L28)).

**Conjugation reverses the frequency.** Proved result. Conjugating the coordinate derivative symbol at the negated frequency recovers its value at the original frequency. (`conj_monoSymbol_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L48)).

**Derivative symbols are continuous.** Proved result. Every coordinate-derivative multiplier ∏ⱼ2πiξαⱼ is continuous in the frequency ξ. (`continuous_monoSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L57)).

**Derivative symbols have a power bound.** Proved result. The norm of an order-n coordinate derivative symbol is at most (2π times the frequency norm) to the n-th power. (`norm_monoSymbol_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L61)).

**Heat decay dominates polynomial growth.** Proved result. For positive time and nonnegative radius, rⁿ exp(−tr²) is at most n! times t to power −n/2. (`pow_mul_exp_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L74)).

**Heat symbols have factorial bounds.** Proved result. At positive time, the heat-damped order-n derivative symbol is bounded at every frequency by n! times time to the power -n/2. (`heatSymbol_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L109)).

**Fourier heat evolution a.e..** Proved result. For positive time, heat evolution multiplies the Fourier representative by the Gaussian heat factor almost everywhere. (`heat_symX`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L125)).

**Heat evolution commutes with derivatives.** Proved result. If y is the weak derivative of x for a fixed list of spatial coordinates in the divergence-free homogeneous H¹ space, heat evolution preserves that derivative relation. For all real t the operator uses the Fourier factor exp(−4π²max(t,0)|ξ|²), so it is the identity when t ≤ 0. (`heat_comm_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L131)).

**The heat derivative multiplier.** Definition. The heat derivative multiplier is the coordinate derivative symbol multiplied by the Gaussian heat factor. (`heatDerivSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L137)).

**Heat derivative multiplier is continuous.** Proved result. For every derivative multi-index and real t, its multiplier times exp(−4π²max(t,0)|ξ|²) is continuous in ξ. (`continuous_heatDerivSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L140)).

**Heat derivatives have conjugate parity.** Proved result. The heat-derivative multiplier m satisfies conj(m(t,−ξ)) = m(t,ξ) for every real t and frequency ξ. (`conj_heatDerivSymbol_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L145)).

**Pointwise action of multiplier operators.** Proved result. Multiplier operators have their pointwise action. (`symbol_realized`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L152)).

**The heat derivative as an L2 operator.** Definition. The L2 heat derivative operator multiplies each frequency value by the heat derivative symbol. (`heatDerivL2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L159)).

**The heat multiplier acts a.e..** Proved result. The L2 heat derivative equals multiplication by its heat derivative symbol almost everywhere. (`heatDerivL2_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L162)).

**Heat derivatives preserve constraints.** Proved result. At positive time, the heat-derivative multiplier preserves conjugate symmetry and the zero longitudinal component of an admissible L2 Fourier field. (`heatDerivL2_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L166)).

**Heat multipliers realize derivatives.** Proved result. At positive time, multiplying Fourier data by the heat factor and the coordinate derivative symbol realizes the corresponding abstract derivative of the heat-evolved field. (`heatDerivL2_isDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L171)).

**Factorial bounds for heat derivatives.** Proved result. For positive time and inputs in the stated Fourier subspace, the L2 norm of the order-n heat derivative is at most n! times time to the power -n/2 times the input L2 norm. (`heatDerivL2_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L181)).

**Heat evolution gains bounded derivatives.** Proved result. At positive time, heat evolution has every order-n coordinate derivative with norm at most n! times time to the power -n/2 times the input norm. (`heat_deriv_exists`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L188)).

**Heat derivative formulas and bounds.** Proved result. Positive-time heat evolution gains derivatives of every order with the heat multiplier and factorial norm bounds. (`derivHeat_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivHeat.lean#L196)).

### Breakdown.CertTorus.DerivIntegral

This file truncates derivative multipliers to bounded multipliers so that abstract derivatives can be passed through interval integrals. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Complex multiplication as scalar action.** Proved result. Complex multiplication acts as scalar action. (`cmul_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L13)).

**The scalar multiplication norm bound.** Proved result. The operator norm of multiplication by a complex scalar is at most that scalar's norm. (`norm_cmul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L15)).

**Scalar multiplication keeps subtraction.** Proved result. Scalar multiplication preserves subtraction. (`cmul_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L19)).

**Continuity of scalar multiplication.** Proved result. Scalar multiplication depends continuously. (`continuous_cmul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L23)).

**A bounded Fourier multiplier operator.** Definition. The Fourier multiplier operator applies complex scalar multiplication by the supplied symbol at each frequency. (`multOp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L28)).

**Fourier multipliers act pointwise a.e..** Proved result. Fourier multipliers act pointwise almost everywhere. (`multOp_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L31)).

**Derivative multipliers are continuous.** Proved result. The Fourier multiplier associated with any finite list of Cartesian derivatives is continuous in ξ. (`continuous_monoSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L41)).

**A derivative symbol cut off by size.** Definition. The truncated derivative symbol equals the full symbol when its norm is at most N and zero otherwise. (`truncSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L45)).

**Cutoff indicator for a derivative symbol.** Definition. The derivative cutoff is one when the symbol norm is at most N and zero otherwise. (`truncCut`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L48)).

**Measurable truncated derivative symbols.** Proved result. For every derivative multi-index and truncation level N, the truncated Fourier derivative multiplier is measurable. (`measurable_truncSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L51)).

**Measurable derivative cutoffs.** Proved result. Derivative cutoff indicators are measurable. (`measurable_truncCut`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L56)).

**The threshold bounds a truncated symbol.** Proved result. The norm of the derivative symbol truncated at threshold N is at most N at every frequency. (`norm_truncSymbol_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L61)).

**A cutoff symbol has norm at most one.** Proved result. For every derivative multi-index, truncation level and frequency, the scalar cutoff used for the truncated derivative multiplier has modulus at most one. (`norm_truncCut_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L68)).

**Truncated integral derivatives a.e..** Proved result. Truncated derivative symbols pass through the interval integral as an almost-everywhere identity of Fourier representatives. (`truncate_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L73)).

**Derivatives of interval integrals.** Proved result. Derivatives pass through the interval integral. (`derivIntegral_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivIntegral.lean#L110)).

### Breakdown.CertTorus.DerivRepresentation

This file differentiates the tensor-product representation of a regular orbit to obtain the weighted profile formulas for its first two spatial derivatives. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Outer product as a bounded bilinear map.** Definition. The outer-product bilinear map sends two spatial vectors to the tensor of all pairwise coordinate products. (`outerProductMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivRepresentation.lean#L10)).

**Outer-product map has norm at most one.** Proved result. The bilinear map sending vectors u,v to their outer product has operator norm at most one. (`outerProductMap_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivRepresentation.lean#L25)).

**Tensor derivatives have a uniform bound.** Proved result. If f is C² and its derivatives of orders zero, one and two are uniformly bounded by C, the corresponding derivatives of f⊗f are uniformly bounded by 4C². (`norm_iteratedFDeriv_outer_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivRepresentation.lean#L28)).

**Differentiate a fixed derivative column.** Proved result. If the derivative map is differentiable, applying it to a fixed vector has derivative equal to the second derivative with that fixed vector in its second input. (`hasFDerivAt_fderiv_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivRepresentation.lean#L49)).

**Represent two profile derivatives.** Proved result. The profile-operator differentiation rule represents the first and second spatial derivatives of a regular orbit field by directional tensor operators with weights three halves and two. (`derivRepresentation_of_op`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivRepresentation.lean#L54)).

### Breakdown.CertTorus.DerivSobolev

This file equates homogeneous Sobolev energy with the sum of the L2 energies of all coordinate derivatives of the prescribed order. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Derivative energy factors by coordinate.** Proved result. The squared norm of a coordinate derivative symbol is the product of the squared factors 2π times each selected frequency coordinate. (`norm_monoSymbol_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L14)).

**Sum derivative energies into a power.** Proved result. Summing squared order-n derivative symbols over all coordinate lists gives (2π times the frequency norm) to the power 2n. (`sum_norm_monoSymbol_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L20)).

**A radial bound for derivative symbols.** Proved result. A coordinate derivative symbol of order n has squared norm at most (2π) to power 2n times frequency radius to power 2n. (`norm_monoSymbol_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L30)).

**Conjugate symmetry of derivative symbols.** Proved result. The conjugate of a derivative multiplier at the negative frequency equals that multiplier at the original frequency. (`conj_monoSymbol_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L36)).

**Derivative multipliers are continuous.** Proved result. For any finite list of coordinate derivatives, the associated Fourier multiplier is continuous in frequency. (`continuous_monoSymbol`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L44)).

**Conjugation conjugates scalar factors.** Proved result. For a complex scalar c and vector z, conj(cz) equals conj(c)conj(z). (`conjVec_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L48)).

**Longitudinal projection respects scalars.** Proved result. The longitudinal projection onto the direction of ξ is complex linear: projection of cz equals c times the projection of z. (`longitudinal_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L52)).

**L2 norm equals integrated square energy.** Proved result. For an L² complex vector field f in frequency space, the integral of its squared pointwise norm equals the square of its L² norm. (`lintegral_enorm_sq_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L57)).

**L2 symbols from finite Sobolev energy.** Proved result. Finite Sobolev energy gives L2 multipliers. (`memLp_monoSymbol_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L64)).

**L2 derivative data keep the constraints.** Proved result. An L2 field equal almost everywhere to a coordinate derivative multiplier times admissible Fourier data retains conjugate symmetry and zero longitudinal component. (`monoSymbol_smul_mem_sig`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L87)).

**Finite Sobolev energy gives derivatives.** Proved result. If the order-n Fourier-weighted energy of x is finite, every prescribed n-fold Cartesian derivative of x exists as an element of the same homogeneous H¹ space. (`exists_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L111)).

**Normalize the derivative square sum.** Proved result. Frequency norm to the power 2n times the vector square norm equals (2π) to the power -2n times the sum of all order-n derivative-multiplier square norms. (`weight_mul_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L117)).

**Sobolev energy as a normalized sum.** Proved result. The homogeneous Sobolev square energy equals (2π) to the power -2n times the sum of the integrals of squared norms of all order-n coordinate derivative multipliers applied to the Fourier field. (`homSob_eq_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L130)).

**Sobolev control and derivative bounds.** Proved result. At each order, finite homogeneous Sobolev energy gives all coordinate derivatives, and a shared derivative norm bound bounds that energy by an order-dependent constant times the bound squared. (`derivSobolev_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DerivSobolev.lean#L147)).

### Breakdown.CertTorus.DiffQuotient

This file characterizes the abstract coordinate derivative by translation difference quotients and proves the equivalence using their Fourier multipliers. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**The exponential difference quotient.** Definition. The exponential difference quotient is (exp(i c t)−1)/t with totalized division at zero. (`phaseSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L16)).

**The Fourier quotient remainder.** Definition. The Fourier quotient remainder multiplies the representative by the exponential quotient minus its limiting linear frequency multiplier. (`slopeRemainder`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L19)).

**The Fourier phase of a coordinate shift.** Proved result. A shift by minus t times a coordinate unit vector has Fourier phase exp(i 2π ξⱼ t). (`phase_neg_smul_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L22)).

**One derivative multiplies by 2πiξ.** Proved result. The multiplier for a single coordinate derivative is 2πi times the corresponding frequency coordinate. (`monoSymbol_single`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L32)).

**Frequency bounds exponential quotients.** Proved result. The norm of (exp(i c t)−1)/t is at most |c| for every real step, using totalized division at zero. (`norm_phaseSlope_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L38)).

**The phase quotient tends to its slope.** Proved result. The complex exponential difference quotient tends to i times its real frequency as the nonzero step tends to zero. (`tendsto_phaseSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L48)).

**Fourier shift-quotient multipliers a.e..** Proved result. For nonzero shift size, the translation difference quotient acts almost everywhere by the exponential phase quotient multiplier. (`quotient_coe_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L61)).

**A majorant for quotient remainders.** Proved result. Difference-quotient remainders have a majorant. (`norm_slopeRemainder_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L71)).

**Frequency coordinates are continuous.** Proved result. Each Cartesian frequency coordinate ξ ↦ ξⱼ is continuous on R³. (`continuous_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L85)).

**Measurable quotient-remainder energy.** Proved result. Difference-quotient remainder energy is measurable. (`aemeasurable_slopeRemainder`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L88)).

**Quotient remainders tend to zero.** Proved result. At each fixed frequency, the squared extended norm of the coordinate difference-quotient remainder tends to zero as the nonzero step tends to zero. (`tendsto_slopeRemainder`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L98)).

**Derivatives give shift-quotient limits.** Proved result. The difference quotient built from shifts by minus the step in a coordinate converges in norm to the corresponding abstract derivative as the nonzero step tends to zero. (`tendsto_of_isDerivX`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L110)).

**Shift-quotient limits give derivatives.** Proved result. If the difference quotients formed from shifts by minus the coordinate step converge in norm as the nonzero step tends to zero, their limit is the corresponding abstract derivative. (`isDerivX_of_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L154)).

**Shift quotients characterize derivatives.** Proved result. Translation quotients characterize derivatives. (`diffQuotient_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DiffQuotient.lean#L179)).

### Breakdown.CertTorus.DilateSymbol

This file tracks similarity dilation through Fourier representatives, velocity and pressure symbols, inverse transforms and Sobolev energy. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Space has real dimension three.** Proved result. The real vector space of spatial vectors has dimension three. (`finrank_space`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L14)).

**Weighted energy as an L2 norm square.** Proved result. Order-k weighted Fourier energy equals the square of the L2 norm after multiplying the field by frequency radius to power k. (`homNormSq_eq_eLpNorm_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L16)).

**Weighted energy respects a.e. equality.** Proved result. Almost-everywhere equality preserves weighted energy. (`homNormSq_congr_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L28)).

**Weighted energy under frequency dilation.** Proved result. Replacing f(ξ) by c f(cξ) with c>0 multiplies its order-k weighted Fourier energy by c to power −(2k+1). (`homNormSq_comp_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L34)).

**Dilating Fourier representatives.** Proved result. For positive μ, the Fourier representative of the dilated field is almost everywhere the original representative at frequency ξ/√μ multiplied by 1/√μ. (`symX_dilX_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L60)).

**Leray projection respects vector scalars.** Proved result. Leray projection commutes with real scalar multiplication of its vector argument. (`lerayC_smul_vec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L69)).

**Scale invariance of Leray projection.** Proved result. Multiplying frequency by a positive factor leaves Leray projection unchanged. (`lerayC_smul_freq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L76)).

**Dilation rescales the velocity symbol.** Proved result. For positive μ, the dilated velocity symbol is almost everywhere μ⁻¹ times the original symbol at frequency ξ/√μ. (`velSymbol_dilX_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L87)).

**Inverse Fourier scaling has a cube.** Proved result. Scaling frequencies by a positive factor scales inverse Fourier values by its reciprocal cube and evaluates them at the reciprocally scaled spatial point. (`fourierInv_comp_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L105)).

**Real scalars in inverse Fourier maps.** Proved result. Inverse Fourier transform respects real scalars. (`fourierInv_real_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L116)).

**Advection symbols have their scaling law.** Proved result. If a velocity symbol equals c² times another at frequency cξ almost everywhere with c>0, its advection symbol equals the other's advection symbol at cξ at every frequency. (`advectionSymbol_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L125)).

**Pressure symbols scale by one power.** Proved result. If a velocity symbol equals c² times another at frequency cξ almost everywhere with c>0, its pressure symbol equals c times the other's pressure symbol at cξ at every frequency. (`pressureSymbol_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L150)).

**Scaling homogeneous Sobolev energy.** Proved result. Dilation by positive μ multiplies the order-k homogeneous Sobolev energy by μ to power k+1/2. (`homSob_dilX`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L166)).

**Fourier subtraction almost everywhere.** Proved result. Fourier representatives preserve subtraction almost everywhere. (`symX_sub_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L179)).

**Dilation is continuous in Sobolev energy.** Proved result. At every positive dilation factor, a field with finite order-k homogeneous Sobolev energy varies continuously in that energy under dilation. (`tendsto_homSob_dilX`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L183)).

**Similarity scaling of physical velocity.** Proved result. For positive μ, dilation multiplies physical velocity by √μ and evaluates the original velocity at the spatial point √μ y. (`physField_dilX`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L239)).

**Similarity scaling of physical pressure.** Proved result. For positive μ, dilation multiplies physical pressure by μ and evaluates the original pressure at the spatial point √μ y. (`physScalar_dilX`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L250)).

**Dilation of Fourier and physical data.** Proved result. Dilation obeys the Fourier, velocity, pressure, homogeneous Sobolev scaling, and continuity requirements of the symbol interface. (`dilateSymbol_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DilateSymbol.lean#L268)).

### Breakdown.CertTorus.DuhamelChangeOfVariables

This file changes space and time variables in the heat and Leray-kernel integrals to recover the Duhamel similarity representation. The smooth-profile and torus route supporting Proposition 7.11 and Corollary 7.2; analytic and Fourier library infrastructure.

**Space has real dimension three.** Proved result. The real vector space used for the spatial change of variables has dimension three. (`finrank_space_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DuhamelChangeOfVariables.lean#L9)).

**Cancellation of heat scaling in 3D.** Proved result. In three dimensions and for positive μ, the heat normalization μ√μ cancels the reciprocal-cube Jacobian of spatial scaling by √μ. (`heat_scalar_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DuhamelChangeOfVariables.lean#L11)).

**Kernel scaling factor is a square root.** Proved result. In three dimensions and for positive μ, the kernel factor μ² times the reciprocal-cube Jacobian of scaling by √μ equals √μ. (`kernel_scalar_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DuhamelChangeOfVariables.lean#L20)).

**Heat convolution obeys parabolic scaling.** Proved result. For positive μ and time τ, heat convolution at time μτ and point √μ y equals time-τ convolution with the input evaluated at √μ times its spatial argument. (`heatConv_dilate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DuhamelChangeOfVariables.lean#L29)).

**Parabolic scaling of kernel convolution.** Proved result. For positive μ and time τ, multiplying kernel convolution at time μτ and point √μ y by √μ equals time-τ convolution of the tensor evaluated at √μ times its spatial argument. (`kernelConv_dilate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DuhamelChangeOfVariables.lean#L50)).

**Duhamel variables from kernel scaling.** Proved result. For a continuous uniformly bounded field and T>0, the kernel assumptions transform the Duhamel integral from time s−log(1+T) to s into the similarity heat term plus the truncated profile integral with square-root spatial dilation. (`duhamelChangeOfVariables_of_kernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertTorus/DuhamelChangeOfVariables.lean#L81)).

### Breakdown.CertTorus.DuhamelContinuous

This file proves spatial continuity of the Duhamel representation used to upgrade a weak profile in Proposition 7.11.

**Continuity under an integral.** An integrable bound and pointwise continuity make the translated convolution continuous. (`Breakdown.FarField.Internal.DuhamelContinuity.continuous_conv_of_dominated`)

**Fourth-power decay is integrable.** A measurable kernel bounded by B divided by (‖x‖ + √τ)⁴ is integrable when τ is positive. (`Breakdown.FarField.Internal.DuhamelContinuity.integrable_of_le_inv_pow_four`)

**Product of two coordinate bounds.** If both vector norms are at most C, the absolute product of any two coordinates is at most C². (`Breakdown.FarField.Internal.DuhamelContinuity.abs_coord_mul_le`)

**Coordinate continuity.** Every coordinate projection on space is continuous. (`Breakdown.FarField.Internal.DuhamelContinuity.continuous_coord`)

**Heat-kernel continuity.** The heat kernel is continuous in its spatial argument for every time parameter. (`Breakdown.FarField.Internal.DuhamelContinuity.continuous_heatKernel_of`)

**Heat-kernel integrability.** The heat kernel is integrable at every positive time. (`Breakdown.FarField.Internal.DuhamelContinuity.integrable_heatKernel_of`)

**Duhamel continuity from kernel bounds.** The heat-kernel bound, uniform convolution bound, Leray-kernel bound, kernel measurability and joint kernel continuity statements make the similarity heat term plus truncated bilinear profile term spatially continuous for every continuous uniformly bounded field and positive truncation time. (`Breakdown.FarField.duhamelContinuous_of_kernel`)

### Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol

This file turns the bilinear Fourier-symbol formula into an almost-everywhere Duhamel identity for the weak-to-smooth profile route.

**Left endpoint of a mesh interval.** For positive mesh size, the floor construction lies between the left endpoint and s, less than one mesh step from s. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.floor_step_mem`)

**Joint representative of an L² curve.** A continuous L² curve on a closed interval has a jointly strongly measurable representative for every time slice. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.exists_joint_version`)

**Local L¹ bound from L².** On any set K, the integral of an L² representative is bounded by its L² norm times the square root of the measure of K. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.lintegral_restrict_enorm_le`)

**Product-space integrability.** An integrable L²-valued curve with a measurable representative is integrable over time and a finite-volume spatial set. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.integrable_prod_restrict`)

**Integrating L² representatives.** Integrating a jointly measurable representative in time gives an almost-everywhere representative of the L²-valued integral. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.coeFn_setIntegral_ae`)

**Measurable Leray projection.** The complex Leray projection is measurable jointly in frequency and vector value. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.measurable_divFreeC_pair`)

**Measurable nonlinear symbol.** A jointly strongly measurable Fourier field has a jointly strongly measurable nonlinear symbol. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.stronglyMeasurable_nonlinSymbol_param`)

**Symbols ignore null-set changes.** Almost-everywhere equal Fourier fields have identical nonlinear symbols. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.nonlinSymbol_congr`)

**Double complex conjugation.** Conjugating a complex vector twice returns the original vector. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.conjVec_conjVec`)

**Conjugation of real scaling.** Vector conjugation commutes with multiplication by a real scalar. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.conjVec_ofReal_smul`)

**Projection and conjugate reflection.** Leray projection at the opposite frequency commutes with complex conjugation. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.lerayC_neg_conjVec`)

**Projection of a vector sum.** Leray projection preserves addition of complex vectors. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.lerayC_add`)

**Projection of complex scaling.** Leray projection preserves multiplication by a complex scalar. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.lerayC_smul`)

**Projected nonlinear symbol.** The nonlinear symbol is fixed by Leray projection at its frequency. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.lerayC_nonlinSymbol`)

**Hermitian velocity symbol.** The velocity symbol at the opposite frequency is the conjugate of its value at the original frequency. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.velSymbol_neg`)

**Hermitian advection symbol.** A Hermitian Fourier field has a Hermitian advection symbol. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.advectionSymbol_neg_of_herm`)

**Hermitian nonlinear symbol.** A Hermitian Fourier field has a Hermitian nonlinear symbol. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.nonlinSymbol_neg_of_herm`)

**Conjugation through an integral.** Vector conjugation commutes with the time integral. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.integral_conjVec`)

**Integrating projected vectors.** An integral of vectors fixed by one Leray projection is also fixed by that projection. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.lerayC_integral`)

**Recover the velocity-symbol identity.** Away from zero frequency, the two symmetric-symbol identities give the corresponding velocity-symbol identity when the nonlinear field is Hermitian and projected and the weight is even. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.velSymbol_of_pointwise`)

**Measurable velocity reconstruction.** Symmetrizing and projecting a jointly measurable Fourier representative gives a jointly measurable velocity representative. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.velOfJoint_measurable`)

**Joint velocity-symbol representative.** A continuous X-valued curve has a jointly strongly measurable representative of its velocity symbol on the closed time interval. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.exists_joint_velSymbol`)

**Joint nonlinear-symbol representative.** A continuous X-valued curve has a jointly strongly measurable nonlinear symbol, equal to the original symbol at every frequency in each time slice. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.exists_joint_nonlinSymbol`)

**Measurable Duhamel integrand.** The Fourier Duhamel integrand of a continuous X-valued curve is almost everywhere strongly measurable on the stated time-frequency product. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.aestronglyMeasurable_duhamel_integrand`)

**Representative of an integral sum.** An X-valued identity z = x plus an interval integral yields the corresponding almost-everywhere identity for L² representatives. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.coe_add_integral_ae`)

**Mild equation for symmetric symbols.** The bilinear-symbol interface turns a smooth mild X-valued solution into the almost-everywhere symmetric-symbol Duhamel equation. (`_private.Breakdown.CertTorus.DuhamelSymbolOfBilinSymbol.0.Breakdown.FarField.symX_mild_ae`)

**Duhamel symbols from bilinear symbols.** The bilinear Fourier-symbol and Sobolev-to-Wiener statements express the velocity symbol of a mild solution with every-order homogeneous Sobolev regularity almost everywhere as the heat-evolved initial symbol plus its heat-weighted nonlinear time integral. (`Breakdown.FarField.duhamelSymbolOfBilinSymbol_holds`)

### Breakdown.CertTorus.DuhamelVelocityAE

This file identifies the similarity-time mild equation with its physical heat and Duhamel integrals, an almost-everywhere step toward Proposition 7.11.

**Dilation respects null-set equality.** A positive dilation preserves almost-everywhere equality of vector fields. (`Breakdown.FarField.Internal.DuhamelVelocity.dilateField_congr_ae`)

**Heat ignores null-set changes.** Almost-everywhere equal vector fields have identical heat convolutions. (`Breakdown.FarField.Internal.DuhamelVelocity.heatConv_congr_ae`)

**Kernel ignores null-set changes.** Almost-everywhere equal vector fields give identical kernel convolutions of their tensor squares. (`Breakdown.FarField.Internal.DuhamelVelocity.kernelConv_congr_ae`)

**Similarity heat evolution.** Similarity heat evolution is ordinary heat evolution followed by the stated dilation. (`Breakdown.FarField.Internal.DuhamelVelocity.similarity_flow_eq`)

**Similarity bilinear evolution.** The similarity bilinear map is the ordinary bilinear map followed by the stated dilation. (`Breakdown.FarField.Internal.DuhamelVelocity.similarity_bilin_eq`)

**Measurable physical Duhamel term.** Joint continuity of the velocity and measurability of the Leray kernel make the dilated Duhamel integrand measurable. (`Breakdown.FarField.Internal.DuhamelVelocity.duhamelIntegrand_measurable`)

**Positive kernel time.** If a is less than b, then 1 − exp(−(b − a)) is positive. (`Breakdown.FarField.Internal.DuhamelVelocity.one_sub_exp_pos`)

**Heat evolution in physical space.** The heat-velocity interface identifies the similarity heat term with the dilated physical heat convolution almost everywhere. (`Breakdown.FarField.Internal.DuhamelVelocity.heat_part_ae`)

**Bilinear evolution in physical space.** The bilinear-kernel interface identifies the similarity bilinear term with the dilated negative kernel convolution almost everywhere. (`Breakdown.FarField.Internal.DuhamelVelocity.duhamel_part_ae`)

**Physical Duhamel identity.** The heat-velocity, bilinear-kernel, L⁶ integration, kernel-measurability and uniform convolution statements identify every smooth velocity representative of a rotation-periodic orbit almost everywhere with its physical Duhamel expression between strictly ordered times. (`Breakdown.FarField.duhamelVelocityAE_holds`)

### Breakdown.CertTorus.FirstDerivBootstrap

This file improves weighted decay of the first spatial derivative once the profile has an integral representation, supporting Proposition 7.11.

**A weighted bound is nonnegative.** The constant in a weighted norm bound is nonnegative. (`Breakdown.FarField.FirstDerivBootstrapInternal.weightedBound_nonneg`)

**Weaken a decay exponent.** A weighted bound at exponent γ also holds at any smaller exponent with the same constant. (`Breakdown.FarField.FirstDerivBootstrapInternal.weightedBound_mono`)

**Derivative of a coordinate.** Composing a differentiable vector field with a coordinate projection gives the corresponding projected derivative. (`Breakdown.FarField.FirstDerivBootstrapInternal.hasFDerivAt_coord`)

**Derivative of a tensor square.** The derivative of a vector field tensored with itself is the sum of its two product-rule terms. (`Breakdown.FarField.FirstDerivBootstrapInternal.fderiv_tensorField_apply`)

**Bound the tensor derivative.** The tensor derivative in direction v is bounded by twice the field norm times the derivative norm times ‖v‖. (`Breakdown.FarField.FirstDerivBootstrapInternal.norm_fderiv_tensorField_le`)

**Decay of a tensor derivative.** Weighted bounds for a field and its derivative give a tensor-derivative bound with the sum of their exponents. (`Breakdown.FarField.FirstDerivBootstrapInternal.directionalTensor_weight`)

**Improve derivative decay.** The stated operator representation and a tensor bound at a nonnegative exponent other than 2 or 3 give derivative decay at min(γ, 2). (`Breakdown.FarField.FirstDerivBootstrapInternal.deriv_weight_step`)

**First-derivative bootstrap.** The weighted operator-bound and Leray-kernel-bound statements give inverse-square gradient decay for a smooth field with uniformly bounded derivatives through order two, inverse-first-power decay and the stated profile-operator representation of its first derivative. (`Breakdown.FarField.firstDerivBootstrap_of_op`)

### Breakdown.CertTorus.HarmonicGradientBound

This file bounds gradients of harmonic functions by local energy, supplying the pressure regularity argument behind Proposition 7.11.

**First two entries of a triple.** Removing the last entry of the three-vector list leaves its first two entries. (`Breakdown.FarField.Internal.init_three`)

**Last two entries of a triple.** Removing the first entry of the three-vector list leaves its last two entries. (`Breakdown.FarField.Internal.tail_three`)

**Third derivative from two derivatives.** Applying the second iterated derivative of the derivative map to a third vector equals the third iterated derivative of the scalar function. (`Breakdown.FarField.Internal.iteratedFDeriv_two_fderiv_apply`)

**Swap the first derivative directions.** For a smooth scalar function, the first two arguments of its third derivative may be exchanged. (`Breakdown.FarField.Internal.iteratedFDeriv_three_swap_head`)

**Swap the last derivative directions.** For a smooth scalar function, the last two arguments of its third derivative may be exchanged. (`Breakdown.FarField.Internal.iteratedFDeriv_three_swap_tail`)

**Derivatives of harmonic functions.** A coordinate derivative of a smooth harmonic function is harmonic on the same open set. (`Breakdown.FarField.Internal.scalarLaplacian_partial_eq_zero`)

**Continuous functions on a ball.** A continuous scalar function is integrable on every finite-radius ball. (`Breakdown.FarField.Internal.integrableOn_ball_of_continuous`)

**Square integrability on a ball.** A continuous scalar function belongs to L² on every finite-radius ball. (`Breakdown.FarField.Internal.memLp_two_restrict_ball`)

**Mean value gives a pointwise bound.** The harmonic mean-value interface and the stated mollifier bound control the central value by the L² norm on the half-radius ball. (`Breakdown.FarField.Internal.abs_le_of_meanValue`)

**Operator norm from basis values.** A real linear functional on space has norm at most the sum of its absolute values on the coordinate basis. (`Breakdown.FarField.Internal.opNorm_le_sum_abs`)

**Gradient bound from mean value.** The harmonic mean-value statement bounds the central gradient of every smooth function harmonic on a positive-radius ball by a common constant times radius to the power −3/2 times its gradient L² norm on that ball. (`Breakdown.FarField.harmonicGradientBound_of_meanValue`)

### Breakdown.CertTorus.HarmonicMeanValue

This file proves the mollified mean-value property used to control harmonic pressure terms in Proposition 7.11.

**Move the Laplacian to a potential.** For a smooth compactly supported scalar function and positive mollifier scale, convolution with the mollifier equals the integral of its Laplacian against the mollifier potential. (`_private.Breakdown.CertTorus.HarmonicMeanValue.0.Breakdown.FarField.integral_mollifier_mul_eq_laplacian`)

**Harmonic mean-value formula.** A smooth real function harmonic on a positive-radius ball equals its mollified value at the centre for every positive mollifier scale smaller than that radius. (`Breakdown.FarField.harmonicMeanValue_holds`)

### Breakdown.CertTorus.HeatConvTest

This file develops heat convolution on compactly supported test fields and identifies its Fourier action for the profile regularity route.

**Gaussian convolution.** Gaussian convolution integrates the heat kernel against a vector-valued function using scalar multiplication. (`Breakdown.FarField.Internal.HeatConvolution.gaussConv`)

**Heat convolution as Gaussian integral.** The physical heat convolution is the Gaussian convolution defined in this file. (`Breakdown.FarField.Internal.HeatConvolution.heatConv_eq`)

**Heat-kernel continuity.** The heat kernel is continuous in space at every time parameter. (`Breakdown.FarField.Internal.HeatConvolution.continuous_heatKernel`)

**Positive heat kernel.** The heat kernel is strictly positive at positive times. (`Breakdown.FarField.Internal.HeatConvolution.heatKernel_pos`)

**Gaussian integral as convolution.** The Gaussian integral is the library convolution formed with scalar multiplication. (`Breakdown.FarField.Internal.HeatConvolution.gaussConv_eq_convolution`)

**Smoothness of Gaussian convolution.** Gaussian convolution preserves the stated differentiability order of a compactly supported function. (`Breakdown.FarField.Internal.HeatConvolution.contDiff_gaussConv`)

**Differentiate Gaussian convolution.** For a continuously differentiable compactly supported function, its Gaussian convolution has derivative equal to the convolution of its derivative. (`Breakdown.FarField.Internal.HeatConvolution.hasFDerivAt_gaussConv`)

**Integrable convolution integrand.** A continuous compactly supported function gives an integrable heat-convolution integrand at every spatial point. (`Breakdown.FarField.Internal.HeatConvolution.integrable_smul`)

**Decay of Gaussian convolution.** The heat-kernel bounds give quadratic spatial decay for a positive-time convolution of continuous compactly supported data. (`Breakdown.FarField.Internal.HeatConvolution.gaussConv_bound`)

**Trace as a continuous linear map.** The trace map sums the diagonal coordinate evaluations of a spatial linear map. (`Breakdown.FarField.Internal.HeatConvolution.traceCLM`)

**Evaluate the trace map.** The trace map evaluates to the sum of the three diagonal entries. (`Breakdown.FarField.Internal.HeatConvolution.traceCLM_apply`)

**Derivative of a convolved test field.** The derivative of a Gaussian-convolved test field equals the Gaussian convolution of its derivative. (`Breakdown.FarField.Internal.HeatConvolution.fderiv_gaussConv`)

**Heat evolution gives a decaying field.** A test field evolved for positive time is a decay field under the heat-kernel bounds. (`Breakdown.FarField.Internal.HeatConvolution.isDecayField_heatConv`)

**Continuity of a test-field partial.** Every coordinate derivative of a test field is continuous. (`Breakdown.FarField.Internal.HeatConvolution.continuous_partialField`)

**Support of a test-field partial.** Every coordinate derivative of a test field has compact support. (`Breakdown.FarField.Internal.HeatConvolution.hasCompactSupport_partialField`)

**Heat convolution and partials.** Coordinate differentiation commutes with heat convolution on test fields. (`Breakdown.FarField.Internal.HeatConvolution.partialField_heatConv`)

**Complex heat kernel.** The complex heat kernel is the real heat kernel cast into the complex numbers. (`Breakdown.FarField.Internal.HeatConvolution.heatKernelC`)

**Complex Gaussian formula.** The complex heat kernel equals its scalar prefactor times the complex Gaussian exponential. (`Breakdown.FarField.Internal.HeatConvolution.heatKernelC_eq`)

**Positive Gaussian coefficient.** For positive time, the real part of the reciprocal Gaussian coefficient is positive. (`Breakdown.FarField.Internal.HeatConvolution.re_pos`)

**Integrability of the complex kernel.** The complex heat kernel is integrable at positive times. (`Breakdown.FarField.Internal.HeatConvolution.integrable_heatKernelC`)

**Integrability of the real kernel.** The real heat kernel is integrable at positive times. (`Breakdown.FarField.Internal.HeatConvolution.integrable_heatKernel`)

**Fourier transform of the heat kernel.** At positive time, the Fourier transform of the complex heat kernel is the heat multiplier. (`Breakdown.FarField.Internal.HeatConvolution.fourier_heatKernelC`)

**Complexification of convolution.** Complexifying a Gaussian convolution of continuous compactly supported data gives convolution with the complex heat kernel. (`Breakdown.FarField.Internal.HeatConvolution.complexify_gaussConv`)

**Fourier transform of convolution.** At positive time, Gaussian convolution multiplies the Fourier transform of continuous compactly supported data by the heat factor. (`Breakdown.FarField.Internal.HeatConvolution.fourier_gaussConv`)

**Complexification of L² data.** Complexifying the L² representative agrees with forming the L² representative of the pointwise complexification. (`Breakdown.FarField.Internal.HeatConvolution.complexify_toLp`)

**Heat convolution in the L² transform.** Under the kernel bounds, positive-time heat convolution corresponds to the L² heat multiplier. (`Breakdown.FarField.Internal.HeatConvolution.fourierR_heatConv`)

**Heat convolution of a gradient.** Under the kernel bounds, the gradient representation of an evolved test field is the heat multiplier applied to its original gradient representation. (`Breakdown.FarField.Internal.HeatConvolution.ofGrad_heatConv`)

**Heat convolution realizes heat flow.** The heat-kernel bounds and heat-kernel partial-derivative statements ensure that positive-time heat convolution of a test field is a decay field and that embedding this convolution equals applying the energy-space heat operator to the embedded test field. (`Breakdown.FarField.heatConvTest_of_heat`)

### Breakdown.CertTorus.HeatKernelBounds

This file supplies explicit Gaussian bounds for the heat-kernel estimates used in the weak-profile smoothing argument.

**Tenth-power Gaussian bound.** For positive scale s, the stated tenth-degree polynomial times its Gaussian is bounded by 40⁵s¹⁰. (`Breakdown.FarField.HeatKernelEstimate.Internal.poly_mul_gaussian_le`)

**Lower-degree Gaussian bounds.** For nonnegative a and degree at most 10, the polynomial-Gaussian expression is bounded by 40⁵sᵐ at positive scale s. (`Breakdown.FarField.HeatKernelEstimate.Internal.pow_mul_gaussian_le`)

**Heat kernel at square-root scale.** At positive time, the heat kernel factors into its normalization, the inverse cube of √τ, and a Gaussian at scale √τ. (`Breakdown.FarField.HeatKernelEstimate.Internal.heatKernel_eq`)

**Coordinate bounded by vector norm.** The absolute value of each spatial coordinate is bounded by the vector norm. (`Breakdown.FarField.HeatKernelEstimate.Internal.coord_abs_le`)

**Optional coordinate bound.** Choosing either a coordinate or zero gives absolute value at most the vector norm. (`Breakdown.FarField.HeatKernelEstimate.Internal.ite_abs_le`)

**Heat-kernel bounds.** One common constant bounds the heat kernel and its displayed first- and third-partial expressions at positive time by (distance + √time) to the powers −3, −4 and −6 respectively. (`Breakdown.FarField.heatKernelBounds_holds`)

### Breakdown.CertTorus.HeatKernelPartials

This file proves the explicit heat-kernel derivative formulas needed by convolution estimates in Proposition 7.11.

**Derivative of the squared norm.** The derivative of the squared spatial norm is the linear functional with coefficients twice the coordinates. (`Breakdown.FarField.Internal.HeatPartials.hasFDerivAt_normSq`)

**Gaussian heat-kernel formula.** The heat kernel is its normalization multiplied by exp(−‖z‖²/(4τ)). (`Breakdown.FarField.Internal.HeatPartials.heatKernel_eq`)

**Derivative of the heat kernel.** At positive time, the heat-kernel derivative has coordinate coefficients −xₖ times the kernel divided by 2τ. (`Breakdown.FarField.Internal.HeatPartials.hasFDerivAt_heat`)

**Coordinate of a basis vector.** A coordinate projection of a unit vector is one when their indices agree and zero otherwise. (`Breakdown.FarField.Internal.HeatPartials.proj_unitVector`)

**Heat derivative on a basis vector.** Evaluating the heat-gradient linear map on a unit vector gives the corresponding scalar derivative formula. (`Breakdown.FarField.Internal.HeatPartials.heatGradient_unitVector`)

**Third Gaussian derivative formula.** Differentiating the stated quadratic Gaussian factor yields its product-rule expression at positive time. (`Breakdown.FarField.Internal.HeatPartials.fderiv_weighted_unitVector`)

**Heat-kernel partial formulas.** At positive time, the heat kernel has the stated Gaussian first derivative, and differentiating its displayed second-partial formula gives the specified third partial. (`Breakdown.FarField.heatKernelPartials_holds`)

### Breakdown.CertTorus.HeatPartVanishes

This file shows that the remote-past heat term vanishes, allowing the full profile integral equation used in Proposition 7.11.

**Heat kernel in Gaussian notation.** The heat kernel equals its normalization times exp(−(4τ)⁻¹‖x‖²). (`_private.Breakdown.CertTorus.HeatPartVanishes.0.Breakdown.FarField.heatKernel_eq_gaussian`)

**Nonnegative heat kernel.** The heat kernel is nonnegative at positive times. (`_private.Breakdown.CertTorus.HeatPartVanishes.0.Breakdown.FarField.heatKernel_nonneg_of_pos`)

**Gaussian mass in three dimensions.** At positive time, the unnormalized Gaussian has integral (4πτ)³ᐟ² over space. (`_private.Breakdown.CertTorus.HeatPartVanishes.0.Breakdown.FarField.integral_gaussian_space`)

**Unit mass of the heat kernel.** The heat kernel has integral one at positive times. (`_private.Breakdown.CertTorus.HeatPartVanishes.0.Breakdown.FarField.integral_heatKernel_eq_one`)

**Integrability of the heat kernel.** The heat kernel is integrable at positive times. (`_private.Breakdown.CertTorus.HeatPartVanishes.0.Breakdown.FarField.integrable_heatKernel`)

**Heat convolution preserves a bound.** At positive time, convolving a field bounded in norm by C leaves its norm bounded by C. (`_private.Breakdown.CertTorus.HeatPartVanishes.0.Breakdown.FarField.norm_heatConv_le`)

**Vanishing remote-past heat term.** The heat-kernel bounds make the similarity heat term of every continuous uniformly bounded field tend pointwise to zero as its elapsed similarity time tends to infinity. (`Breakdown.FarField.heatPartVanishes_of_heat`)

### Breakdown.CertTorus.HeatVelocity

This file extends the physical heat-convolution identity from test fields to the L⁶ velocity representatives used for weak profiles.

**Continuity of the heat kernel.** The heat kernel is continuous in space for every time parameter. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.heatKernel_continuous`)

**Nonnegativity of the heat kernel.** The heat kernel is nonnegative at positive time. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.heatKernel_nonneg`)

**The six-fifths Gaussian power.** At positive time, the six-fifths power of the heat kernel is the stated rescaled Gaussian. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.heatKernel_rpow`)

**Finite six-fifths kernel norm.** The translated heat kernel has a finite six-fifths power integral at positive time. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.lintegral_heatKernel_rpow_lt_top`)

**Hölder bound for heat convolution.** The heat-convolution integrand of a measurable field is bounded in L¹ by the kernel's L⁶ᐟ⁵ norm times the field's L⁶ norm. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.lintegral_heatKernel_smul_le`)

**Integrable L⁶ heat convolution.** An L⁶ velocity has an integrable heat-convolution integrand at positive time. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.integrable_heatKernel_smul`)

**Subtract two L⁶ heat convolutions.** Subtracting two positive-time heat convolutions agrees with convolving the difference of their L⁶ classes. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.heatConv_sub_Lp`)

**Continuity bound from L⁶.** At positive time and a fixed point, the difference of heat convolutions is bounded by a constant times the L⁶ distance. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.norm_heatConv_sub_le`)

**Pass an L⁶ limit through heat.** L⁶ convergence implies pointwise convergence of positive-time heat convolutions. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.tendsto_heatConv_of_tendsto`)

**Heat identity on the test span.** The heat-convolution test interface identifies heat evolution with physical convolution almost everywhere on the test span. (`_private.Breakdown.CertTorus.HeatVelocity.0.Breakdown.FarField.heatVelocity_on_testSpan`)

**Heat identity for all velocities.** The heat-kernel bounds and test-field heat-convolution statement identify the velocity of every positive-time heat-evolved energy-space state almost everywhere with heat convolution of its original velocity. (`Breakdown.FarField.heatVelocity_of_heatConvTest`)

### Breakdown.CertTorus.HomWiener

This file obtains weighted Fourier L¹ bounds from homogeneous Sobolev energies, a regularity bridge in Proposition 7.11.

**Sobolev comparison weight.** The comparison weight is 1 plus the frequency norm raised to 2(k + 1). (`Breakdown.FarField.Internal.HomWienerBound.sobolevSum`)

**Wiener comparison ratio.** The comparison ratio divides (1 + ‖ξ‖)ᵏ by 2π‖ξ‖ times the square root of the Sobolev weight. (`Breakdown.FarField.Internal.HomWienerBound.wienerRatio`)

**Lower bound for the Sobolev weight.** The Sobolev comparison weight is at least one. (`Breakdown.FarField.Internal.HomWienerBound.one_le_sobolevSum`)

**Even Sobolev weight.** The Sobolev comparison weight is unchanged when frequency is negated. (`Breakdown.FarField.Internal.HomWienerBound.sobolevSum_neg`)

**Measurable Sobolev weight.** The Sobolev comparison weight is measurable. (`Breakdown.FarField.Internal.HomWienerBound.measurable_sobolevSum`)

**Measurable Wiener ratio.** The Wiener comparison ratio is measurable. (`Breakdown.FarField.Internal.HomWienerBound.measurable_wienerRatio`)

**Nonnegative Wiener ratio.** The Wiener comparison ratio is nonnegative. (`Breakdown.FarField.Internal.HomWienerBound.wienerRatio_nonneg`)

**Conjugation preserves vector norm.** Conjugating a complex vector preserves its norm. (`Breakdown.FarField.Internal.HomWienerBound.norm_conjVec_eq`)

**Velocity symbol from two frequencies.** The velocity-symbol norm is bounded by the sum of the symmetric-symbol norms at ξ and −ξ, divided by 2π‖ξ‖. (`Breakdown.FarField.Internal.HomWienerBound.norm_velSymbol_le`)

**Weighted velocity-symbol bound.** The weighted velocity symbol is bounded by the two Sobolev-weighted symmetric symbols multiplied by the comparison ratio. (`Breakdown.FarField.Internal.HomWienerBound.weight_mul_norm_velSymbol_le`)

**Low-frequency ratio bound.** Below unit frequency, the square of the Wiener ratio is bounded by 2²ᵏ‖ξ‖⁻². (`Breakdown.FarField.Internal.HomWienerBound.wienerRatio_sq_le_of_lt_one`)

**High-frequency ratio bound.** At and above unit frequency, the square of the Wiener ratio is bounded by 2²ᵏ‖ξ‖⁻⁴. (`Breakdown.FarField.Internal.HomWienerBound.wienerRatio_sq_le_of_one_le`)

**Square integrability of the ratio.** The square of the Wiener comparison ratio has finite integral. (`Breakdown.FarField.Internal.HomWienerBound.lintegral_wienerRatio_sq_lt_top`)

**Weighted Fourier L¹ estimate.** The weighted velocity-symbol integral is bounded by twice the ratio's L² norm times the square root of the two Sobolev energies. (`Breakdown.FarField.Internal.HomWienerBound.lintegral_weight_velSymbol_le`)

**Sobolev-to-Wiener estimate.** For each natural weight order, a constant bounds the weighted Fourier L¹ velocity norm by the square root of the sum of its zeroth and next-order homogeneous Sobolev energies. (`Breakdown.FarField.homWiener_holds`)

### Breakdown.CertTorus.InnerSplitBound

This file splits the spatial convolution near the origin to control weighted profile operators in Proposition 7.11.

**Decay weight is at most one.** At positive scale and nonnegative exponent, the radial decay weight is at most one. (`_private.Breakdown.CertTorus.InnerSplitBound.0.Breakdown.FarField.weight_le_one_of_pos`)

**Nonnegative radial weight.** At positive scale, the radial power weight is nonnegative. (`_private.Breakdown.CertTorus.InnerSplitBound.0.Breakdown.FarField.weight_nonneg_of_pos`)

**Weight outside a half-radius ball.** Outside radius R/2, the radial weight is bounded by 2ᵞ times the smaller of one and (a/R)ᵞ under the stated positivity assumptions. (`_private.Breakdown.CertTorus.InnerSplitBound.0.Breakdown.FarField.weight_le_far_of_norm`)

**Kernel bound near the origin.** If ‖z‖ is less than half of ‖y‖, the inverse fourth-power kernel is bounded by 16 divided by (‖y‖ + t)⁴ for nonnegative t. (`_private.Breakdown.CertTorus.InnerSplitBound.0.Breakdown.FarField.kernel_le_of_norm_lt`)

**Compare half-radius factors.** For positive a and R and exponent at most three, the weighted half-ball volume factor is bounded by its full-radius counterpart. (`_private.Breakdown.CertTorus.InnerSplitBound.0.Breakdown.FarField.half_radius_factor`)

**Inner convolution split.** The kernel-mass and radial-weight bounds make the weighted kernel integral finite for nonnegative decay exponent other than three, bound it by a constant times the inverse square root of positive time, and bound it at radius at least one by the sum of the far and near majorants. (`Breakdown.FarField.innerSplitBound_of_mass`)

### Breakdown.CertTorus.IntegralEquationClosed

This file discharges the kernel interfaces that are assembled into the full profile integral equation for Proposition 7.11.

**Leray-kernel decay bound.** A common constant bounds every Leray-kernel entry at positive time by (distance + √time) to the power −4. (`Breakdown.FarField.lerayKernelBound_holds`)

**Measurable Leray kernel.** The Leray kernel is jointly measurable in time and space as required by its interface. (`Breakdown.FarField.lerayKernelMeasurable_holds`)

**Continuous Leray kernel.** The Leray kernel is jointly continuous at positive time as required by its interface. (`Breakdown.FarField.lerayKernelJointContinuous_holds`)

**Differentiable Leray kernel.** The positive-time Leray kernel is continuously differentiable in space. (`Breakdown.FarField.lerayKernelC1_holds`)

**Divergence-free Leray kernel.** The Leray kernel satisfies its divergence-free identity at positive time. (`Breakdown.FarField.lerayKernelDivFree_holds`)

**Leray-kernel L¹ bound.** Every positive-time Leray-kernel entry is integrable, and one common constant bounds its L¹ norm by the inverse square root of time. (`Breakdown.FarField.kernelL1Bound_holds`)

**Uniform convolution bound.** At positive time, convolution of the Leray kernel with a uniformly bounded measurable tensor is bounded by a common constant times the tensor bound divided by the square root of time. (`Breakdown.FarField.kernelConvSup_holds`)

**Decay after convolving a test field.** For positive time and a test vector field, the negative Leray-kernel convolution of its self-tensor is a decay field. (`Breakdown.FarField.kernelConvTestDecay_holds`)

### Breakdown.CertTorus.IntervalIntegralL6

This file justifies time integration of L⁶ velocity representatives, used when passing from the mild equation to physical Duhamel integrals.

**Local L¹ control by the L⁶ norm.** The integral of the norm of an L⁶ representative over K is at most its L⁶ norm times the measure of K to the power 5/6. (`_private.Breakdown.CertTorus.IntervalIntegralL6.0.Breakdown.FarField.Internal.IntervalIntegralL6.lintegral_enorm_le`)

**L⁶ fields on finite-volume sets.** An L⁶ field is integrable on every finite-volume set. (`_private.Breakdown.CertTorus.IntervalIntegralL6.0.Breakdown.FarField.Internal.IntervalIntegralL6.integrableOn_of_mem`)

**Integrate an L⁶ field over a set.** Integration over a finite-volume set defines a continuous linear map from L⁶ fields to spatial vectors. (`Breakdown.FarField.Internal.IntervalIntegralL6.setIntegralL6`)

**Evaluate the L⁶ integration map.** The continuous linear integration map evaluates to the ordinary set integral of the L⁶ representative. (`Breakdown.FarField.Internal.IntervalIntegralL6.setIntegralL6_apply`)

**Time integration in L⁶.** On an ordered interval, integrating an interval-integrable L⁶-valued curve agrees almost everywhere with pointwise integration of any jointly measurable representatives agreeing with the curve at interior times. (`Breakdown.FarField.intervalIntegralL6_holds`)

### Breakdown.CertTorus.KernelContraction

This file reduces contraction of the Leray kernel against a solenoidal test field to derivatives of heat convolution.

**Continuous coordinate projection.** Each coordinate function on space is continuous. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.coord_continuous`)

**Differentiable coordinate projection.** Each coordinate function on space is differentiable. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.coord_differentiable`)

**Continuous heat kernel.** The spatial heat kernel is continuous for every time parameter. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.heatKernel_continuous`)

**Continuous optional coordinate.** A coordinate selected when two indices agree, and zero otherwise, is continuous. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.ite_coord_continuous`)

**Continuous third heat derivative.** The explicit third heat derivative is continuous in space. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.heatKernelThird_continuous`)

**Measurable third heat derivative.** The explicit third heat derivative is jointly measurable in time and space. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.heatKernelThird_measurable`)

**Derivative of a field component.** Differentiating a coordinate of a smooth vector field gives that coordinate of the vector-field derivative. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.fderiv_component`)

**Differentiable field component.** Every component of a smooth vector field is differentiable. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.component_differentiable`)

**Continuous field component.** Every component of a smooth vector field is continuous. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.component_continuous`)

**Support of a field component.** Each component of a compactly supported field has compact support. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.component_compact`)

**Continuous directional derivative.** Every fixed directional derivative of a component of a smooth field is continuous. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.component_deriv_continuous`)

**Support of a directional derivative.** Directional derivatives of a smooth compactly supported field have compact support. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.component_deriv_compact`)

**Product with left compact support.** Two continuous scalar functions have integrable product if the first has compact support. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.integrable_mul_compact_left`)

**Product with right compact support.** Two continuous scalar functions have integrable product if the second has compact support. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.integrable_mul_compact_right`)

**Derivative of reflection and shift.** Differentiating f(x − z) with respect to z introduces a minus sign in its directional derivative. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.fderiv_comp_sub_apply`)

**Third derivatives pair to zero.** Under the heat derivative formulas, the third-derivative kernel pairs to zero with a smooth compactly supported divergence-free field. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.third_pairing_zero`)

**Remove the spatial denominator.** A sixth-power kernel bound at positive time implies the corresponding uniform bound Cρ⁻³. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.third_bound`)

**Integrated third-derivative pairing.** The time-integrated third-derivative kernel has an integrable pairing with a solenoidal test field and that pairing vanishes under the heat hypotheses. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.third_integral_part`)

**Heat gradient from kernel pairing.** At positive time, the heat-gradient kernel paired with a smooth compactly supported field gives the corresponding derivative of its heat convolution. (`_private.Breakdown.CertTorus.KernelContraction.0.Breakdown.FarField.gradient_part`)

**Kernel contraction from heat formulas.** The heat-kernel bounds and partial-derivative formulas identify pairing a positive-time Leray-kernel column with a test field as the corresponding spatial derivative of the field’s heat convolution. (`Breakdown.FarField.kernelContraction_of_heat`)

### Breakdown.CertTorus.KernelConvDeriv

This file differentiates the Leray convolution against bounded differentiable tensor data for the profile derivative bootstrap.

**Tensor-entry projection.** The tensor-entry map is the continuous linear projection onto one specified matrix entry. (`_private.Breakdown.CertTorus.KernelConvDeriv.0.Breakdown.FarField.entryMap`)

**Evaluate an entry projection.** Applying the tensor-entry projection returns the chosen entry. (`_private.Breakdown.CertTorus.KernelConvDeriv.0.Breakdown.FarField.entryMap_apply`)

**Norm of an entry projection.** The tensor-entry projection has operator norm at most one. (`_private.Breakdown.CertTorus.KernelConvDeriv.0.Breakdown.FarField.norm_entryMap_le`)

**Differentiate a kernel component.** Under the kernel hypotheses, a tensor field and its derivative bounded by A permit differentiation under the positive-time kernel integral, with an integrable derivative integrand. (`_private.Breakdown.CertTorus.KernelConvDeriv.0.Breakdown.FarField.hasFDerivAt_kernelComponent`)

**Derivative of kernel convolution.** The Leray-kernel measurability, kernel-mass bound and Leray-kernel-bound statements allow each spatial derivative to pass through positive-time convolution of a continuously differentiable tensor whose value and derivative are uniformly bounded. (`Breakdown.FarField.kernelConvDeriv_of_mass`)

### Breakdown.CertTorus.KernelConvL3Pointwise

This file obtains pointwise Leray-convolution estimates from L³ tensor data through a scaled Hölder bound.

**Scale a radial power.** At positive scale s, the rescaled radial weight equals (‖x‖ + s) raised to the same negative exponent. (`Breakdown.FarField.KernelConvL3Internal.add_norm_rpow_eq`)

**Integrable sixth-power weight.** The inverse sixth power of ‖x‖ + s is integrable for positive s. (`Breakdown.FarField.KernelConvL3Internal.integrable_add_norm_rpow_neg_six`)

**Integral of a scaled sixth power.** At positive scale s, the inverse sixth-power integral is s⁻³ times its unit-scale value. (`Breakdown.FarField.KernelConvL3Internal.integral_add_norm_rpow_neg_six`)

**Hölder bound for an L³ tensor.** At positive time, the fourth-power kernel weight times an L³ tensor norm is integrable and obeys the stated τ⁻¹ bound. (`Breakdown.FarField.KernelConvL3Internal.holder_weight_bound`)

**Pointwise bound from L³ data.** The Leray-kernel bound and measurability give integrable convolution components for every L³ tensor and bound the convolution pointwise by a common constant times its L³ norm divided by positive time. (`Breakdown.FarField.kernelConvL3Pointwise_of_bound`)

### Breakdown.CertTorus.KernelConvSup

This file derives the uniform kernel-convolution estimate needed by the Duhamel continuity argument.

**Uniform bound from kernel L¹.** The kernel L¹ bound and Leray-kernel measurability bound positive-time convolution of every uniformly bounded measurable tensor by a common constant times its uniform bound divided by the square root of time. (`Breakdown.FarField.kernelConvSup_of_l1`)

### Breakdown.CertTorus.KernelConvTestDecay

This file proves smoothness, decay and solenoidality of kernel convolution on test fields for the physical integral representation.

**Reversed scalar multiplication.** The reversed bilinear multiplication map sends a and b to b times a. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.mulRev`)

**Evaluate reversed multiplication.** Reversed multiplication applied to a and b equals b times a. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.mulRev_apply`)

**Precompose reversed multiplication.** Precomposition of reversed multiplication with a linear functional gives scalar multiplication of that functional. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.precompL_mulRev`)

**Convolution in reversed notation.** Convolution formed with reversed multiplication equals the integral of k(y − t)g(t). (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.conv_mulRev_eq`)

**Integrability with compact data.** A continuous kernel multiplied by translated continuous compactly supported data has an integrable convolution integrand. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.integrable_kernel_smul`)

**Differentiate the data in convolution.** For continuously differentiable compactly supported data and a continuous kernel, the convolution derivative is the integral against the data derivative. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.hasFDerivAt_conv_mulRev`)

**Evaluate the derivative integral.** Under the stated continuity and support assumptions, evaluating the derivative integral in direction v commutes with integration. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.conv_deriv_apply`)

**Move a derivative to the kernel.** For continuously differentiable kernel and compactly supported data, integration by parts moves the directional derivative from the data to the translated kernel. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.integral_kernel_mul_deriv`)

**Bound convolution on the support.** An integrable field supported in S has convolution norm at most the kernel bound on S times the integral of its norm. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.norm_integral_kernel_le`)

**Compare translated radial weights.** When t lies in the radius-R ball and s is positive, the stated product controls 1 + ‖y‖ by ‖y − t‖ + s. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.one_add_norm_le`)

**Kernel decay with compact support.** For a positive-time fourth-power kernel and ‖t‖ ≤ R, the translated kernel has the stated fourth-power decay in y. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.kernel_bound_on_ball`)

**Sum twenty-seven scalar terms.** If every term in the three-index array has absolute value at most M, its assembled vector sum has norm at most 27M. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.norm_sum_smul_unit_le`)

**Sum twenty-seven linear maps.** If every map in the three-index array has norm at most M, the assembled vector-valued linear map has norm at most 27M. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.norm_sum_smulRight_unit_le`)

**Product of two field components.** The test product multiplies the jth and kth components of a field. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.testProd`)

**Read an assembled component.** The ith coordinate of the assembled sum of basis-valued linear maps equals the ith scalar map evaluated on the direction. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.apply_sum_smulRight_unit`)

**Weaken fourth-power decay.** For nonnegative M and r, fourth-power decay implies the stated degree-n bound whenever n is at most four. (`_private.Breakdown.CertTorus.KernelConvTestDecay.0.Breakdown.FarField.div_four_le`)

**Test-field kernel decay.** The Leray-kernel bound, measurability, continuous differentiability and divergence-free statements make the negative positive-time convolution of every test field’s self-tensor a decay field. (`Breakdown.FarField.kernelConvTestDecay_of_kernel`)

### Breakdown.CertTorus.KernelL1Bound

This file integrates the pointwise fourth-power Leray bound to obtain the time-singular L¹ estimate.

**Integrability of the radial weight.** The function (1 + ‖x‖)⁻⁴ is integrable over three-dimensional space. (`Breakdown.FarField.Internal.KernelL1.integrable_bracket`)

**Rescale the fourth-power weight.** For positive s, the rescaled unit weight equals s⁴ divided by (‖x‖ + s)⁴. (`Breakdown.FarField.Internal.KernelL1.bracket_smul_eq`)

**Factor a fourth-power bound.** For positive s, C divided by (‖x‖ + s)⁴ factors into the stated dilation of the unit weight. (`Breakdown.FarField.Internal.KernelL1.bound_eq`)

**Integrability of a scaled bound.** The function C divided by (‖x‖ + s)⁴ is integrable for positive s. (`Breakdown.FarField.Internal.KernelL1.integrable_bound`)

**Integral scales as inverse radius.** At positive scale s, the fourth-power bound has integral C times the unit-weight integral times s⁻¹. (`Breakdown.FarField.Internal.KernelL1.integral_bound`)

**L¹ bound from pointwise decay.** The Leray-kernel bound and measurability make every positive-time kernel entry integrable with its L¹ norm bounded by a common constant times the inverse square root of time. (`Breakdown.FarField.kernelL1Bound_of_bound`)

### Breakdown.CertTorus.KernelMassBound

This file evaluates the radial mass integral behind the Leray-kernel mass estimate.

**Antiderivative of the radial kernel.** At positive a and nonnegative r, the stated rational function has derivative r² divided by (r + a)⁴. (`_private.Breakdown.CertTorus.KernelMassBound.0.Breakdown.FarField.Internal.quarticRadial_antideriv_hasDerivAt`)

**Antiderivative vanishes at infinity.** The rational radial antiderivative tends to zero at infinity. (`_private.Breakdown.CertTorus.KernelMassBound.0.Breakdown.FarField.Internal.quarticRadial_antideriv_tendsto`)

**Evaluate the radial mass.** For positive a, the radial mass integrand is integrable on the positive half-line and its integral is 1/(3a). (`_private.Breakdown.CertTorus.KernelMassBound.0.Breakdown.FarField.Internal.quarticRadial_integral`)

**Kernel-mass estimate.** At positive time, (distance from any centre + √time) to the power −4 is integrable, with integral at most five divided by the square root of time. (`Breakdown.FarField.kernelMassBound_holds`)

### Breakdown.CertTorus.KernelScaling

This file checks parabolic scaling of the heat and Leray kernels used by the similarity-time representation.

**Parabolic heat-kernel scaling.** At positive scale and time, scaling space by s and time by s² multiplies the heat kernel by s⁻³. (`Breakdown.FarField.KernelScalingInternal.heatKernel_dilate`)

**Scale the third heat derivative.** At positive scale and time, the third heat derivative acquires the factor s⁻⁶ under parabolic scaling. (`Breakdown.FarField.KernelScalingInternal.heatKernelThird_dilate`)

**Scale an integrated heat derivative.** At positive scale and time, the tail time integral of the third heat derivative acquires the factor s⁻⁴. (`Breakdown.FarField.KernelScalingInternal.integral_heatKernelThird_dilate`)

**Heat and Leray scaling laws.** For positive scale and time, scaling time by μ and space by √μ multiplies the heat kernel by μ to the power −3/2 and each Leray-kernel entry by μ to the power −2. (`Breakdown.FarField.kernelScaling_holds`)

### Breakdown.CertTorus.KernelStatements

This file states the heat and Leray kernel interfaces later discharged by the analytic kernel modules; these propositions are proof obligations for the profile integral route.

**Bounds for heat-kernel derivatives.** This interface asks for one uniform constant controlling the heat kernel and its first and third derivatives by the stated third-, fourth- and sixth-power weights. (`Breakdown.FarField.HeatKernelBounds`)

**Heat-kernel derivative formulas.** This interface asks for the explicit first-derivative and third-partial formulas at positive times. (`Breakdown.FarField.HeatKernelPartials`)

**Fourth-power Leray-kernel bound.** This interface requires one constant bounding every Leray-kernel component by (‖x‖ + √τ)⁻⁴ at positive time. (`Breakdown.FarField.LerayKernelBound`)

**Joint continuity at positive time.** This interface requires joint time-space continuity of each Leray-kernel component on the positive-time domain. (`Breakdown.FarField.LerayKernelJointContinuous`)

**Joint kernel measurability.** This interface requires joint time-space measurability of every Leray-kernel component. (`Breakdown.FarField.LerayKernelMeasurable`)

**Spatial kernel differentiability.** This interface requires continuous first spatial derivatives of each Leray-kernel component at positive time. (`Breakdown.FarField.LerayKernelC1`)

**Divergence-free kernel columns.** This interface requires the sum of the three corresponding spatial derivatives of a Leray-kernel column to vanish. (`Breakdown.FarField.LerayKernelDivFree`)

**Odd Leray kernel.** This interface requires spatial reflection to negate every Leray-kernel component. (`Breakdown.FarField.LerayKernelOdd`)

**Parabolic kernel scaling.** This interface requires the stated heat and Leray scaling laws under positive rescaling of time and its square root in space. (`Breakdown.FarField.KernelScaling`)

**Time-weighted kernel L¹ bound.** This interface requires componentwise kernel integrability and an L¹ bound proportional to τ⁻¹ᐟ² at positive time. (`Breakdown.FarField.KernelL1Bound`)

**Uniform kernel-convolution bound.** This interface requires a τ⁻¹ᐟ² uniform bound for convolution of a measurable tensor field bounded in norm by A. (`Breakdown.FarField.KernelConvSup`)

### Breakdown.CertTorus.KernelStatementsIdentify

This file states how heat and bilinear evolution in the energy space agree with physical kernel convolutions, the identification stage of Proposition 7.11.

**Physical heat convolution.** The heat convolution integrates the heat kernel at y − z against the vector field at z. (`Breakdown.FarField.heatConv`)

**Heat evolution of test fields.** This interface requires positive-time heat convolution of a test field to be a decay field and to agree with heat evolution after embedding in X. (`Breakdown.FarField.HeatConvTest`)

**Physical heat-velocity identity.** This interface requires the velocity of heat evolution to agree almost everywhere with heat convolution of the velocity. (`Breakdown.FarField.HeatVelocity`)

**Kernel pairing with a test field.** This interface identifies the Leray-kernel pairing against a test field with the corresponding derivative of its heat convolution. (`Breakdown.FarField.KernelContraction`)

**Decay of the test-field kernel term.** This interface requires the negative kernel convolution of a test field's tensor square to be a decay field. (`Breakdown.FarField.KernelConvTestDecay`)

**Bilinear evolution of test fields.** This interface identifies positive-time bilinear evolution of an embedded test field with its embedded negative kernel convolution. (`Breakdown.FarField.BilinTestKernel`)

**Pointwise L³ convolution estimate.** This interface requires integrability of each kernel component against L³ tensor data and a pointwise norm bound proportional to τ⁻¹. (`Breakdown.FarField.KernelConvL3Pointwise`)

**Physical bilinear-velocity identity.** This interface identifies the velocity of the bilinear term with the negative kernel convolution of the velocity tensor square almost everywhere. (`Breakdown.FarField.BilinKernel`)

### Breakdown.CertTorus.KernelStatementsIntegral

This file states the physical Duhamel representation and its limiting steps, then assembles the orbit integral equation used in Proposition 7.11.

**Similarity heat term.** The similarity heat term is the heat convolution of the shifted field multiplied by the inverse square root of 1 + T. (`Breakdown.FarField.similarityHeatPart`)

**Truncated profile bilinear term.** The truncated profile term integrates the negative kernel convolution of the two shifted fields over (0, T], weighted by (1 + τ)⁻¹. (`Breakdown.FarField.profileBilinTrunc`)

**Physical Duhamel expression.** The Duhamel expression adds the dilated heat evolution from s′ to the time integral of the dilated bilinear kernel term. (`Breakdown.FarField.duhamelVelocityForm`)

**Integrating velocity representatives.** This interface requires an interval integral in L⁶ to agree almost everywhere with the pointwise time integral of any stated jointly measurable representative. (`Breakdown.FarField.IntervalIntegralL6`)

**Orbit Duhamel identity.** This interface requires a smooth orbit field representing an energy-space orbit to satisfy the physical Duhamel identity almost everywhere between any two ordered times. (`Breakdown.FarField.DuhamelVelocityAE`)

**Duhamel change of variables.** This interface rewrites the Duhamel expression of a continuous uniformly bounded field as its similarity heat term plus truncated profile term. (`Breakdown.FarField.DuhamelChangeOfVariables`)

**Continuity of the Duhamel expression.** This interface requires the transformed Duhamel expression of a continuous uniformly bounded field to be continuous in space at positive truncation time. (`Breakdown.FarField.DuhamelContinuous`)

**Vanishing similarity heat term.** This interface requires the similarity heat term of a continuous uniformly bounded field to tend pointwise to zero as T tends to infinity. (`Breakdown.FarField.HeatPartVanishes`)

**Limit of truncated profile integrals.** This interface requires truncated profile integrals of a continuous uniformly bounded field to tend to the full bilinear profile integral. (`Breakdown.FarField.TruncTendsto`)

**Assemble the orbit integral equation.** The almost-everywhere Duhamel identity, change of variables, continuity and two limiting interfaces imply the orbit integral equation. (`Breakdown.FarField.integralEquationOfOrbit_of_duhamel`)

**Build the integral equation route.** The supplied kernel facts and all stated intermediate implication maps assemble the orbit integral equation. (`Breakdown.FarField.integralEquationOfOrbit_of_kernel`)

### Breakdown.CertTorus.LerayKernelBound

This file integrates the third heat-derivative bound to obtain the fourth-power Leray-kernel estimate.

**Antiderivative with square-root time.** For nonnegative a and positive time, the stated reciprocal fourth-power expression has the displayed square-root-time derivative. (`_private.Breakdown.CertTorus.LerayKernelBound.0.Breakdown.FarField.Internal.hasDerivAt_neg_inv_pow_add_sqrt`)

**Integrate the heat-derivative bound.** For nonnegative a and C and positive τ, the tail integral of the stated kernel bound equals C divided by twice (a + √τ)⁴. (`_private.Breakdown.CertTorus.LerayKernelBound.0.Breakdown.FarField.Internal.integral_Ioi_inv_pow_add_sqrt`)

**Leray bound from heat bounds.** The heat-kernel bounds give one common constant controlling every positive-time Leray-kernel entry by (distance + √time) to the power −4. (`Breakdown.FarField.lerayKernelBound_of_heatKernelBounds`)

### Breakdown.CertTorus.LerayKernelC1

This file proves continuous spatial differentiability of the Leray kernel by differentiating its heat-kernel representation.

**Linear third-derivative factor.** The linear factor sums the three index-selected coordinates and divides by 4ρ². (`Breakdown.FarField.Internal.LerayKernelSmooth.linPart`)

**Derivative of the linear factor.** The linear-factor derivative is the corresponding sum of coordinate projections divided by 4ρ². (`Breakdown.FarField.Internal.LerayKernelSmooth.linPartDeriv`)

**Cubic third-derivative factor.** The cubic factor is the product of the three selected coordinates divided by 8ρ³. (`Breakdown.FarField.Internal.LerayKernelSmooth.cubicPart`)

**Derivative of the cubic factor.** The cubic-factor derivative sums the three coordinate product-rule terms divided by 8ρ³. (`Breakdown.FarField.Internal.LerayKernelSmooth.cubicPartDeriv`)

**Heat-gradient linear map.** The heat-gradient map has coordinate coefficients −xₗ times the kernel divided by 2ρ. (`Breakdown.FarField.Internal.LerayKernelSmooth.heatGrad`)

**Derivative of the third heat term.** The proposed derivative of the third heat term is the difference of the two stated product-rule expressions. (`Breakdown.FarField.Internal.LerayKernelSmooth.thirdDeriv`)

**Split the third heat derivative.** The third heat derivative is the linear Gaussian term minus the cubic Gaussian term. (`Breakdown.FarField.Internal.LerayKernelSmooth.heatKernelThird_eq`)

**Smooth heat kernel.** The spatial heat kernel has every stated differentiability order. (`Breakdown.FarField.Internal.LerayKernelSmooth.contDiff_heatKernel`)

**Derivative of a selected coordinate.** The derivative of a conditionally selected coordinate is the selected coordinate projection, or zero. (`Breakdown.FarField.Internal.LerayKernelSmooth.hasFDerivAt_ite_coord`)

**Check the linear-factor derivative.** The linear factor has the continuous linear derivative defined for it. (`Breakdown.FarField.Internal.LerayKernelSmooth.hasFDerivAt_linPart`)

**Check the cubic-factor derivative.** The cubic factor has the continuous linear derivative defined for it. (`Breakdown.FarField.Internal.LerayKernelSmooth.hasFDerivAt_cubicPart`)

**Differentiate the third heat term.** Under the heat-partial interface, the third heat derivative has the stated spatial derivative at positive time. (`Breakdown.FarField.Internal.LerayKernelSmooth.hasFDerivAt_heatKernelThird`)

**Coordinate norm bound.** Each absolute coordinate is at most the spatial norm. (`Breakdown.FarField.Internal.LerayKernelSmooth.abs_coord_le`)

**Selected coordinate norm bound.** A coordinate selected by index equality, or zero otherwise, has absolute value at most the spatial norm. (`Breakdown.FarField.Internal.LerayKernelSmooth.abs_ite_coord_le`)

**Evaluate a selected projection.** Applying a conditionally selected coordinate projection gives the selected coordinate or zero. (`Breakdown.FarField.Internal.LerayKernelSmooth.ite_proj_apply`)

**Bound the linear Gaussian factor.** At positive time, the linear factor has absolute value at most 3‖y‖ divided by 4ρ². (`Breakdown.FarField.Internal.LerayKernelSmooth.abs_linForm_le`)

**Bound a triple coordinate product.** A product of two coordinates of x and one of y has absolute value at most ‖x‖²‖y‖. (`Breakdown.FarField.Internal.LerayKernelSmooth.abs_triple_le`)

**Bound the fourth heat derivative.** At positive time, the derivative of the third heat term has operator norm at most 13(4πρ)⁻³ᐟ² divided by ρ². (`Breakdown.FarField.Internal.LerayKernelSmooth.norm_thirdDeriv_le`)

**Integrable inverse powers in time.** At positive lower time, reciprocal integer powers of degree at least two are integrable on the time tail. (`Breakdown.FarField.Internal.LerayKernelSmooth.integrableOn_inv_pow`)

**Continuous third-derivative map.** The derivative map for the third heat term is continuous in space. (`Breakdown.FarField.Internal.LerayKernelSmooth.continuous_thirdDeriv`)

**Measurable heat kernel in time.** At every fixed spatial point, the heat kernel is measurable in time. (`Breakdown.FarField.Internal.LerayKernelSmooth.measurable_heatKernel_time`)

**Measurable third derivative in time.** At every fixed spatial point, the third heat derivative is measurable in time. (`Breakdown.FarField.Internal.LerayKernelSmooth.measurable_heatKernelThird_time`)

**Measurable derivative-map curve.** The spatial derivative map for the third heat term is almost everywhere strongly measurable in time for any time measure. (`Breakdown.FarField.Internal.LerayKernelSmooth.aestronglyMeasurable_thirdDeriv`)

**Differentiate the time-tail integral.** The heat bounds and partial formulas make the positive-time tail integral of the third heat derivative continuously differentiable in space. (`Breakdown.FarField.Internal.LerayKernelSmooth.contDiff_integral_third`)

**Leray differentiability from heat.** The heat-kernel bounds and partial-derivative formulas make every Leray-kernel entry continuously differentiable in space at positive time. (`Breakdown.FarField.lerayKernelC1_of_heat`)

### Breakdown.CertTorus.LerayKernelContinuity

This file proves the joint measurability and positive-time continuity needed for physical Leray-kernel integrals.

**Continuous selected spatial coordinate.** A conditionally selected spatial coordinate is continuous as a function of time and space. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.coordIf_continuous`)

**Jointly measurable heat kernel.** The heat kernel is measurable jointly in time and space. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.heatKernel_measurable_prod`)

**Jointly measurable third heat term.** The third heat derivative is measurable jointly in time and space. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.heatKernelThird_measurable_prod`)

**Heat continuity away from zero time.** The heat kernel is jointly continuous at every nonzero time and spatial point. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.heatKernel_continuousAt_prod`)

**Third-term continuity away from zero.** The third heat derivative is jointly continuous at every nonzero time and spatial point. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.heatKernelThird_continuousAt_prod`)

**Measurable Leray kernel.** Every Leray-kernel entry is jointly measurable in time and space. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.lerayKernel_measurable_all`)

**Uniform cubic time decay.** The heat-kernel bounds imply that the third heat derivative has absolute value at most Cρ⁻³ at positive time. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.heatKernelThird_le_cube`)

**Leray continuity from heat bounds.** The heat-kernel bounds imply joint positive-time continuity of the Leray kernel. (`_private.Breakdown.CertTorus.LerayKernelContinuity.0.Breakdown.FarField.Internal.lerayKernel_jointContinuous_of_bounds`)

**Joint Leray regularity.** The heat-kernel bounds imply both joint positive-time continuity and joint measurability of the Leray kernel. (`Breakdown.FarField.lerayKernel_continuous_measurable`)

### Breakdown.CertTorus.LerayKernelDivFree

This file proves zero divergence of the Leray kernel by matching a time derivative of the second heat partial with a summed spatial derivative.

**Kronecker delta.** The Kronecker delta is one when the two indices agree and zero otherwise. (`Breakdown.FarField.Internal.LerayDivFree.kd`)

**Second heat partial.** The second heat partial multiplies the Gaussian by its stated quadratic factor and diagonal correction. (`Breakdown.FarField.Internal.LerayDivFree.secondPartial`)

**Time derivative of a second partial.** The proposed time derivative combines the derivative of the quadratic factor with the time derivative of the Gaussian. (`Breakdown.FarField.Internal.LerayDivFree.secondPartialTime`)

**Time derivative of the heat kernel.** At positive time, the heat-kernel derivative is the kernel multiplied by −3/(2ρ) + ‖x‖²/(4ρ²). (`Breakdown.FarField.Internal.LerayDivFree.heatKernel_hasDerivAt_time`)

**Time derivative of the second partial.** At positive time, the second heat partial has the stated time derivative. (`Breakdown.FarField.Internal.LerayDivFree.secondPartial_hasDerivAt`)

**Nonnegative heat kernel.** The heat kernel is nonnegative at positive time. (`Breakdown.FarField.Internal.LerayDivFree.heatKernel_nonneg`)

**Second partial vanishes at infinity.** Each second heat partial tends to zero as time tends to infinity at a fixed spatial point. (`Breakdown.FarField.Internal.LerayDivFree.secondPartial_tendsto`)

**Uniform Gaussian bound in time.** For ρ at least the positive lower time τ, the heat kernel is at most (4πτ)⁻³ᐟ². (`Breakdown.FarField.Internal.LerayDivFree.heatKernel_le`)

**Heat derivative along a line.** The line-gradient expression pairs the explicit heat-gradient coefficients with the direction vector. (`Breakdown.FarField.Internal.LerayDivFree.gammaLine`)

**Third-term derivative along a line.** The line derivative of the third heat term is encoded by its four product-rule contributions. (`Breakdown.FarField.Internal.LerayDivFree.thirdLine`)

**Derivative of a coordinate on a line.** The derivative of the mth coordinate of x + se is the mth coordinate of e. (`Breakdown.FarField.Internal.LerayDivFree.coord_line`)

**Differentiate a conditional scalar.** A fixed conditional choice between a differentiable scalar function and zero has the correspondingly selected derivative. (`Breakdown.FarField.Internal.LerayDivFree.ite_line`)

**Heat derivative on a spatial line.** The heat-partial interface gives the line-gradient expression as the derivative of the heat kernel along x + se at positive time. (`Breakdown.FarField.Internal.LerayDivFree.heatKernel_line`)

**Third heat derivative on a line.** The heat-partial interface gives the stated line derivative of the third heat term at positive time. (`Breakdown.FarField.Internal.LerayDivFree.third_line`)

**Uniform heat-kernel factor.** The uniform heat factor is (4πτ)⁻³ᐟ². (`Breakdown.FarField.Internal.LerayDivFree.heatSup`)

**Uniform line-gradient factor.** The line-gradient factor is three times R/(2τ) times the uniform heat factor. (`Breakdown.FarField.Internal.LerayDivFree.lineSup`)

**Bound a conditional scalar.** A choice between a scalar bounded in absolute value by nonnegative B and zero is also bounded by B. (`Breakdown.FarField.Internal.LerayDivFree.ite_abs_le`)

**Multiply absolute bounds.** Bounds |a| ≤ A and |b| ≤ B imply |ab| ≤ AB. (`Breakdown.FarField.Internal.LerayDivFree.abs_mul_le'`)

**Add absolute bounds.** Bounds |a| ≤ A and |b| ≤ B imply |a + b| ≤ A + B. (`Breakdown.FarField.Internal.LerayDivFree.abs_add_le'`)

**Subtract absolute bounds.** Bounds |a| ≤ A and |b| ≤ B imply |a − b| ≤ A + B. (`Breakdown.FarField.Internal.LerayDivFree.abs_sub_le'`)

**Divide an absolute bound.** Dividing an absolute bound by a positive scalar preserves the inequality. (`Breakdown.FarField.Internal.LerayDivFree.abs_div_le'`)

**Weaken cubic time decay.** For ρ at least positive τ and nonnegative A, A/(8ρ³) is at most A/(8τ) divided by ρ². (`Breakdown.FarField.Internal.LerayDivFree.cube_le`)

**Bound the line heat derivative.** With spatial coordinates bounded by R and directional coordinates by one, the line heat derivative is bounded by the uniform line-gradient factor for ρ ≥ τ > 0. (`Breakdown.FarField.Internal.LerayDivFree.gammaLine_bound`)

**Bound the line third derivative.** Under the coordinate and positive-time bounds, the line derivative of the third heat term obeys the displayed reciprocal-square time estimate. (`Breakdown.FarField.Internal.LerayDivFree.thirdLine_bound`)

**Bound the third heat term.** Under the coordinate and positive-time bounds, the third heat term obeys the displayed reciprocal-square time estimate. (`Breakdown.FarField.Internal.LerayDivFree.third_bound`)

**Sum the line derivatives.** Summing the line derivatives of the third heat term along the coordinate basis yields the time derivative of the second heat partial. (`Breakdown.FarField.Internal.LerayDivFree.sum_thirdLine`)

**Derivative of the first kernel term.** The first-term line derivative differentiates the selected Gaussian gradient factor by the product rule. (`Breakdown.FarField.Internal.LerayDivFree.aLine`)

**Check the first-term line derivative.** Under the heat-partial interface, the selected first kernel term has the stated derivative along a spatial line at positive time. (`Breakdown.FarField.Internal.LerayDivFree.first_line`)

**Sum the first-term derivatives.** Summing the first-term derivatives along the coordinate basis yields the second heat partial. (`Breakdown.FarField.Internal.LerayDivFree.sum_aLine`)

**Measurable third heat term.** The third heat term is measurable in time at a fixed spatial point. (`Breakdown.FarField.Internal.LerayDivFree.third_meas`)

**Measurable line third derivative.** The line derivative of the third heat term is measurable in time at fixed point and direction. (`Breakdown.FarField.Internal.LerayDivFree.thirdLine_meas`)

**Coordinate bound by the norm.** Each absolute coordinate is bounded by the spatial norm. (`Breakdown.FarField.Internal.LerayDivFree.coord_le`)

**Differentiate the full Leray kernel.** Under the heat-partial and Leray C¹ interfaces, a direction of norm at most one gives an integrable time-tail derivative and the stated formula for the Leray derivative. (`Breakdown.FarField.Internal.LerayDivFree.line_deriv`)

**Zero divergence from heat identities.** The heat-kernel bounds, partial-derivative formulas and continuous spatial differentiability of the Leray kernel make the divergence of every positive-time Leray-kernel column vanish. (`Breakdown.FarField.lerayKernelDivFree_of_c1`)

### Breakdown.CertTorus.LerayKernelOdd

This file verifies the spatial reflection parity of the kernels used in the physical bilinear identity.

**Even heat kernel.** Reflecting the spatial argument leaves the heat kernel unchanged. (`Breakdown.FarField.Internal.LerayOdd.heatKernel_neg`)

**Odd third heat derivative.** Reflecting the spatial argument negates the third heat derivative. (`Breakdown.FarField.Internal.LerayOdd.heatKernelThird_neg`)

**Odd Leray kernel.** At every time, reversing the spatial argument negates each Leray-kernel entry. (`Breakdown.FarField.lerayKernelOdd_holds`)

### Breakdown.CertTorus.MildRestrict

This file supplies restriction of a mild solution to a shorter time interval for the regularity bootstrap in Proposition 7.11.

**Restrict a mild solution.** A mild solution on [a, b] remains mild on [a′, b] whenever a ≤ a′ ≤ b. (`Breakdown.FarField.mildRestrict_holds`)

### Breakdown.CertTorus.MildSmoothing

This file derives bounded derivatives away from the initial time of a bounded mild solution, a core weak-to-smooth step of Proposition 7.11.

**The derivative of order zero.** The zero-order derivative relation identifies every energy-space element with itself. (`Breakdown.FarField.MildSmoothing.Internal.isDerivX_fin_zero`)

**Symmetric symbols of a difference.** The symmetric symbol of x − y agrees almost everywhere with the difference of their symmetric symbols. (`Breakdown.FarField.MildSmoothing.Internal.symX_sub`)

**Subtract derivative relations.** Two energy-space derivative relations of the same order subtract to give the derivative relation of the differences. (`Breakdown.FarField.MildSmoothing.Internal.isDerivX_sub`)

**Measurable symbol norm.** The extended norm of the symmetric symbol is almost everywhere measurable. (`Breakdown.FarField.MildSmoothing.Internal.aemeasurable_enorm_symX`)

**Zero-order Sobolev energy.** The zero-order homogeneous Sobolev energy is the squared energy-space norm cast to the extended nonnegative reals. (`Breakdown.FarField.MildSmoothing.Internal.homSob_zero_eq`)

**Interpolate Sobolev energies.** The order-k Sobolev energy is at most the geometric mean of the zero-order and order-2k energies. (`Breakdown.FarField.MildSmoothing.Internal.homSob_le_interp`)

**Bound all derivatives after a delay.** The local-gain and restriction interfaces give uniformly bounded energy-space derivatives of every finite order on each later closed time interval of a bounded mild solution. (`Breakdown.FarField.MildSmoothing.Internal.deriv_bounds`)

### Breakdown.CertTorus.NeumannDecay

This file uses Neumann iteration to transfer weighted decay through the profile operator in Proposition 7.11.

**Zero weight is a uniform bound.** A weighted bound with exponent zero is equivalent to a uniform pointwise norm bound. (`_private.Breakdown.CertTorus.NeumannDecay.0.Breakdown.FarField.weightedBound_zero_iff`)

**Decay implies a uniform bound.** A weighted bound with nonnegative exponent implies the same uniform pointwise bound. (`_private.Breakdown.CertTorus.NeumannDecay.0.Breakdown.FarField.weightedBound_zero_of`)

**Measurable tensor product.** The tensor product of two jointly measurable time-dependent fields is jointly measurable. (`_private.Breakdown.CertTorus.NeumannDecay.0.Breakdown.FarField.measurable_pairTensor`)

**Bounded measurable tensor product.** The tensor-weight interface turns two measurable uniformly bounded fields into a bounded measurable tensor. (`_private.Breakdown.CertTorus.NeumannDecay.0.Breakdown.FarField.boundedMeasurable_pairTensor`)

**Tensor product of a left sum.** The tensor product distributes over addition in its first field. (`_private.Breakdown.CertTorus.NeumannDecay.0.Breakdown.FarField.pairTensor_add_left`)

**Tensor product of a right sum.** The tensor product distributes over addition in its second field. (`_private.Breakdown.CertTorus.NeumannDecay.0.Breakdown.FarField.pairTensor_add_right`)

**Neumann iteration.** The iteration starts from zero and repeatedly adds g to the profile operator applied to V tensored with the previous iterate. (`_private.Breakdown.CertTorus.NeumannDecay.0.Breakdown.FarField.neumannIterate`)

**Weighted decay by Neumann iteration.** The weighted operator bound, linearity, measurability, tensor-weight and Leray-kernel-bound statements give spatial decay exponent 3/4 for every bounded measurable field with vanishing tails that satisfies its nonlinear profile equation. (`Breakdown.FarField.neumannDecay_of_op`)

### Breakdown.CertTorus.NewtonFar

This file combines the far-field Newton representation with its quantitative estimate in the pressure-decay route.

**Far Newton bound from its formula.** The far Newton identity and estimate give an integrable far gradient kernel against a tensor’s double divergence with inverse-cube spatial decay whenever that tensor is twice continuously differentiable and its derivatives through order two have the prescribed decay. (`Breakdown.FarField.newtonFar_of_identity`)

### Breakdown.CertTorus.NewtonFarEstimate

This file controls the Hessian of the truncated far Newton kernel to obtain pressure-gradient decay for Proposition 7.11.

**Far Newton cutoff profile.** The far profile multiplies a reflected Newton-kernel gradient component by a smooth cutoff that removes the inner region. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farProfile`)

**Translate the far cutoff profile.** The far weight is the far profile at scale max(1, ‖y‖), translated by y. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farWeight_eq_farProfile`)

**Scale the Newton-kernel gradient.** At positive scale c, the Newton-kernel gradient scales by c⁻². (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.kernelGrad_smul`)

**Scale the far cutoff profile.** At positive scale M, the far profile is M⁻² times its unit-scale profile evaluated at M⁻¹x. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farProfile_scale`)

**Far profile vanishes near zero.** For positive M and 3‖x‖ < M, the far cutoff profile is zero. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farProfile_eq_zero`)

**Far profile equals the kernel.** For positive M and M < 2‖x‖, the far profile equals the reflected Newton-kernel gradient component. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farProfile_eq_kernel`)

**Local vanishing of the far profile.** Inside 3‖x‖ < M with positive M, the far profile is identically zero in a neighbourhood of x. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.eventually_farProfile_eq_zero`)

**Twice differentiable far profile.** At positive cutoff scale, the far profile is twice continuously differentiable. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farProfile_contDiff`)

**Zero Hessian in the inner region.** The far profile's second derivative vanishes where 3‖x‖ < M for positive M. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.iteratedFDeriv_farProfile_eq_zero`)

**Scale the far-profile Hessian.** At positive M, the far-profile Hessian norm is bounded by M⁻⁴ times the unit-scale Hessian norm at M⁻¹x. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.norm_iteratedFDeriv_farProfile_le`)

**Unit-scale far Hessian bounds.** Each unit-scale far-profile Hessian has both a uniform bound and inverse-fourth-power spatial decay with one nonnegative constant. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farProfile_bound`)

**Uniform far Hessian bounds.** A single nonnegative constant bounds every far-profile Hessian by both M⁻⁴ and ‖x‖⁻⁴ factors at positive scale M. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.farProfile_uniform`)

**Inverse-square mass in a ball.** On a positive-radius ball, the inverse-square norm weight has lower integral at most 20πρ/3. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.lintegral_ball_inv_sq_le`)

**Inverse-sixth mass outside a ball.** Outside a positive-radius ball, the inverse-sixth norm weight has lower integral at most 4π/(3ρ³). (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.lintegral_compl_ball_inv_six_le`)

**Hessian entry bounded by its norm.** A bilinear form evaluated on two coordinate unit vectors has absolute value at most its operator norm. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.abs_apply_unitVector_le`)

**Bound the tensor-Hessian contraction.** When the two Hessians agree as stated, their nine-entry contraction with the tensor is bounded by nine times the Hessian norm times the tensor norm. (`_private.Breakdown.CertTorus.NewtonFarEstimate.0.Breakdown.FarField.abs_sum_le`)

**Far Newton estimate.** For a continuous tensor bounded by A times the inverse square of 1 plus distance, its pairing with the second derivatives of the far Newton weight is bounded by a common constant times A times the inverse cube of 1 plus the observation distance. (`Breakdown.FarField.newtonFarEstimate_holds`)

### Breakdown.CertTorus.NewtonFarIdentity

This file moves two derivatives from the pressure source onto a smooth far Newton kernel, producing the far-field identity for Proposition 7.11.

**Newton gradient with an inner cutoff.** The cutoff kernel multiplies a Newton-gradient component by the smooth factor that removes the inner region. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.cutKernel`)

**Far weight as a translated kernel.** The far weight equals the cutoff kernel at scale max(1, ‖y‖) evaluated at y − z. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.farWeight_eq_cutKernel`)

**Finite differentiability order.** Every natural differentiability order is bounded by infinity. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.natCast_le_infty`)

**Smooth Newton gradient off the origin.** Each Newton-gradient component is smooth at every nonzero point. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.kernelGrad_coord_contDiffAt`)

**Smooth radial cutoff.** The radial cutoff factor is smooth on all of space. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.cutoff_contDiff`)

**Cutoff kernel vanishes near zero.** At positive cutoff radius, the cutoff kernel vanishes when ‖x‖ < r/4. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.cutKernel_eq_zero`)

**Smooth cutoff Newton kernel.** At positive cutoff radius, the cutoff Newton kernel is smooth on all of space. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.cutKernel_contDiff`)

**Recover the kernel outside the cutoff.** Outside the half-radius ball, a positive-radius cutoff kernel equals the original Newton-gradient component. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.cutKernel_far`)

**Newton-gradient scaling.** At positive dilation t, the Newton-gradient vector scales by t⁻². (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.kernelGrad_smul`)

**Far cutoff scaling identity.** For 1 ≤ r ≤ R and ‖x‖ > R/2, the radius-r cutoff kernel equals R⁻² times the unit cutoff at R⁻¹x. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.cutKernel_scale`)

**Decay of every cutoff derivative.** For cutoff radius at least one, each fixed-order derivative of the cutoff kernel has a nonnegative quadratic-decay bound. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.cutKernel_decay`)

**Far-weight derivative bounds.** The far weight is twice continuously differentiable and its derivatives through order two share a quadratic-decay bound. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.farWeight_bounds`)

**Pass derivative bounds to an entry.** A twice differentiable tensor with the stated derivative decay gives the same bounds for each scalar entry. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.component_bounds`)

**Multiply two decay bounds.** Multiplying two pointwise power-decay bounds adds their exponents and multiplies their constants. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.decay_mul`)

**Decay stronger than cubic integrates.** A continuous scalar function with power decay of integer degree greater than three is integrable. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.integrable_of_decay`)

**Identify a second directional derivative.** For a twice continuously differentiable scalar function, differentiating its derivative in a fixed direction equals the corresponding second iterated derivative. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.fderiv_fderiv_apply_eq`)

**Integrate by parts twice.** Under the stated twice-differentiable decay bounds, the two products are integrable and two directional derivatives can be transferred from g to w inside the integral. (`_private.Breakdown.CertTorus.NewtonFarIdentity.0.Breakdown.FarField.ibp_twice`)

**Far Newton representation.** For a twice continuously differentiable tensor with the stated derivative decay through order two, the far Newton weight times its double divergence is integrable and its integral equals the tensor pairing with the second derivatives of that weight. (`Breakdown.FarField.newtonFarIdentity_holds`)

### Breakdown.CertTorus.NewtonNear

This file estimates the locally singular Newton-gradient contribution using its integrable inverse-square kernel.

**Truncated inverse-square weight.** The truncated inverse-square weight equals t⁻² below ρ and zero elsewhere. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.inverseSquareTrunc`)

**Three-dimensional space.** The real dimension of space is three. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.finrank_space_eq_three`)

**Radial cancellation of inverse square.** On positive radii, the radial Jacobian times the truncated inverse-square weight is the indicator of radii below ρ. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.radial_inverseSquareTrunc`)

**Integrable truncated inverse square.** The truncated inverse-square weight of the spatial norm is integrable. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.integrable_inverseSquareTrunc`)

**Mass of the truncated inverse square.** For nonnegative ρ, the truncated inverse-square integral is three times the unit-ball volume times ρ. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.integral_inverseSquareTrunc`)

**Newton-gradient coordinate bound.** Each Newton-gradient component is bounded in absolute value by (4π)⁻¹‖w‖⁻². (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.abs_kernelGrad_apply_le`)

**Measurable Newton gradient.** The Newton-kernel gradient is measurable. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.measurable_kernelGrad`)

**Near cutoff vanishes outside.** The near cutoff is zero when the separation is at least half of max(1, ‖y‖). (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.nearCutoff_eq_zero_of_le`)

**Comparable norms in the near region.** In the stated near region, 1 + ‖y‖ is at most twice 1 + ‖z‖. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.one_add_norm_le_of_near`)

**Transfer decay across the near region.** A nonnegative fourth-power decay bound at z gives the corresponding bound with factor 16 at y in the near region. (`_private.Breakdown.CertTorus.NewtonNear.0.Breakdown.FarField.decay_bound_of_near`)

**Near Newton estimate.** For a continuous scalar source with inverse fourth-power decay, the near Newton gradient integral is integrable and bounded by a common constant times the source bound times the inverse cube of 1 plus the observation distance. (`Breakdown.FarField.newtonNear_holds`)

### Breakdown.CertTorus.OpLinear

This file proves linearity of the weighted profile integral operator after establishing the integrability needed to split its integrals.

**Mass of the inverse-quartic kernel.** The inner-split interface gives integrability of every positive-time translated inverse-quartic kernel and a uniform inverse-square-root-time mass bound. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.inverseQuartic_integrable`)

**Nonnegative kernel-bound constant.** A constant bounding all Leray-kernel components in the stated way is nonnegative. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.kernelConstant_nonneg`)

**Bound one kernel-tensor product.** A bounded tensor entry times a positive-time Leray component is bounded by CA times the translated inverse-quartic weight. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.kernelTerm_norm_le`)

**Integrability of one kernel term.** The stated kernel measurability, decay and radial integrability make each bounded measurable tensor-kernel product integrable. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.kernelTerm_integrable`)

**Add bounded tensor convolutions.** Under the stated integrability and kernel hypotheses, convolution distributes over addition of bounded measurable tensor fields. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.kernelConv_add_of_bounded`)

**Bound the full tensor convolution.** The stated componentwise and radial mass bounds control the full convolution by 27CA times the mass bound. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.kernelConv_norm_le_of_bounded`)

**Measurable shifted tensor.** Every fixed similarity shift of a jointly measurable tensor field is measurable. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.tensorShift_measurable`)

**Measurable shifted kernel integrand.** Jointly measurable tensor data and Leray kernel give a measurable shifted time-space kernel integrand. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.shiftedIntegrand_measurable`)

**Measurable weighted convolution.** Joint tensor and kernel measurability make the weighted convolution measurable in its positive-time integration variable. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.weightedKernelConv_measurable`)

**Scale a kernel convolution.** Kernel convolution commutes with scalar multiplication of tensor data. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.kernelConv_smul'`)

**Scale the profile operator.** The profile operator commutes with scalar multiplication of its tensor input. (`_private.Breakdown.CertTorus.OpLinear.0.Breakdown.FarField.profileOp_smul'`)

**Linearity of the profile operator.** Kernel measurability, the inner-split bound, small-time integrability and the Leray-kernel bound make the profile operator additive on bounded measurable tensors at parameter at least one and homogeneous under every real scalar. (`Breakdown.FarField.opLinear_of_kernel`)

### Breakdown.CertTorus.OpMeasurable

This file supplies joint measurability of the profile integral operator for its Neumann and decay arguments.

**Measurability of the profile operator.** Joint measurability of the Leray kernel makes the profile operator preserve joint time-space measurability of tensor inputs for every real operator parameter. (`Breakdown.FarField.opMeasurable_of_kernel`)

### Breakdown.CertTorus.OpWeightedBound

This file combines inner and outer convolution estimates to obtain the weighted operator bound used throughout Proposition 7.11.

**Decay after a similarity shift.** At positive τ, a weighted tensor bound becomes the stated weight with spatial scale √(1 + τ) after similarity shifting. (`_private.Breakdown.CertTorus.OpWeightedBound.0.Breakdown.FarField.norm_tensorShift_le`)

**Bound a kernel-convolution component.** The stated Leray and shifted-tensor bounds control each nine-term component sum by 9CA times the product of radial weights. (`_private.Breakdown.CertTorus.OpWeightedBound.0.Breakdown.FarField.norm_kernel_coeff_le`)

**Bound the vector convolution.** With integrable radial majorant, the kernel-convolution norm is at most 27CA times the weighted kernel integral. (`_private.Breakdown.CertTorus.OpWeightedBound.0.Breakdown.FarField.norm_kernelConv_le`)

**Integrate a time majorant.** An integrable positive-time majorant for the weighted convolution bounds the norm of the full profile operator by its integral. (`_private.Breakdown.CertTorus.OpWeightedBound.0.Breakdown.FarField.norm_profileOp_le`)

**Weighted operator estimate.** The inner-split, far-outer, near-outer, small-time and Leray-kernel bounds send a tensor with decay exponent γ to profile-operator decay exponent min(γ, n + 1) for n at most two, nonnegative γ different from three and n + 1, and operator parameter 1 + n/2. (`Breakdown.FarField.opWeightedBound_of_split`)

### Breakdown.CertTorus.OrbitDerivBoundOfSymbolCurve

This file obtains uniform orbit derivative control from Sobolev-to-Wiener bounds and Fourier curve regularity in Proposition 7.11.

**Uniform weighted orbit-symbol bound.** The orbit Sobolev, Wiener and rotation interfaces give a uniform weighted Fourier L¹ norm bound along a rotationally periodic orbit. (`Breakdown.FarField.Internal.OrbitDerivBound.exists_bound_weight_orbit`)

**Orbit derivatives from symbol curves.** The orbit Sobolev regularity, homogeneous Sobolev-to-Wiener, symbol rotation and physical derivative-bound statements together give every rotation-periodic orbit field a uniform spatial derivative bound through order three. (`Breakdown.FarField.orbitDerivBoundOfSymbolCurve_holds`)

### Breakdown.CertTorus.OrbitHomSobolevOfWindows

This file transfers Sobolev regularity from physical-time windows back to the similarity-time orbit.

**Square of a sum bound.** For extended nonnegative a and b, (a + b)² is at most 2(a² + b²). (`_private.Breakdown.CertTorus.OrbitHomSobolevOfWindows.0.Breakdown.FarField.sq_add_le_two_mul`)

**Symmetric symbol of a sum.** The symmetric symbol of a sum agrees almost everywhere with the sum of the symbols. (`_private.Breakdown.CertTorus.OrbitHomSobolevOfWindows.0.Breakdown.FarField.symX_add_ae`)

**Sobolev energy of a sum.** The order-k Sobolev energy of a + b is at most twice the sum of their order-k energies. (`_private.Breakdown.CertTorus.OrbitHomSobolevOfWindows.0.Breakdown.FarField.homSob_add_le`)

**Cancel inverse dilations.** Dilating by positive μ after dilating by μ⁻¹ returns the original energy-space vector. (`_private.Breakdown.CertTorus.OrbitHomSobolevOfWindows.0.Breakdown.FarField.dilX_mul_inv_apply`)

**Physical-time window curve.** The window curve rescales the orbit by (1 − t)⁻¹ and evaluates it at s₀ − log(1 − t). (`_private.Breakdown.CertTorus.OrbitHomSobolevOfWindows.0.Breakdown.FarField.windowCurve`)

**Recover an orbit from its window.** The orbit value at σ is recovered by the stated exponential dilation of the corresponding window value. (`_private.Breakdown.CertTorus.OrbitHomSobolevOfWindows.0.Breakdown.FarField.eq_dilX_windowCurve`)

**Local Sobolev continuity of an orbit.** The window, smoothing and dilation interfaces give finite Sobolev energy and Sobolev convergence to zero of orbit increments after the starting time. (`_private.Breakdown.CertTorus.OrbitHomSobolevOfWindows.0.Breakdown.FarField.homSobolev_near`)

**Sobolev orbit regularity from windows.** The orbit-window, mild-smoothing and symbol-dilation statements make every rotation-periodic orbit a homogeneous Sobolev curve of every order on the whole time axis. (`Breakdown.FarField.orbitHomSobolevOfWindows_holds`)

### Breakdown.CertTorus.OrbitSmoothOfWindows

This file recovers smooth profile velocity and pressure, the similarity equation and zero divergence from smooth physical-time windows.

**Smooth mild window on an interior band.** The orbit-window, restriction and smoothing interfaces give a mild window on [1/4, 3/4] with a Sobolev curve at every order. (`_private.Breakdown.CertTorus.OrbitSmoothOfWindows.0.Breakdown.FarField.window_mild_sobolev`)

**Smoothness of every orbit state.** The window, restriction, smoothing and dilation interfaces imply that every orbit state is smooth in the energy-space sense. (`_private.Breakdown.CertTorus.OrbitSmoothOfWindows.0.Breakdown.FarField.isSmoothX_orbit`)

**Smooth orbit solves the profile PDE.** The listed window, symbol, Wiener and residual interfaces give joint smoothness of orbit velocity and pressure together with zero similarity residual and zero divergence at each point. (`_private.Breakdown.CertTorus.OrbitSmoothOfWindows.0.Breakdown.FarField.orbit_point`)

### Breakdown.CertTorus.OrbitTailOfSymbolCurve

This file controls the spatial tail of the reconstructed orbit through integrable Fourier symbols and rotational periodicity.

**The zero-weight measure.** The weighted Fourier measure of order zero is ordinary volume. (`Breakdown.FarField.Internal.OrbitTail.weightL1Measure_zero`)

**Integrable orbit velocity symbols.** The Sobolev-to-Wiener interface makes each velocity symbol integrable when the orbit is a Sobolev curve at every order. (`Breakdown.FarField.Internal.OrbitTail.integrable_orbit_velSymbol`)

**Integrability after Fourier modulation.** Multiplying an integrable Fourier field by a Fourier character preserves integrability. (`Breakdown.FarField.Internal.OrbitTail.integrable_char_smul`)

**Physical difference from Fourier L¹.** The pointwise difference of two integrable Fourier reconstructions is bounded by the real-part map norm times their Fourier L¹ difference. (`Breakdown.FarField.Internal.OrbitTail.norm_physField_sub_le`)

**Fourier reconstruction vanishes far out.** For every positive tolerance, the physical reconstruction is bounded by that tolerance beyond some radius. (`Breakdown.FarField.Internal.OrbitTail.exists_radius_physField`)

**Rotational periodicity of the field.** Under the rotation-symbol interface, advancing an orbit field by its period rotates both its spatial argument and its value as stated. (`Breakdown.FarField.Internal.OrbitTail.orbitField_add_period`)

### Breakdown.CertTorus.OrbitWindows

This file supplies the physical-time windows through which a similarity orbit gains parabolic regularity.

**Orbit windows.** Every rotation-periodic orbit, after the stated logarithmic time change and dilation, gives a mild solution on [0, T] for each 0 < T < 1 and each initial orbit time. (`Breakdown.FarField.orbitWindows_holds`)

### Breakdown.CertTorus.OuterFarBound

This file bounds the far portion of the time-integrated weighted kernel after splitting at a radius-dependent time.

**Weaken a truncated power.** For positive x and 0 ≤ c ≤ γ, min(1, xᵞ) is at most xᶜ. (`Breakdown.FarField.OuterFar.Internal.min_one_rpow_le`)

**Inverse square root as a power.** At positive τ, the reciprocal square root equals τ⁻¹ᐟ². (`Breakdown.FarField.OuterFar.Internal.inv_sqrt_eq`)

**Nonnegative far-time integrand.** At positive time and radius, the weighted far majorant is nonnegative. (`Breakdown.FarField.OuterFar.Internal.integrand_nonneg`)

**Weighted far-majorant bound.** For 0 ≤ c ≤ γ and positive time and radius, the far integrand is bounded by R⁻ᶜ times the stated time weight. (`Breakdown.FarField.OuterFar.Internal.pointwise_weight`)

**Far-majorant tail bound.** For nonnegative b and positive time and radius, the far integrand is bounded by τ⁻¹ᐟ²⁻ᵇ. (`Breakdown.FarField.OuterFar.Internal.pointwise_tail`)

**Split a positive-time integral.** A measurable nonnegative integrand dominated by integrable bounds before and after positive T is integrable and bounded by the sum of those two integrals. (`Breakdown.FarField.OuterFar.Internal.split_integral`)

**Integrate a power from zero.** For exponent greater than −1 and nonnegative T, the power integrand is integrable on (0, T] with integral Tᵃ⁺¹/(a + 1). (`Breakdown.FarField.OuterFar.Internal.integral_Ioc_rpow`)

**Measurable far-time majorant.** The weighted far majorant is almost everywhere strongly measurable on positive time. (`Breakdown.FarField.OuterFar.Internal.integrand_measurable`)

**Outer far estimate.** For derivative order n at most two and nonnegative decay exponent γ different from n + 1, the weighted far majorant is integrable over positive times and its integral at radius R at least one is bounded by a constant times R to the power −min(γ, n + 1). (`Breakdown.FarField.outerFarBound_holds`)

### Breakdown.CertTorus.OuterNearBound

This file integrates the near spatial contribution to the weighted profile-operator estimate.

**Weaken a truncated power.** For positive x and 0 ≤ m ≤ g, min(1, xᵍ) is bounded by xᵐ. (`Breakdown.FarField.Internal.min_one_rpow_le_rpow`)

**Nonnegative near kernel.** At positive radius R, R³ divided by (R + √τ)⁴ is nonnegative. (`Breakdown.FarField.Internal.nearKernel_nonneg`)

**Near kernel bounded by inverse radius.** At positive radius R, the near kernel factor is at most R⁻¹. (`Breakdown.FarField.Internal.nearKernel_le_inv`)

**Near kernel bounded at large time.** At positive radius and time, the near kernel factor is at most R³/τ². (`Breakdown.FarField.Internal.nearKernel_le_sq`)

**Nonnegative near majorant.** The near majorant is nonnegative at positive radius. (`Breakdown.FarField.Internal.nearMajorant_nonneg`)

**Weighted near-integrand bound.** For derivative order at most two, nonnegative γ, R ≥ 1 and positive τ, the near integrand has the stated radial factor R⁻ᵐⁱⁿ⁽ᵞ˒ⁿ⁺¹⁾ and time-kernel bound. (`Breakdown.FarField.Internal.nearIntegrand_le`)

**Integrate inverse square-root time.** For positive R, the integral of τ⁻¹ᐟ² over (0, R²] is 2R. (`Breakdown.FarField.Internal.integral_Ioc_rpow_neg_half`)

**Integrate the large-time tail.** For positive R, the integral of τ⁻⁵ᐟ² beyond R² is 2/(3R³). (`Breakdown.FarField.Internal.integral_Ioi_rpow_neg_five_half`)

**Small-time square-root integrability.** The inverse square root of time is integrable on every interval (0, b] with b nonnegative. (`Breakdown.FarField.Internal.integrableOn_Ioc_rpow_neg_half`)

**Measurable near-time majorant.** The weighted near-majorant integrand is measurable in time. (`Breakdown.FarField.Internal.measurable_nearIntegrand`)

**Outer near estimate.** For derivative order n at most two and nonnegative decay exponent γ, the weighted near majorant is integrable over positive times and its integral at radius R at least one is bounded by a constant times R to the power −min(γ, n + 1). (`Breakdown.FarField.outerNearBound_holds`)

### Breakdown.CertTorus.PhysFieldDerivBound

This file converts weighted Fourier L¹ norms into pointwise derivative bounds for reconstructed profile velocities.

**Volume below the weighted measure.** Volume is absolutely continuous with respect to every nonnegative-order weighted Fourier measure. (`Breakdown.FarField.Internal.volume_ac_weightL1Measure`)

**Expand the weighted L¹ integral.** Integrating the extended norm against the weighted measure equals integrating the weight times that norm against volume. (`Breakdown.FarField.Internal.lintegral_weightL1Measure`)

**Weighted norm under volume.** The lower integral of the weighted ordinary norm equals the extended-norm integral against the weighted measure. (`Breakdown.FarField.Internal.lintegral_weighted_norm`)

**Integrability of the weighted norm.** Membership in weighted L¹ makes the weighted ordinary norm integrable against volume. (`Breakdown.FarField.Internal.integrable_weighted`)

**Weighted integral equals the L¹ norm.** For weighted-L¹ data, the integral of its weighted norm equals the norm of its weighted L¹ class. (`Breakdown.FarField.Internal.integral_weighted_eq_norm`)

**Physical field as a Fourier transform.** The physical field is the real part of the Fourier transform of the reflected symbol. (`Breakdown.FarField.Internal.physField_eq_realVec_comp`)

**Bound derivatives of a Fourier transform.** An almost everywhere measurable symbol with integrable order-j weight has jth Fourier derivative bounded by (2π)ʲ times its weighted L¹ integral. (`Breakdown.FarField.Internal.norm_iteratedFDeriv_fourier_le`)

**Physical derivatives from Fourier L¹.** For every derivative order, a common constant bounds each pointwise derivative of the reconstructed physical field by the corresponding weighted Fourier L¹ norm whenever that norm is finite. (`Breakdown.FarField.physFieldDerivBound_holds`)

### Breakdown.CertTorus.PicardConverges

This file proves local convergence of Picard iteration to a bounded mild solution, allowing derivative bounds to pass to that solution.

**Picard iterates retain the initial value.** Every Picard iterate takes the prescribed initial value at the starting time. (`Breakdown.FarField.Internal.PicardConvergence.picardIter_self`)

**Heat evolution contracts the X norm.** Heat evolution at nonnegative time does not increase the energy-space norm. (`Breakdown.FarField.Internal.PicardConvergence.norm_heatX_le`)

**Extend a continuous interval curve.** A continuous curve on a closed interval has an almost everywhere strongly measurable, globally bounded extension agreeing with it on that interval. (`Breakdown.FarField.Internal.PicardConvergence.exists_bounded_extension`)

**Integrability of the bilinear time term.** For a continuous curve on a closed interval, its bilinear time integrand is interval integrable up to each time in that interval. (`Breakdown.FarField.Internal.PicardConvergence.bilin_intervalIntegrable`)

**Continuity of every Picard iterate.** Each Picard iterate is continuous on every stated closed time interval. (`Breakdown.FarField.Internal.PicardConvergence.picardIter_continuousOn`)

**Integrate the three-quarter singularity.** A time integrand with the stated (t − s)⁻³ᐟ⁴ bound has integral norm at most 4CL(t − a)¹ᐟ⁴ for a ≤ t. (`Breakdown.FarField.Internal.PicardConvergence.norm_integral_le_kernel`)

**Local Picard convergence.** For each uniform norm bound, a common positive initial time window makes Picard iteration converge pointwise in time to every mild solution satisfying that bound on a positive-length interval. (`Breakdown.FarField.picardConverges_holds`)

### Breakdown.CertTorus.PicardDerivBound

This file propagates bounded derivatives through Picard iteration and gains one derivative with an inverse-square-root time cost.

**Add one Fourier derivative factor.** Prepending one derivative direction multiplies the derivative monomial by its one-direction factor. (`Breakdown.FarField.Internal.PicardDeriv.monoSymbol_cons`)

**Add energy-space derivatives.** Derivative relations of the same order add to give the derivative relation of the sum. (`Breakdown.FarField.Internal.PicardDeriv.isDerivX_add`)

**Differentiate after one coordinate.** Taking one coordinate derivative and then the remaining derivatives gives the combined derivative relation. (`Breakdown.FarField.Internal.PicardDeriv.isDerivX_cons`)

**Differentiate before one coordinate.** Taking the remaining derivatives and then one coordinate derivative gives the combined derivative relation. (`Breakdown.FarField.Internal.PicardDeriv.isDerivX_cons'`)

**Remove the first derivative step.** A first-coordinate derivative and the combined derivative relation determine the remaining derivative relation of that first derivative. (`Breakdown.FarField.Internal.PicardDeriv.isDerivX_of_cons`)

**Higher derivatives of a bilinear term.** The derivative algebra, Leibniz rule and bilinear norm bound give the stated factor-2ᵐ bound from all products of input derivatives through order m. (`Breakdown.FarField.Internal.PicardDeriv.bilin_deriv_bound`)

**Measurability of derivative curves.** The derivative algebra and difference-quotient interface make an almost-everywhere derivative curve measurable when the stated lower derivatives exist. (`Breakdown.FarField.Internal.PicardDeriv.aestronglyMeasurable_deriv`)

**Initial value of every iteration.** Every Picard iterate agrees with its initial value at the starting time. (`Breakdown.FarField.Internal.PicardDeriv.picardIter_self`)

**Picard continuity after the start.** Each Picard iterate is continuous on the time half-line beginning at its initial time. (`Breakdown.FarField.Internal.PicardDeriv.continuousOn_picardIter`)

**Integrate a left-endpoint power.** For exponent greater than −1, the interval integral of (t − s)ʳ has the stated power-antiderivative value. (`Breakdown.FarField.Internal.PicardDeriv.integral_rpow_sub_left`)

**Integrate a right-endpoint power.** For exponent greater than −1, the interval integral of (s − a)ʳ has the stated power-antiderivative value. (`Breakdown.FarField.Internal.PicardDeriv.integral_rpow_sub_right`)

**Integrable left-endpoint power.** The function (t − s)ʳ is interval integrable when r > −1. (`Breakdown.FarField.Internal.PicardDeriv.intervalIntegrable_rpow_sub_left`)

**Integrable right-endpoint power.** The function (s − a)ʳ is interval integrable when r > −1. (`Breakdown.FarField.Internal.PicardDeriv.intervalIntegrable_rpow_sub_right`)

**Compare negative powers.** For positive u and w with w ≤ 2u and −1 ≤ r ≤ 0, uʳ is at most 2wʳ. (`Breakdown.FarField.Internal.PicardDeriv.rpow_le_two_mul`)

**Split the two endpoint singularities.** Between a and t, the product of the three-quarter and half-power singularities is bounded by the stated sum that separates them. (`Breakdown.FarField.Internal.PicardDeriv.split_bound`)

**Integrate the separated singularities.** For a < t, the separated bound integrates to 12(t − a)¹ᐟ⁴(t − a)⁻¹ᐟ². (`Breakdown.FarField.Internal.PicardDeriv.integral_split`)

**Integrate a single singularity.** The interval integral of K(t − s)⁻³ᐟ⁴ equals 4K(t − a)¹ᐟ⁴. (`Breakdown.FarField.Internal.PicardDeriv.integral_low`)

**Heat preserves and gains derivatives.** Under the derivative-heat hypothesis, bounded derivatives through order k remain bounded after heat evolution and order k + 1 gains the stated τ⁻¹ᐟ² bound. (`Breakdown.FarField.Internal.PicardDeriv.heat_deriv_bounds`)

**Bound a derivative of a time integral.** The stated derivative interfaces and integrable majorant give an energy-space derivative of the time integral bounded by the majorant's integral. (`Breakdown.FarField.Internal.PicardDeriv.integral_deriv`)

**Pointwise bilinear derivative bounds.** Under the derivative algebra and Leibniz hypotheses, the stated lower and top input bounds give the displayed time-singular bounds on every bilinear derivative through order k + 1. (`Breakdown.FarField.Internal.PicardDeriv.bilin_pointwise`)

**Lower derivatives of the Duhamel term.** Under the derivative integration hypotheses, derivatives through order k of the Duhamel integral obey the displayed single-singularity integral bound. (`Breakdown.FarField.Internal.PicardDeriv.duhamel_low`)

**Top derivative of the Duhamel term.** Under the derivative integration hypotheses, the order-k + 1 Duhamel derivative obeys the displayed split-singularity integral bound. (`Breakdown.FarField.Internal.PicardDeriv.duhamel_top`)

**Preserve bounds in one Picard step.** The stated initial bounds, calculus interfaces and smallness inequalities propagate both the lower-order bound and the top inverse-square-root bound to the next Picard iterate. (`Breakdown.FarField.Internal.PicardDeriv.picard_step`)

**Picard derivative bounds from calculus.** The derivative algebra, heat, integration, difference-quotient and bilinear Leibniz statements give Picard iterates uniform bounds through each initially controlled derivative order and a next-order bound proportional to the inverse square root of elapsed time on a common positive short interval. (`Breakdown.FarField.picardDerivBoundOfCalculus_holds`)

### Breakdown.CertTorus.PressureGradL2OfWiener

This file proves square integrability of the pressure gradient from weighted Fourier bounds, used to identify the physical pressure.

**Weighted integral-square inequality.** For almost everywhere measurable nonnegative a and c, the square of the integral of ac is bounded by the integral of a times the integral of ac². (`Breakdown.FarField.Internal.PressureGradYoung.sq_lintegral_mul_le`)

**L¹-L² convolution bound.** For measurable nonnegative a and b, the squared L² convolution integral is bounded by the square of the integral of a times the squared integral of b. (`Breakdown.FarField.Internal.PressureGradYoung.lintegral_conv_sq_le`)

**Vector norm from component norms.** A complex vector's norm is at most the sum of its component norms. (`Breakdown.FarField.Internal.PressureGradYoung.norm_le_sum_coord`)

**Derivative norm from the gradient.** The norm of a scalar spatial derivative is at most three times the norm of its gradient vector. (`Breakdown.FarField.Internal.PressureGradYoung.norm_fderiv_le_gradientAt`)

**Extended norm from components.** A complex vector's extended norm is at most the sum of the extended component norms. (`Breakdown.FarField.Internal.PressureGradYoung.enorm_le_sum_coord`)

**Expand the advection symbol.** Each component of the advection symbol is the sum of the three displayed Fourier convolution integrals. (`Breakdown.FarField.Internal.PressureGradYoung.advectionSymbol_apply`)

**Bound an advection integrand.** The stated frequency-weighted bound on f by g controls each advection integrand by ‖f(η)‖‖g(ξ − η)‖. (`Breakdown.FarField.Internal.PressureGradYoung.norm_conv_term_le`)

**Bound the full advection symbol.** An almost-everywhere weighted bound on f by g bounds the extended advection-symbol norm by nine times their norm convolution. (`Breakdown.FarField.Internal.PressureGradYoung.enorm_advectionSymbol_le`)

**Finite squared integral for L² data.** An L² field has finite lower integral of its squared extended norm. (`Breakdown.FarField.Internal.PressureGradYoung.lintegral_enorm_sq_lt_top`)

**Square-integrable advection symbol.** An integrable f, an L² majorant g and the stated frequency and measurability conditions imply that the advection symbol lies in L². (`Breakdown.FarField.Internal.PressureGradYoung.memLp_two_advectionSymbol`)

**Pressure gradient bounded by advection.** The Fourier pressure-gradient vector has norm at most the advection-symbol norm. (`Breakdown.FarField.Internal.PressureGradYoung.norm_grad_pressureSymbol_le`)

**Pressure-gradient L² from Wiener bounds.** The homogeneous Sobolev-to-Wiener statement makes the reconstructed pressure gradient square integrable for every smooth state in the energy space. (`Breakdown.FarField.pressureGradL2OfWiener_holds`)

### Breakdown.CertTorus.PressureIdentification

This file uses truncated Newton potentials and a harmonic-gradient estimate to identify the recovered pressure gradient.

**Smooth ball cutoff.** The ball cutoff is smooth for every radius parameter. (`_private.Breakdown.CertTorus.PressureIdentification.0.Breakdown.FarField.cutoff_smooth`)

**Cutoff is one on the inner ball.** For positive ρ, the ball cutoff equals one when ‖z‖ ≤ ρ. (`_private.Breakdown.CertTorus.PressureIdentification.0.Breakdown.FarField.cutoff_one`)

**Cutoff vanishes beyond twice the radius.** For positive ρ, the ball cutoff is zero when ‖z‖ > 2ρ. (`_private.Breakdown.CertTorus.PressureIdentification.0.Breakdown.FarField.cutoff_zero`)

**Smooth truncated scalar field.** Multiplying a smooth scalar field by the ball cutoff preserves smoothness. (`_private.Breakdown.CertTorus.PressureIdentification.0.Breakdown.FarField.truncated_smooth`)

**Compact support after truncation.** At positive cutoff radius, the product of a scalar field with the ball cutoff has compact support. (`_private.Breakdown.CertTorus.PressureIdentification.0.Breakdown.FarField.truncated_compact`)

**Square integrability of quadratic decay.** The square of D/(1 + ‖x‖)² is integrable on space. (`_private.Breakdown.CertTorus.PressureIdentification.0.Breakdown.FarField.integrable_decay_sq`)

**Identify pressure using harmonic bounds.** The harmonic-gradient bound and truncated Newton statements identify each pressure-gradient component with minus the corresponding Newton gradient whenever the pressure and source are smooth, their Laplacian relation holds, the pressure gradient is square integrable and the source has inverse fourth-power decay. (`Breakdown.FarField.pressureIdentification_of_harmonic`)

### Breakdown.CertTorus.PressureSourceBound

This file bounds the quadratic pressure source by the velocity-gradient norm before applying Newton-potential estimates.

**Unit coordinate vectors.** Each coordinate unit vector has norm one. (`_private.Breakdown.CertTorus.PressureSourceBound.0.Breakdown.FarField.norm_unitVector_eq_one`)

**Matrix entries bounded by operator norm.** Every coordinate entry of a spatial linear map is bounded in absolute value by its operator norm. (`_private.Breakdown.CertTorus.PressureSourceBound.0.Breakdown.FarField.abs_clm_entry_le`)

**Quadratic pressure-source bound.** The pressure-source magnitude is at most nine times the squared velocity-derivative norm. (`_private.Breakdown.CertTorus.PressureSourceBound.0.Breakdown.FarField.abs_pressureSource_le`)

**Smooth pressure source.** A jointly smooth velocity field has a smooth spatial pressure source at every time. (`_private.Breakdown.CertTorus.PressureSourceBound.0.Breakdown.FarField.contDiff_pressureSource`)

**Pressure-source estimate.** A jointly smooth orbit field whose spatial gradient has uniform inverse-square decay has a smooth pressure source with a uniform inverse fourth-power spatial decay bound. (`Breakdown.FarField.pressureSourceBound_holds`)

### Breakdown.CertTorus.PressureSourceDivDiv

This file identifies the pressure source as the double divergence of the velocity tensor square for smooth divergence-free fields.

**Smoothness after one more derivative.** Adding one to the infinite differentiability order remains bounded by infinity. (`Breakdown.FarField.Internal.DivDivSource.top_add_one_le_top`)

**Differentiate a smooth derivative map.** The derivative map of a smooth function is differentiable. (`Breakdown.FarField.Internal.DivDivSource.differentiable_fderiv_of_smooth`)

**Derivative of a vector coordinate.** A differentiable vector field's coordinate derivative is its derivative composed with that coordinate projection. (`Breakdown.FarField.Internal.DivDivSource.coord_hasFDerivAt`)

**Derivative after evaluating a direction.** Differentiating the derivative evaluated on b equals composition with the continuous evaluation map at b. (`Breakdown.FarField.Internal.DivDivSource.slot_hasFDerivAt`)

**Derivative of a directional component.** For a smooth vector field, a directional derivative's component has the stated twice-differentiated linear map. (`Breakdown.FarField.Internal.DivDivSource.slot_coord_hasFDerivAt`)

**Product rule for two components.** The derivative of a product of two field components is the sum of the two product-rule terms. (`Breakdown.FarField.Internal.DivDivSource.product_fderiv_apply`)

**Second derivative of two components.** A smooth field's component product has the displayed four-term second derivative. (`Breakdown.FarField.Internal.DivDivSource.product_second_apply`)

**Derivative of zero divergence.** For a smooth divergence-free field, the corresponding trace of its second derivative is zero. (`Breakdown.FarField.Internal.DivDivSource.sum_second_eq_zero`)

**Pressure source as double divergence.** For a smooth orbit velocity-pressure pair, the pressure source equals the double divergence of the velocity self-tensor at every time and point. (`Breakdown.FarField.pressureSourceDivDiv_holds`)

### Breakdown.CertTorus.PressureSumSecondPartials

This file takes divergence of the smooth similarity equation to derive the pressure Poisson equation.

**Trace of a spatial linear map.** The trace map sums diagonal evaluations on the coordinate basis. (`Breakdown.FarField.Internal.LerayDivergence.traceMap`)

**Evaluate the trace.** The trace map evaluates to the sum of the diagonal entries. (`Breakdown.FarField.Internal.LerayDivergence.traceMap_apply`)

**Divergence as a trace.** The divergence of a field is the trace of its spatial derivative. (`Breakdown.FarField.Internal.LerayDivergence.divergenceAt_eq_traceMap`)

**Smoothness exceeds second order.** Infinite smoothness satisfies the minimum smoothness required for second derivatives. (`Breakdown.FarField.Internal.LerayDivergence.smooth_two_le`)

**Infinite smoothness absorbs a step.** Adding one to the infinite differentiability order remains bounded by infinity. (`Breakdown.FarField.Internal.LerayDivergence.succ_le_smooth`)

**Differentiability of a derivative map.** A smooth function between the stated normed spaces has a differentiable derivative map. (`Breakdown.FarField.Internal.LerayDivergence.differentiable_fderiv`)

**Smooth directional derivative.** Every fixed directional derivative of a smooth spatial function is smooth. (`Breakdown.FarField.Internal.LerayDivergence.contDiff_partial`)

**Differentiate a directional derivative.** Differentiating the derivative evaluated on a equals evaluating the derivative of the derivative on the two directions in the stated order. (`Breakdown.FarField.Internal.LerayDivergence.fderiv_partial_apply`)

**Differentiate a component.** A component of a differentiable vector field has the corresponding component of its derivative. (`Breakdown.FarField.Internal.LerayDivergence.fderiv_component_apply`)

**Differentiate divergence.** For a smooth field, the derivative of divergence is the sum of the indicated second-derivative entries. (`Breakdown.FarField.Internal.LerayDivergence.fderiv_divergence_apply`)

**Divergence of a varying directional term.** The divergence of DV applied to U splits into the derivative of divergence along U and the stated contraction of DV with DU. (`Breakdown.FarField.Internal.LerayDivergence.divergence_fderiv_apply`)

**Solenoidal directional derivatives.** A fixed directional derivative of a smooth divergence-free field is divergence-free. (`Breakdown.FarField.Internal.LerayDivergence.divergence_partial_eq_zero`)

**Divergence of a finite sum.** The divergence of a sum of differentiable fields equals the sum of their divergences. (`Breakdown.FarField.Internal.LerayDivergence.divergence_sum`)

**Laplacian as coordinate derivatives.** For a smooth field, the Laplacian is the sum of the three repeated coordinate derivatives. (`Breakdown.FarField.Internal.LerayDivergence.laplacianAt_eq_sum`)

**Laplacian remains solenoidal.** The Laplacian of a smooth divergence-free field is divergence-free. (`Breakdown.FarField.Internal.LerayDivergence.divergence_laplacian_eq_zero`)

**Expand a spatial vector in its basis.** Every spatial vector is the sum of its coordinates times the coordinate unit vectors. (`Breakdown.FarField.Internal.LerayDivergence.space_eq_sum`)

**Trace of a squared map.** The trace of a linear map composed with itself is the stated double sum of paired matrix entries. (`Breakdown.FarField.Internal.LerayDivergence.trace_comp_self`)

**Laplacian as gradient divergence.** The scalar Laplacian of a smooth pressure equals the divergence of its gradient. (`Breakdown.FarField.Internal.LerayDivergence.laplacian_eq_divergence_gradient`)

**Time derivative remains solenoidal.** A jointly smooth field that is divergence-free at every time has a divergence-free time derivative. (`Breakdown.FarField.Internal.LerayDivergence.divergence_time_deriv`)

**Pressure Poisson equation.** For a smooth orbit velocity-pressure pair, the pressure Laplacian equals minus the pressure source at every time and point. (`Breakdown.FarField.pressureLaplacian_holds`)

### Breakdown.CertTorus.ProfileOpDeriv

This file moves spatial differentiation through the similarity-time profile operator, supplying the derivative bootstrap.

**Scale a kernel integrand.** Kernel convolution commutes with constant scalar multiplication of its tensor integrand. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.kernelConv_const_smul`)

**Derivative of a fixed-time slice.** A jointly C¹ tensor field has the spatial slice derivative obtained by restricting its joint derivative to spatial directions. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.hasFDerivAt_slice`)

**Continuous spatial derivative slices.** A jointly C¹ tensor field has a jointly continuous spatial derivative map. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.continuous_fderiv_slice`)

**Differentiable similarity-shifted tensor.** Every fixed similarity shift of a jointly C¹ tensor field is C¹ in space. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.contDiff_shift`)

**Derivative of the similarity shift.** The shifted tensor derivative is the original slice derivative composed with the inverse-square-root spatial scaling. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.hasFDerivAt_shift`)

**Directional derivative after shifting.** A directional derivative of the shifted tensor equals its shifted directional tensor times the inverse square root of 1 + τ. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.fderiv_shift_apply`)

**The shift preserves a derivative bound.** For positive τ, a uniform nonnegative spatial-derivative bound is preserved by the similarity shift. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.norm_fderiv_shift_le`)

**Measurable shifted convolution.** Joint tensor measurability and kernel measurability make the shifted convolution measurable in time. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.measurable_kernelConv_shift`)

**Decompose a map into its columns.** Every continuous linear map from space equals the sum of its three basis columns multiplied by coordinate projections. (`_private.Breakdown.CertTorus.ProfileOpDeriv.0.Breakdown.FarField.clm_eq_sum_columns`)

**Differentiate the profile operator.** Kernel measurability, the uniform convolution estimate, convolution differentiation, small-time integrability and the Leray-kernel bound allow spatial differentiation of the profile operator on continuously differentiable tensors with bounded value and spatial derivative, increasing its parameter by one half when that parameter is at least one. (`Breakdown.FarField.profileOpDeriv_holds`)

### Breakdown.CertTorus.RadialWeightBound

This file bounds radial decay weights inside balls, distinguishing exponents below and above the spatial dimension.

**Dimension of physical space.** The real dimension of physical space is three. (`Breakdown.FarField.RadialWeightInternal.finrank_space`)

**Nonnegative radial decay weight.** The radial weight is nonnegative at positive scale. (`Breakdown.FarField.RadialWeightInternal.weight_nonneg`)

**Radial decay weight at most one.** At positive scale and nonnegative exponent, the radial decay weight is at most one. (`Breakdown.FarField.RadialWeightInternal.weight_le_one`)

**Bound by the ball volume.** At positive radius and scale and nonnegative exponent, the radial-weight integral is bounded by the ball volume. (`Breakdown.FarField.RadialWeightInternal.volume_bound`)

**Radial power comparison.** For positive radius and scale and nonnegative exponent, the radial integrand is bounded by aᵞ times y²⁻ᵞ. (`Breakdown.FarField.RadialWeightInternal.pointwise_bound`)

**Weight integral below dimension three.** For 0 ≤ γ < 3 and positive radius and scale, the radial-weight integral has the stated aᵞr³⁻ᵞ/(3 − γ) bound. (`Breakdown.FarField.RadialWeightInternal.radial_bound`)

**Weight integral above dimension three.** For γ > 3 and positive scale, the integral over any ball is at most a³ times the full unit-scale weight integral. (`Breakdown.FarField.RadialWeightInternal.whole_bound`)

**Combine volume and decay bounds.** Two bounds by Ar³ and Br³m combine into max(A, B)r³min(1, m) when r is positive and m nonnegative. (`Breakdown.FarField.RadialWeightInternal.combine`)

**Radial-weight estimate.** For every nonnegative exponent γ different from three, the integral of the radial weight (1 + distance/a) to the power −γ over a ball of radius r is bounded by a constant times r³ times min(1, (a/r) to the power min(γ, 3)) for positive a and r. (`Breakdown.FarField.radialWeightBound_holds`)

### Breakdown.CertTorus.RegularStatements

This file defines the Fourier and Sobolev interfaces for the weak-to-smooth profile argument of Proposition 7.11 and records how their proofs assemble.

**Symmetric energy-space representative.** The symmetric symbol is the chosen pointwise representative of the energy-space element's complex L² class. (`Breakdown.FarField.symX`)

**Homogeneous Sobolev energy.** The order-k Sobolev energy is the homogeneous squared Fourier norm of the symmetric symbol. (`Breakdown.FarField.homSob`)

**Smoothness in the energy space.** An energy-space element is smooth when every nonnegative-order homogeneous Sobolev energy is finite. (`Breakdown.FarField.IsSmoothX`)

**Continuous Sobolev curve.** A curve is Sobolev continuous on S when its order-k energies are finite there and the energy of each increment tends to zero within S. (`Breakdown.FarField.IsHomSobolevCurve`)

**Velocity symbol.** The velocity symbol symmetrizes the energy-space representative under conjugate reflection, projects it by Leray and divides by 2π‖ξ‖. (`Breakdown.FarField.velSymbol`)

**Fourier derivative monomial.** The derivative monomial multiplies the factors 2πiξ in the specified coordinate directions. (`Breakdown.FarField.monoSymbol`)

**Energy-space derivative relation.** The derivative relation requires the symmetric symbol of y to equal the derivative monomial times that of x almost everywhere. (`Breakdown.FarField.IsDerivX`)

**Spatial translation in X.** The translation operator multiplies the Fourier representative by exp(−2πi〈h, ξ〉) and restricts the result to X. (`Breakdown.FarField.shiftX`)

**Picard iterates.** Picard iteration begins with heat evolution and repeatedly adds the time-integrated bilinear term formed from the previous iterate. (`Breakdown.FarField.fixedPointIter`)

**Reconstructed orbit velocity.** The orbit field is the physical reconstruction of the velocity symbol at each orbit time. (`Breakdown.FarField.orbitField`)

**Reconstructed orbit pressure.** The orbit pressure is the scalar reconstruction of the pressure symbol formed from the orbit's velocity symbol. (`Breakdown.FarField.orbitPressure`)

**Sobolev-to-Wiener interface.** This interface asks for a weighted Fourier L¹ bound in terms of the square root of the zero-order and order-k + 1 Sobolev energies. (`Breakdown.FarField.HomWiener`)

**Velocity reconstruction interface.** This interface identifies the L⁶ velocity of a smooth energy-space element with its Fourier reconstruction almost everywhere. (`Breakdown.FarField.VelocityOfSymbol`)

**Reconstruction from Wiener bounds.** This interface asks that the Sobolev-to-Wiener bound imply the velocity-reconstruction identity. (`Breakdown.FarField.VelocityOfSymbolOfWiener`)

**Bilinear Fourier-symbol interface.** This interface identifies the symmetric symbol of the positive-time bilinear term of a smooth state with its heat-weighted nonlinear velocity symbol almost everywhere. (`Breakdown.FarField.BilinSymbol`)

**Bilinear symbol from reconstruction.** This interface asks that the Wiener bound and velocity reconstruction imply the bilinear-symbol identity. (`Breakdown.FarField.BilinSymbolOfVelocity`)

**Sobolev derivatives and norm bounds.** This interface relates finite Sobolev energy to existence of all coordinate derivatives of that order and bounds the energy from uniform derivative norms. (`Breakdown.FarField.DerivSobolev`)

**Algebra of energy-space derivatives.** This interface packages uniqueness, order-zero identity, linearity, permutation and composition of energy-space derivative relations. (`Breakdown.FarField.DerivAlgebra`)

**Heat smoothing of derivatives.** This interface requires heat evolution to commute with derivatives and to gain every derivative order with its stated time-power bound. (`Breakdown.FarField.DerivHeat`)

**Derivatives through time integrals.** This interface requires integration of an interval-integrable derivative curve to give the derivative of the integrated curve. (`Breakdown.FarField.DerivIntegral`)

**Closedness under bounded derivatives.** This interface passes a derivative bound through a convergent sequence of energy-space inputs. (`Breakdown.FarField.DerivClosed`)

**Translation covariance of bilinearity.** This interface requires simultaneous translation of two inputs to translate their positive-time bilinear output. (`Breakdown.FarField.ShiftCovariance`)

**Derivatives as difference quotients.** This interface identifies one-coordinate derivative relations with limits of the stated translation difference quotients. (`Breakdown.FarField.DiffQuotient`)

**Leibniz rule for the bilinear map.** This interface requires a coordinate derivative of the positive-time bilinear map to split into derivatives in its two inputs. (`Breakdown.FarField.BilinLeibniz`)

**Leibniz rule from translations.** This interface asks that translation covariance and difference quotients imply the bilinear Leibniz rule. (`Breakdown.FarField.BilinLeibnizOfShift`)

**Convergence of local Picard iteration.** This interface requires a uniform short time on which Picard iterates converge pointwise to each mild solution with the stated norm bound. (`Breakdown.FarField.PicardConverges`)

**Derivative bounds for Picard iterates.** This interface requires uniform short-time bounds through order k for every iterate and an inverse-square-root bound at order k + 1. (`Breakdown.FarField.PicardDerivBound`)

**Picard bounds from calculus.** This interface asks that derivative algebra, heat smoothing, integration, difference quotients and the bilinear Leibniz rule imply Picard derivative bounds. (`Breakdown.FarField.PicardDerivBoundOfCalculus`)

**Local gain of one derivative.** This interface gives a short-time derivative gain for bounded mild solutions with bounded initial derivatives through order k. (`Breakdown.FarField.LocalGain`)

**Restriction of a mild solution.** This interface requires a mild solution on [a, b] to remain mild on [a′, b] whenever a ≤ a′ ≤ b. (`Breakdown.FarField.MildRestrict`)

**Smoothing inside a mild interval.** This interface requires every later closed portion of a mild interval to be a Sobolev curve at every order. (`Breakdown.FarField.MildSmoothing`)

**Almost-everywhere Duhamel symbols.** This interface requires the velocity symbols of a mild Sobolev curve to satisfy the Fourier Duhamel formula almost everywhere at each time. (`Breakdown.FarField.DuhamelSymbolAe`)

**Duhamel identity from bilinear symbols.** This interface asks that the bilinear-symbol and Sobolev-to-Wiener estimates imply the almost-everywhere Fourier Duhamel identity. (`Breakdown.FarField.DuhamelSymbolOfBilinSymbol`)

**Differentiable weighted symbol curve.** This interface requires the weighted L¹ velocity-symbol curve to have the stated time derivative within the closed mild interval. (`Breakdown.FarField.SymbolCurve`)

**Symbol derivatives from Duhamel.** This interface asks that the Duhamel-symbol and Wiener estimates imply the differentiable weighted-symbol curve. (`Breakdown.FarField.SymbolCurveOfDuhamel`)

**Smooth physical solution from symbols.** This interface turns solenoidal symbols with every weighted L¹ moment and the stated time derivatives into smooth physical velocity and pressure satisfying the PDE and zero divergence. (`Breakdown.FarField.WienerSolution`)

**Dilation of symbols and physical fields.** This interface packages Sobolev scaling and continuity together with the stated velocity and pressure dilation identities for smooth states. (`Breakdown.FarField.DilateSymbol`)

**Rotation of symbols and physical fields.** This interface requires rotation to preserve Sobolev energies and weighted Fourier L¹ norms and to rotate the reconstructed field as stated. (`Breakdown.FarField.RotateSymbol`)

**Recover the similarity equation.** This interface transfers smooth physical-window solutions and their zero divergence to smooth similarity velocity and pressure with zero similarity residual on the corresponding open interval. (`Breakdown.FarField.WindowResidual`)

**Physical windows of an orbit.** This interface requires every rotationally periodic energy-space orbit to give a physical mild window on [0, T] whenever 0 < T < 1. (`Breakdown.FarField.OrbitWindows`)

**Pointwise derivatives from weighted L¹.** This interface bounds each physical derivative order by the matching weighted Fourier L¹ norm. (`Breakdown.FarField.PhysFieldDerivBound`)

**Square-integrable pressure derivative.** This interface requires the reconstructed pressure of every smooth energy-space state to have an L² spatial derivative. (`Breakdown.FarField.PressureGradL2`)

**Pressure L² estimate from Wiener.** This interface asks that the Sobolev-to-Wiener estimate imply square integrability of the pressure derivative. (`Breakdown.FarField.PressureGradL2OfWiener`)

**Smooth orbit solution.** This interface requires every orbit state, its reconstructed velocity and pressure to be smooth and to solve the similarity equation with zero divergence. (`Breakdown.FarField.OrbitSmooth`)

**Sobolev regularity of an orbit.** This interface requires every orbit to be a Sobolev curve at every order on the whole real time axis. (`Breakdown.FarField.OrbitHomSobolev`)

**Orbit Sobolev regularity from windows.** This interface asks that physical windows, mild smoothing and symbol dilation imply global orbit Sobolev regularity. (`Breakdown.FarField.OrbitHomSobolevOfWindows`)

**Uniform orbit derivatives.** This interface requires a uniform bound on the reconstructed orbit field's derivatives through order three. (`Breakdown.FarField.OrbitDerivBound`)

**Orbit bounds from weighted symbols.** This interface asks that orbit Sobolev regularity, Wiener estimates, rotations and physical derivative bounds imply the uniform orbit-derivative bound. (`Breakdown.FarField.OrbitDerivBoundOfSymbolCurve`)

**Vanishing spatial orbit tail.** This interface requires the reconstructed orbit field to have a vanishing spatial tail. (`Breakdown.FarField.OrbitTail`)

**Identify the orbit rotation operator.** The rotation operator in the realization equals the energy-space rotation operator. (`Breakdown.FarField.realization_rot_eq`)

**Assemble a smooth orbit field.** The orbit smoothness, derivative-bound, tail, velocity-reconstruction, symbol-rotation and pressure-gradient L² statements give every rotation-periodic orbit a smooth velocity-pressure representative with the required periodicity and decay properties. (`Breakdown.FarField.smoothFieldOfOrbit_of_regularity`)

### Breakdown.CertTorus.RotateSymbol

This file proves that rotations preserve the Fourier and Sobolev quantities used to obtain uniform bounds along the orbit.

**Coordinates of a rotated vector.** Each coordinate of a rotated vector is the matrix-coordinate sum against its original coordinates. (`Breakdown.FarField.Internal.RotateSymbol.apply_coord`)

**Coordinates of a complex rotation.** Complex rotation uses the same real matrix coefficients acting on complex coordinates. (`Breakdown.FarField.Internal.RotateSymbol.rotC_apply`)

**Complex scaling commutes with rotation.** Rotating a complex scalar multiple equals that scalar times the rotated vector. (`Breakdown.FarField.Internal.RotateSymbol.rotC_complex_smul`)

**Compose complex rotations.** Successive complex rotations equal the complex rotation of the composed spatial isometries. (`Breakdown.FarField.Internal.RotateSymbol.rotC_comp`)

**Identity complex rotation.** The complex rotation induced by the identity spatial map leaves the vector unchanged. (`Breakdown.FarField.Internal.RotateSymbol.rotC_refl`)

**Cancel a complex rotation.** Applying the inverse complex rotation after a rotation returns the original vector. (`Breakdown.FarField.Internal.RotateSymbol.rotC_symm_rotC`)

**Real parts commute with rotation.** Taking real parts after complex rotation equals rotating the real-part vector. (`Breakdown.FarField.Internal.RotateSymbol.realVec_rotC`)

**Conjugation commutes with rotation.** Complex conjugation commutes with complex rotation. (`Breakdown.FarField.Internal.RotateSymbol.conjVec_rotC`)

**Complexify a rotated real vector.** Complexifying a real rotated vector equals complex rotation of its complexification. (`Breakdown.FarField.Internal.RotateSymbol.complexifyVec_map`)

**Imaginary-part vector.** The imaginary-part vector collects the imaginary coordinate parts as a real spatial vector. (`Breakdown.FarField.Internal.RotateSymbol.imVec`)

**Real coordinate after rotation.** The real part of a rotated complex coordinate is the corresponding coordinate of the rotated real-part vector. (`Breakdown.FarField.Internal.RotateSymbol.re_rotC`)

**Imaginary coordinate after rotation.** The imaginary part of a rotated complex coordinate is the corresponding coordinate of the rotated imaginary-part vector. (`Breakdown.FarField.Internal.RotateSymbol.im_rotC`)

**Split the complex squared norm.** The squared complex-vector norm is the sum of the squared norms of its real and imaginary parts. (`Breakdown.FarField.Internal.RotateSymbol.normSq_split`)

**Rotation preserves complex norm.** Complex rotation preserves the ordinary vector norm. (`Breakdown.FarField.Internal.RotateSymbol.norm_rotC`)

**Rotation preserves extended norm.** Complex rotation preserves the extended vector norm. (`Breakdown.FarField.Internal.RotateSymbol.enorm_rotC`)

**Complex rotation as a real isometry.** Complex rotation is packaged as a real linear isometry. (`Breakdown.FarField.Internal.RotateSymbol.rotCIsom`)

**Evaluate the packaged isometry.** The packaged real linear isometry acts as the complex rotation. (`Breakdown.FarField.Internal.RotateSymbol.rotCIsom_apply`)

**Rotated basis pairing.** Pairing a rotated vector with a rotated coordinate unit vector recovers the original coordinate. (`Breakdown.FarField.Internal.RotateSymbol.inner_coord`)

**Rotation preserves frequency pairing.** Rotating the real frequency and complex vector together preserves their bilinear coordinate pairing. (`Breakdown.FarField.Internal.RotateSymbol.dot_rotC`)

**Leray projection commutes with rotation.** Leray projection at the rotated frequency commutes with rotation of the complex vector. (`Breakdown.FarField.Internal.RotateSymbol.lerayC_rotC`)

**Rotate a symmetric symbol.** The symmetric symbol of a rotated state is the rotated original symbol at inverse-rotated frequency almost everywhere. (`Breakdown.FarField.Internal.RotateSymbol.symX_rotX_ae`)

**Rotate a velocity symbol.** The velocity symbol of a rotated state is the rotated original velocity symbol at inverse-rotated frequency almost everywhere. (`Breakdown.FarField.Internal.RotateSymbol.velSymbol_rotX_ae`)

**Rotation preserves the weighted measure.** The inverse spatial rotation preserves every radial weighted Fourier measure. (`Breakdown.FarField.Internal.RotateSymbol.measurePreserving_weight`)

**Transfer weighted L¹ under rotation.** An almost-everywhere rotated copy of a weighted-L¹ field remains in weighted L¹ with equal norm. (`Breakdown.FarField.Internal.RotateSymbol.weight_transfer`)

**Recover the unrotated velocity symbol.** The original velocity symbol is recovered almost everywhere by inverse-rotating the rotated state's symbol. (`Breakdown.FarField.Internal.RotateSymbol.velSymbol_rotX_ae_inv`)

**Rotation preserves Sobolev energies.** Rotating an energy-space state preserves every homogeneous Sobolev energy. (`Breakdown.FarField.Internal.RotateSymbol.homSob_rotX`)

**Rotation preserves weighted L¹ norms.** Rotation preserves every weighted Fourier L¹ norm of the velocity symbol. (`Breakdown.FarField.Internal.RotateSymbol.weightNorm_rotX`)

**Rotate the reconstructed field.** Reconstructing a rotated state's velocity rotates its value and inverse-rotates its spatial argument. (`Breakdown.FarField.Internal.RotateSymbol.physField_rotX`)

**Rotation preserves symbol norms.** Rotating a state preserves every homogeneous Sobolev energy and weighted Fourier L¹ velocity norm, and reconstructs the correspondingly rotated physical field. (`Breakdown.FarField.rotateSymbol_holds`)

### Breakdown.CertTorus.SecondDerivBootstrap

This file improves the spatial decay of second profile derivatives by differentiating the quadratic tensor term twice.

**Tensor product as a bounded bilinear map.** The tensor-product map sends two spatial vectors to the matrix of their coordinate products. (`Breakdown.FarField.SecondDeriv.Internal.tensorBilin`)

**Norm of the tensor bilinear map.** The tensor-product bilinear map has operator norm at most one. (`Breakdown.FarField.SecondDeriv.Internal.tensorBilin_norm_le`)

**Evaluate the tensor product.** Applying the bilinear tensor map gives the coordinate product aⱼbₖ. (`Breakdown.FarField.SecondDeriv.Internal.tensorBilin_apply`)

**Tensor square through the bilinear map.** The field tensor square equals the tensor bilinear map applied pointwise to two copies of the field. (`Breakdown.FarField.SecondDeriv.Internal.pairTensor_eq_tensorBilin`)

**Bound a second tensor derivative.** For a smooth field, the second directional derivative of its tensor square is bounded by the stated sum of field-times-Hessian and squared-gradient terms. (`Breakdown.FarField.SecondDeriv.Internal.norm_secondDirectional_le`)

**Combine derivative decay exponents.** Under the stated nonnegativity and exponent inequalities, the weighted quadratic derivative terms are bounded by 2AM + 2B². (`Breakdown.FarField.SecondDeriv.Internal.weight_combine`)

**Improve second-derivative decay.** The integral representation and stated weighted bounds give second-derivative decay at min(γt, 3) when γt is nonnegative, differs from three and obeys the two exponent limits. (`Breakdown.FarField.SecondDeriv.Internal.secondDeriv_weight_gain`)

**Second-derivative bootstrap.** The weighted operator-bound and Leray-kernel-bound statements give inverse-cube second-derivative decay for a smooth field with bounded derivatives through order two, inverse-first-power value decay, inverse-square gradient decay and the stated profile representation of its second derivative. (`Breakdown.FarField.secondDerivBootstrap_of_op`)

### Breakdown.CertTorus.ShiftCovariance

This file proves translation covariance of the bilinear evolution, which supplies its derivative Leibniz rule through difference quotients.

**Fourier translation phase.** The translation phase is exp(−2πi〈h, ξ〉). (`Breakdown.FarField.Internal.TranslationCovariance.phase`)

**Modulation on complex L².** The modulation operator multiplies complex L² data by the translation phase. (`Breakdown.FarField.Internal.TranslationCovariance.modL2`)

**Translation as restricted modulation.** The energy-space translation is the restriction of the complex L² modulation operator. (`Breakdown.FarField.Internal.TranslationCovariance.shiftX_eq`)

**Unit norm of the translation phase.** The Fourier translation phase has norm one. (`Breakdown.FarField.Internal.TranslationCovariance.norm_phase`)

**Continuous translation phase.** At fixed shift, the translation phase is continuous in frequency. (`Breakdown.FarField.Internal.TranslationCovariance.continuous_phase`)

**Cancel opposite translation phases.** Multiplying the phases for opposite shifts gives one. (`Breakdown.FarField.Internal.TranslationCovariance.phase_mul_neg`)

**Conjugate-reflection of the phase.** Conjugating the phase at the opposite frequency returns the original phase. (`Breakdown.FarField.Internal.TranslationCovariance.conj_phase_neg`)

**Measurable phase multiplication.** The phase multiplication operator is almost everywhere strongly measurable in frequency. (`Breakdown.FarField.Internal.TranslationCovariance.meas_phase`)

**Norm bound for phase multiplication.** Multiplication by a translation phase has operator norm at most one. (`Breakdown.FarField.Internal.TranslationCovariance.bound_phase`)

**Pointwise modulation representative.** The L² modulation class is represented almost everywhere by pointwise phase multiplication. (`Breakdown.FarField.Internal.TranslationCovariance.modL2_ae`)

**Complex-linear multipliers commute.** A bounded measurable complex-linear field multiplier commutes with phase modulation on L². (`Breakdown.FarField.Internal.TranslationCovariance.fieldOp_modL2`)

**Two complex scalings commute.** Complex multiplication commutes with complex scalar multiplication of a vector. (`Breakdown.FarField.Internal.TranslationCovariance.cmul_smul_comm`)

**Conjugate a complex scalar multiple.** Conjugating a scaled vector conjugates both its scalar and its vector. (`Breakdown.FarField.Internal.TranslationCovariance.conjVec_smul`)

**Longitudinal projection and scaling.** Longitudinal projection commutes with complex scalar multiplication. (`Breakdown.FarField.Internal.TranslationCovariance.longitudinal_smul_comm`)

**Null-set equality under reflection.** Reflecting frequency preserves almost-everywhere equality with respect to volume. (`Breakdown.FarField.Internal.TranslationCovariance.ae_comp_neg`)

**Modulation preserves the symbol space.** Phase modulation preserves membership in the admissible symbol subspace. (`Breakdown.FarField.Internal.TranslationCovariance.modL2_mem_sig`)

**Underlying L² class of a translation.** The L² class of an energy-space translation equals modulation of the underlying class. (`Breakdown.FarField.Internal.TranslationCovariance.shiftX_coe`)

**Modulation preserves the L² norm.** Phase modulation preserves the complex L² norm. (`Breakdown.FarField.Internal.TranslationCovariance.norm_modL2`)

**Translation preserves the X norm.** Spatial translation preserves the energy-space norm. (`Breakdown.FarField.Internal.TranslationCovariance.norm_shiftX`)

**Cancel opposite spatial translations.** Translating by −h and then h returns the original state. (`Breakdown.FarField.Internal.TranslationCovariance.shiftX_shiftX_neg`)

**Translation across an inner product.** A translation on the first argument of the real inner product equals the opposite translation on the second argument. (`Breakdown.FarField.Internal.TranslationCovariance.inner_shiftX`)

**Null-set equality under translation.** Translating the argument preserves almost-everywhere equality with respect to volume. (`Breakdown.FarField.Internal.TranslationCovariance.ae_comp_sub`)

**Translation isometry on L².** The physical L² translation is the measure-preserving pullback by y ↦ y − h. (`Breakdown.FarField.Internal.TranslationCovariance.transL2`)

**Pointwise L² translation.** The L² translation class is represented almost everywhere by translating the original representative. (`Breakdown.FarField.Internal.TranslationCovariance.transL2_ae`)

**Fourier transform of a translation.** Translating a field multiplies its Fourier transform by the translation phase. (`Breakdown.FarField.Internal.TranslationCovariance.fourier_translate`)

**Translate a Schwartz L² class.** Translating the L² class of a Schwartz function agrees with the L² class of its translated Schwartz function. (`Breakdown.FarField.Internal.TranslationCovariance.transL2_toLp`)

**Fourier transform of a Schwartz class.** The L² Fourier transform of a Schwartz class is the L² class of its ordinary Fourier transform. (`Breakdown.FarField.Internal.TranslationCovariance.fourierL2_toLp`)

**Translation under the L² transform.** The L² Fourier transform sends physical translation to frequency modulation. (`Breakdown.FarField.Internal.TranslationCovariance.fourier_transL2`)

**Modulation under inverse Fourier.** The inverse L² Fourier transform sends frequency modulation to physical translation. (`Breakdown.FarField.Internal.TranslationCovariance.fourierInv_modL2`)

**Translate the physical representative.** Modulating the Fourier class translates its physical representative almost everywhere. (`Breakdown.FarField.Internal.TranslationCovariance.toPhys_modL2`)

**Translation of a partial field.** A partial field of a translated state is the translated original partial field almost everywhere. (`Breakdown.FarField.Internal.TranslationCovariance.partialX_shift`)

**Translation of the smoothing test field.** At positive time, the smoothing test field of a translated state is the translated original field almost everywhere. (`Breakdown.FarField.Internal.TranslationCovariance.phiX_shift`)

**Translated test fields.** Translating a test field preserves the test-field conditions. (`Breakdown.FarField.Internal.TranslationCovariance.test_translate`)

**Partials commute with translation.** A coordinate partial of a translated field is the translated coordinate partial. (`Breakdown.FarField.Internal.TranslationCovariance.partialField_translate`)

**Translate a complexified L² field.** Complexifying the L² class of translated real data equals translating its complexified L² class. (`Breakdown.FarField.Internal.TranslationCovariance.complexify_translate`)

**Translate a gradient representation.** Translating a test field modulates its gradient representation by the translation phase. (`Breakdown.FarField.Internal.TranslationCovariance.ofGrad_translate`)

**Translate an embedded test field.** Translating an embedded test field agrees with embedding its translated physical field. (`Breakdown.FarField.Internal.TranslationCovariance.embed_translate`)

**Translate an L⁶ velocity.** The velocity of a translated state is the translated original velocity almost everywhere. (`Breakdown.FarField.Internal.TranslationCovariance.velocity_shift`)

**Move translations in a trilinear form.** Translating both energy-space inputs moves the opposite shift to the test argument of the trilinear form. (`Breakdown.FarField.Internal.TranslationCovariance.trilinear_shift`)

**Move translations in the bilinear form.** At positive time, translating both bilinear inputs moves the inverse translation to the test state. (`Breakdown.FarField.Internal.TranslationCovariance.bilinForm_shift`)

**Bilinear map satisfies its specification.** The chosen positive-time bilinear map satisfies its defining specification. (`Breakdown.FarField.Internal.TranslationCovariance.bilinX_spec`)

**Bilinear translation covariance.** At positive time, the bilinear evolution map commutes with translating both inputs by the same spatial vector. (`Breakdown.FarField.shiftCovariance_holds`)

### Breakdown.CertTorus.SmallTimeIntegrable

This file controls the inverse-square-root time singularity in profile-operator integrals.

**Inverse square root as a real power.** At positive time, the reciprocal square root equals τ⁻¹ᐟ². (`Breakdown.FarField.SmallTimeWeight.Internal.inv_sqrt_eq_rpow`)

**Combine inverse time and square root.** At positive time, τ⁻¹ times the reciprocal square root equals τ⁻³ᐟ². (`Breakdown.FarField.SmallTimeWeight.Internal.inv_mul_inv_sqrt_eq_rpow`)

**Time decay weight at most one.** At nonnegative time and exponent, (1 + τ)⁻ᵝ is at most one. (`Breakdown.FarField.SmallTimeWeight.Internal.weight_le_one`)

**Inverse-time bound for the weight.** When τ and β are at least one, (1 + τ)⁻ᵝ is at most τ⁻¹. (`Breakdown.FarField.SmallTimeWeight.Internal.weight_le_inv`)

**Small-time integrability estimate.** For every natural n, the function (1 + time) to the power −(1 + n/2) divided by the square root of time is integrable over positive times. (`Breakdown.FarField.smallTimeIntegrable_holds`)

### Breakdown.CertTorus.SymbolCurve

This file differentiates the velocity-symbol curve in weighted Fourier L¹ spaces using the almost-everywhere Duhamel equation.

**Measurable complex Leray projection.** The complex Leray projection is measurable jointly in frequency and vector. (`Breakdown.FarField.Internal.SymbolCurve.measurable_lerayC_prod`)

**Velocity symbol of a representative.** The velocity reconstruction symmetrizes a representative under conjugate reflection, projects it and divides by 2π‖ξ‖. (`Breakdown.FarField.Internal.SymbolCurve.velOf`)

**Velocity symbol from its representative.** The energy-space velocity symbol is the representative reconstruction applied to its symmetric symbol. (`Breakdown.FarField.Internal.SymbolCurve.velSymbol_eq`)

**Measurable velocity reconstruction.** A measurable Fourier representative gives a measurable reconstructed velocity symbol. (`Breakdown.FarField.Internal.SymbolCurve.measurable_velOf`)

**Subtract Leray projections.** Leray projection preserves subtraction of complex vectors. (`Breakdown.FarField.Internal.SymbolCurve.divFreeC_sub`)

**Subtract reconstructed symbols.** The velocity reconstruction of a difference is the difference of the reconstructed symbols. (`Breakdown.FarField.Internal.SymbolCurve.velOf_sub`)

**Reconstruction respects null sets.** Almost-everywhere equal representatives give almost-everywhere equal reconstructed velocity symbols. (`Breakdown.FarField.Internal.SymbolCurve.velOf_congr_ae`)

**Subtract symmetric symbols.** The symmetric symbol of a difference agrees almost everywhere with the difference of the symbols. (`Breakdown.FarField.Internal.SymbolCurve.symX_sub_ae`)

**Subtract velocity symbols.** The velocity symbol of a difference agrees almost everywhere with the difference of the velocity symbols. (`Breakdown.FarField.Internal.SymbolCurve.velSymbol_sub_ae`)

**Measurable velocity symbol.** Every energy-space velocity symbol is measurable. (`Breakdown.FarField.Internal.SymbolCurve.measurable_velSymbol`)

**Expand a weighted lower integral.** Integrating against the weighted Fourier measure equals integrating the radial weight times the integrand against volume. (`Breakdown.FarField.Internal.SymbolCurve.lintegral_weightL1`)

**Volume below the weighted measure.** Volume is absolutely continuous with respect to each weighted Fourier measure. (`Breakdown.FarField.Internal.SymbolCurve.volume_ac_weightL1`)

**Identify the weighted L¹ class.** For a field in weighted L¹, its chosen weighted class equals the class obtained from that membership proof. (`Breakdown.FarField.Internal.SymbolCurve.toWeightL1_eq`)

**Absorb a frequency power into a weight.** A factor ‖ξ‖ʲ under the order-k weighted integral is bounded by the order-k + j weighted integral. (`Breakdown.FarField.Internal.SymbolCurve.lintegral_weight_mul_le`)

**Finite Sobolev energies give weighted L¹.** The Wiener interface and finite energies at orders zero and k + 1 imply weighted-L¹ membership of the velocity symbol. (`Breakdown.FarField.Internal.SymbolCurve.memLp_velSymbol`)

**Bound symbol differences in weighted L¹.** The Wiener interface bounds the weighted L¹ difference of velocity symbols by the stated Sobolev energies of the state difference. (`Breakdown.FarField.Internal.SymbolCurve.lintegral_velSymbol_sub_le`)

**Weighted symbols along a Sobolev curve.** Under the Wiener interface, every state on a curve with all Sobolev orders has a velocity symbol in every weighted L¹ space. (`Breakdown.FarField.Internal.SymbolCurve.memLp_curve`)

**Weighted symbol increments vanish.** Along a curve with all Sobolev orders, the Wiener interface makes each weighted L¹ integral of velocity-symbol increments tend to zero. (`Breakdown.FarField.Internal.SymbolCurve.tendsto_lintegral_vel_sub`)

**Continuous weighted symbol curve.** The Wiener interface makes the weighted-L¹ velocity-symbol class continuous along a curve with all Sobolev orders. (`Breakdown.FarField.Internal.SymbolCurve.continuousOn_toWeightL1_vel`)

**Continuous nonlinear map on weighted L¹.** The nonlinear symbol induces a continuous map from order-k + 1 weighted L¹ classes to order-k weighted L¹ classes. (`Breakdown.FarField.Internal.SymbolCurve.exists_nonlin_map`)

**Joint representative of an L¹ curve.** A continuous L¹-valued curve on a closed interval has a jointly strongly measurable representative agreeing almost everywhere at every time. (`Breakdown.FarField.Internal.SymbolCurve.exists_measurable_version`)

**Advection ignores null-set changes.** Almost-everywhere changes in both Fourier inputs leave the bilinear advection symbol unchanged. (`Breakdown.FarField.Internal.SymbolCurve.advectionBilin_congr_ae`)

**Nonlinearity ignores null-set changes.** Almost-everywhere equal Fourier fields have identical nonlinear symbols. (`Breakdown.FarField.Internal.SymbolCurve.nonlinSymbol_congr_ae`)

**Measurable nonlinear time slices.** A jointly measurable Fourier field has a jointly measurable nonlinear symbol. (`Breakdown.FarField.Internal.SymbolCurve.measurable_nonlin_section`)

**Heat-symbol semigroup law.** The heat symbol at x + y is the product of its heat symbols at x and y. (`Breakdown.FarField.Internal.SymbolCurve.heatSymbol_add`)

**Continuous heat-symbol time curve.** At fixed terminal time and frequency, the complex-cast heat symbol is continuous in the starting time. (`Breakdown.FarField.Internal.SymbolCurve.continuous_heat_coe`)

**Restart a Duhamel identity.** Two Duhamel identities from a common starting time and an integrable nonlinear term yield the restarted identity between p and q when a ≤ p ≤ q. (`Breakdown.FarField.Internal.SymbolCurve.duhamel_restart`)

**Quadratic exponential remainder.** For nonnegative y, the error exp(−y) − 1 + y has absolute value at most y². (`Breakdown.FarField.Internal.SymbolCurve.abs_exp_neg_sub_le`)

**Linear exponential bound.** For every real y, 1 − exp(−y) is at most y. (`Breakdown.FarField.Internal.SymbolCurve.one_sub_exp_neg_le`)

**Bound a Duhamel increment.** For p ≤ q and an integrable nonlinear term, subtracting the frozen value times q − p leaves the stated variation integral plus a quadratic time remainder. (`Breakdown.FarField.Internal.SymbolCurve.enorm_duhamel_sub_le`)

**Extended norm of real scaling.** The extended norm of a complex-cast real scalar multiple is the absolute scalar cast to the nonnegative reals times the vector's extended norm. (`Breakdown.FarField.Internal.SymbolCurve.enorm_smul_real`)

**Bound the derivative remainder.** The stated restarted Duhamel identity bounds its first-order increment remainder by the displayed frequency-weighted quadratic and continuity terms. (`Breakdown.FarField.Internal.SymbolCurve.enorm_increment_le`)

**Split a nonnegative scalar factor.** Under the stated factorization with nonnegative h and X′, casting to extended nonnegative reals factors the product as displayed. (`Breakdown.FarField.Internal.SymbolCurve.ofReal_mul_split`)

**Weighted derivative from increments.** The stated weighted integrability, continuity and almost-everywhere Duhamel identities imply the displayed derivative within the closed interval of the weighted-L¹ curve. (`Breakdown.FarField.Internal.SymbolCurve.hasDerivWithinAt_of_increment`)

**Symbol curve from Duhamel.** The almost-everywhere Duhamel symbol formula and homogeneous Sobolev-to-Wiener estimate give the prescribed time derivative in every weighted Fourier L¹ space for a mild solution on a positive-length interval with homogeneous Sobolev regularity of every order. (`Breakdown.FarField.symbolCurveOfDuhamel_holds`)

### Breakdown.CertTorus.TensorDerivDecay

This file derives decay of tensor derivatives from weighted bounds on velocity derivatives, used in the pressure-source representation.

**Algebraic outer product.** The algebraic outer product maps two spatial vectors to their coordinate-product matrix. (`Breakdown.FarField.TensorDerivDecayInternal.outerProductLinear`)

**Outer-product norm bound.** The outer-product matrix norm is at most the product of the two vector norms. (`Breakdown.FarField.TensorDerivDecayInternal.norm_outerProductLinear_le`)

**Continuous outer product.** The bounded algebraic outer product is packaged as a continuous bilinear map. (`Breakdown.FarField.TensorDerivDecayInternal.outerProduct`)

**Outer-product operator norm.** The continuous outer product has operator norm at most one. (`Breakdown.FarField.TensorDerivDecayInternal.norm_outerProduct_le`)

**Represent the field tensor square.** The field tensor square is the continuous outer product of the field with itself. (`Breakdown.FarField.TensorDerivDecayInternal.pairTensor_eq_outerProduct`)

**Weighted bound as a decay quotient.** An integer-order weighted bound implies the corresponding norm bound C divided by (1 + ‖y‖)ⁿ. (`Breakdown.FarField.TensorDerivDecayInternal.norm_le_of_weightedBound`)

**Decay of tensor derivatives.** For a jointly smooth field whose value, gradient and second derivative have uniform inverse first-, second- and third-power decay, its self-tensor has derivatives through order two decaying by the inverse power 2 plus the derivative order. (`Breakdown.FarField.tensorDerivDecay_holds`)

### Breakdown.CertTorus.TensorWeight

This file supplies the tensor-product estimate used to multiply decay bounds inside the profile integral equation.

**Norm bound for a tensor product.** The matrix of two vector-coordinate products has norm at most the product of the vector norms. (`Breakdown.FarField.TensorWeightInternal.norm_tensorField_le`)

**Decay weights multiply for tensors.** The tensor product of fields with nonnegative weighted decay exponents has the sum of those exponents and the product of their decay constants. (`Breakdown.FarField.tensorWeight_holds`)

### Breakdown.CertTorus.TopStatements

This file connects weak-profile regularity and decay to a smooth periodic similarity profile and the torus breakdown conclusion of Corollary 7.2.

**Regular orbit from the integral equation.** A smooth orbit field satisfying the full profile integral equation is a regular orbit field. (`Breakdown.FarField.isRegularOrbitField_of_smooth`)

**Similarity profile from decay.** A regular orbit field with the stated decay bounds gives a periodic similarity profile. (`Breakdown.FarField.periodicLerayProfileExists_of_regular`)

**Similarity profile from an orbit.** The smooth-field, integral-equation and far-field-decay interfaces turn the existence of an energy-space orbit into a periodic similarity profile. (`Breakdown.FarField.periodicLerayProfileExists_of_orbit`)

**Upgrade a weak similarity profile.** The smooth-field, integral-equation and far-field-decay interfaces turn a weak periodic similarity profile into a smooth periodic similarity profile. (`Breakdown.FarField.periodicLerayProfileExists_of_weak_of_parts`)

**Torus breakdown from a weak profile.** The smooth-field, integral-equation and far-field-decay interfaces turn a weak periodic similarity profile into torus breakdown. (`Breakdown.FarField.breakdownOnTorus_of_weak_of_parts`)

### Breakdown.CertTorus.TruncTendsto

This file removes the finite upper limit in the profile integral by proving convergence of the truncated bilinear term.

**Bound the product of bounded fields.** Two field norm bounds A and B give tensor norm at most AB at every point. (`_private.Breakdown.CertTorus.TruncTendsto.0.Breakdown.FarField.norm_tensorField_le_mul`)

**Measurable similarity coordinates.** The time-space similarity change of variables is measurable. (`_private.Breakdown.CertTorus.TruncTendsto.0.Breakdown.FarField.measurable_similarityArg`)

**Continuous shifted velocity.** A jointly continuous velocity field remains spatially continuous after each fixed similarity shift. (`_private.Breakdown.CertTorus.TruncTendsto.0.Breakdown.FarField.continuous_similarityShift`)

**Measurable shifted tensor square.** The tensor square of a shifted jointly continuous velocity field is measurable. (`_private.Breakdown.CertTorus.TruncTendsto.0.Breakdown.FarField.measurable_tensorField_shift`)

**Integrable full time weight.** The weight (1 + τ)⁻¹τ⁻¹ᐟ² is integrable on the positive time axis. (`_private.Breakdown.CertTorus.TruncTendsto.0.Breakdown.FarField.integrableOn_inv_one_add_mul_rpow`)

**Convergence of truncated integrals.** The uniform convolution estimate, Leray-kernel bound and measurability make the truncated bilinear profile integrals of every continuous uniformly bounded field converge pointwise to the full profile integral as truncation time tends to infinity. (`Breakdown.FarField.truncTendsto_of_kernel`)

### Breakdown.CertTorus.TruncatedNewton

This file differentiates truncated Newton potentials and controls their gradients before identifying the pressure in Proposition 7.11.

**Smooth ball cutoff.** The ball cutoff is smooth. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.ballCutoff_contDiff`)

**Cutoff vanishes outside twice the radius.** At positive radius, the ball cutoff vanishes beyond twice that radius. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.ballCutoff_eq_zero`)

**Cutoff equals one on the inner ball.** At positive radius, the ball cutoff equals one on the closed inner ball. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.ballCutoff_eq_one`)

**Absolute bound for the cutoff.** The ball cutoff has absolute value at most one. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.abs_ballCutoff_le`)

**Compact support after cutting off.** Multiplying any scalar field by a positive-radius ball cutoff gives compact support. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.hasCompactSupport_cutoff_mul`)

**Regularized Newton kernel.** The regularized kernel is −1/(4π) divided by the square root of ‖w‖² + δ. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.smoothKernel`)

**Smooth regularized kernel.** A positive regularization parameter makes the Newton kernel smooth everywhere. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.smoothKernel_contDiff`)

**Derivative of the regularized kernel.** At positive regularization, the kernel derivative is the stated reciprocal-cubic factor times the inner product with w. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.hasFDerivAt_smoothKernel`)

**Dominate the regularized kernel.** Away from the origin, the regularized kernel has absolute value at most that of the Newton kernel. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.abs_smoothKernel_le`)

**Recover the Newton kernel.** Away from the origin, the regularized kernel tends to the Newton kernel as the positive regularization tends to zero. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.tendsto_smoothKernel`)

**Recover the Newton-gradient formula.** Away from the origin, the regularized directional gradient tends to the stated Newton-gradient expression. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.tendsto_smoothGrad`)

**Bound the regularized gradient.** The regularized directional gradient is bounded by (4π)⁻¹‖w‖⁻²‖v‖ at positive regularization. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.abs_smoothGrad_le`)

**Bound the Newton gradient.** The directional Newton-gradient expression is bounded by (4π)⁻¹‖w‖⁻²‖v‖. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.abs_gradKernel_le`)

**Support of a directional derivative.** A directional derivative of a compactly supported scalar function has compact support. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.hasCompactSupport_fderiv_dir`)

**Continuity of a directional derivative.** A directional derivative of a smooth scalar function is continuous. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.continuous_fderiv_dir`)

**Continuous regularized gradient.** At positive regularization, the translated regularized gradient is continuous in its integration variable. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.continuous_smoothGrad`)

**Integrate by parts with the smoothing.** For smooth compactly supported data and positive regularization, integration by parts moves the directional derivative onto the smoothed Newton kernel. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.integral_deriv_mul_smoothKernel`)

**Derivative of a Newton potential.** The derivative of the potential of smooth compactly supported data is the displayed integral against the directional Newton-gradient kernel. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.fderiv_potential_eq_integral`)

**Split the singular decay weight.** The inverse-square translated kernel times the fourth-power decay weight is bounded by the stated local-ball term plus a quadratic-decay remainder. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.weight_pointwise`)

**Integrable fourth-power decay.** The fourth-power reciprocal radial decay weight is integrable. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.integrable_decay_four`)

**Integrable local singular contribution.** The local-ball contribution in the split weight is integrable. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.integrable_ballPart`)

**Integrability of the full weight.** The translated inverse-square kernel times the fourth-power decay weight is integrable. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.integrable_weight`)

**Quadratic decay of the convolution.** One nonnegative constant bounds the singular weighted convolution by the quadratic radial decay weight. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.integral_weight_le`)

**Dominate the truncated gradient term.** A fourth-power source bound and a cutoff of absolute value at most one bound the gradient integrand by the stated singular weighted majorant. (`_private.Breakdown.CertTorus.TruncatedNewton.0.Breakdown.FarField.integrand_bound`)

**Truncated Newton estimate.** For a smooth scalar source with inverse fourth-power decay, gradients of its ball-truncated Newton potentials have a uniform inverse-square decay bound for cutoff radii at least one and converge componentwise to the full Newton gradient as the cutoff radius tends to infinity. (`Breakdown.FarField.truncatedNewton_holds`)

### Breakdown.CertTorus.VelocityOfSymbol

This file identifies the L⁶ velocity representative with the inverse Fourier reconstruction of a smooth energy-space state.

**Symmetry of an energy-space symbol.** The energy-space representative is conjugate-even and has zero longitudinal component almost everywhere. (`Breakdown.FarField.Internal.VelocityOfSymbol.symX_ae_sig`)

**Velocity symbol without the projection.** Almost everywhere, the velocity symbol is the symmetric symbol divided by 2π‖ξ‖. (`Breakdown.FarField.Internal.VelocityOfSymbol.velSymbol_ae`)

**Measurable velocity symbol.** The velocity symbol is almost everywhere strongly measurable. (`Breakdown.FarField.Internal.VelocityOfSymbol.aestronglyMeasurable_velSymbol`)

**Integrability from smoothness.** The Sobolev-to-Wiener interface makes the velocity symbol of a smooth state integrable. (`Breakdown.FarField.Internal.VelocityOfSymbol.integrable_velSymbol`)

**Even bounded Fourier multipliers.** A bounded measurable even real multiplier of an energy-space representative is represented by another energy-space state. (`Breakdown.FarField.Internal.VelocityOfSymbol.exists_radial_mul`)

**High-frequency cutoff set.** The nth high-frequency set contains frequencies of norm at least 1/(n + 1). (`Breakdown.FarField.Internal.VelocityOfSymbol.highFreq`)

**Measurable cutoff set.** Each high-frequency cutoff set is measurable. (`Breakdown.FarField.Internal.VelocityOfSymbol.measurableSet_highFreq`)

**Cutoff frequencies are nonzero.** Every frequency in the high-frequency set has strictly positive norm. (`Breakdown.FarField.Internal.VelocityOfSymbol.pos_of_mem_highFreq`)

**Reflection preserves the cutoff set.** A frequency and its negative belong to the high-frequency set together. (`Breakdown.FarField.Internal.VelocityOfSymbol.neg_mem_highFreq`)

**Every nonzero frequency is retained.** Every nonzero frequency lies in all sufficiently late high-frequency cutoff sets. (`Breakdown.FarField.Internal.VelocityOfSymbol.eventually_mem_highFreq`)

**Cutting off preserves evenness.** Cutting an even scalar function to the high-frequency set preserves its evenness. (`Breakdown.FarField.Internal.VelocityOfSymbol.indicator_neg_highFreq`)

**Bound the truncated inverse frequency.** The truncated reciprocal-frequency multiplier has absolute value at most n + 1. (`Breakdown.FarField.Internal.VelocityOfSymbol.abs_indicator_inv_le`)

**Convergence of cut-off states.** States with the stated high-frequency-cutoff representatives converge in X to the original state. (`Breakdown.FarField.Internal.VelocityOfSymbol.tendsto_cut`)

**Convergence of cut-off reconstructions.** For an integrable symbol, physical reconstructions of the high-frequency cutoffs converge pointwise to its full reconstruction. (`Breakdown.FarField.Internal.VelocityOfSymbol.physField_cut_tendsto`)

**Velocity equals Fourier reconstruction.** The Wiener interface identifies the velocity of a smooth state with its reconstructed velocity symbol almost everywhere. (`Breakdown.FarField.Internal.VelocityOfSymbol.velocity_ae_physField`)

**Velocity reconstruction from Wiener.** The homogeneous Sobolev-to-Wiener estimate identifies the velocity representative of every smooth energy-space state almost everywhere with the physical field reconstructed from its Fourier symbol. (`Breakdown.FarField.velocityOfSymbolOfWiener_holds`)

### Breakdown.CertTorus.WienerSolution

This file turns a weighted Fourier evolution into smooth physical velocity and pressure satisfying the ordinary Navier–Stokes equation.

**Weighted L¹ class from membership.** For weighted-L¹ data, the chosen class equals the class obtained from its membership proof. (`Breakdown.FarField.Internal.FourierSolution.toWeightL1_of_memLp`)

**Smooth map for symbol time derivatives.** The symbol time derivative is induced by a map smooth at every finite order from the stated pair of weighted L¹ spaces to the lower-weight space. (`Breakdown.FarField.Internal.FourierSolution.exists_timeDeriv_map`)

**Weighted integrability of time symbols.** A symbol with every weighted L¹ moment has a time-derivative symbol with every weighted L¹ moment. (`Breakdown.FarField.Internal.FourierSolution.memLp_timeDeriv`)

**Integrability of the Laplacian symbol.** An order-two weighted-L¹ symbol has an integrable Laplacian symbol. (`Breakdown.FarField.Internal.FourierSolution.integrable_lapSymbol`)

**Nonzero first complex basis vector.** The complex vector whose first coordinate is one is nonzero. (`Breakdown.FarField.Internal.FourierSolution.single_ne_zero`)

**Integrability of the pressure symbol.** A solenoidal symbol with every weighted L¹ moment has an integrable pressure symbol. (`Breakdown.FarField.Internal.FourierSolution.integrable_pressure`)

**Inverse transform of a scalar product.** Inverse Fourier transformation of a scalar function times a constant vector equals the inverse scalar transform times that vector. (`Breakdown.FarField.Internal.FourierSolution.fourierInv_smul_const`)

**Real part of the first coordinate.** The first-coordinate real-part map is the continuous real linear projection from a complex vector to that scalar component. (`Breakdown.FarField.Internal.FourierSolution.reFirst`)

**Recover a scalar through a vector.** Scalar physical reconstruction equals the first-coordinate real part of the displayed vector-valued inverse Fourier transform. (`Breakdown.FarField.Internal.FourierSolution.physScalar_eq_reFirst`)

**Smooth weighted-symbol evolution.** Every weighted-L¹ class curve is smooth to each finite order on the closed interval under the stated time-derivative and weighted-integrability hypotheses. (`Breakdown.FarField.Internal.FourierSolution.contDiffOn_weighted`)

**Smooth weighted-pressure evolution.** Under the solenoidal and weighted evolution hypotheses, the pressure placed in the first complex coordinate is smooth in each weighted L¹ space. (`Breakdown.FarField.Internal.FourierSolution.contDiffOn_pressureSingle`)

**Physical solution from Wiener evolution.** On a positive-length interval, a solenoidal symbol curve in every weighted Fourier L¹ space with the prescribed time derivative reconstructs smooth velocity and pressure satisfying the Navier–Stokes evolution equation at interior times and zero divergence throughout the interval. (`Breakdown.FarField.wienerSolution_holds`)

### Breakdown.CertTorus.WindowResidual

This file changes from a smooth physical-time window back to similarity coordinates and transfers the PDE residual.

**Recover the profile velocity by scaling.** Under the positive scale and logarithmic identity, the similarity velocity is r times the physical-window velocity at time 1 − r² and position ry. (`_private.Breakdown.CertTorus.WindowResidual.0.Breakdown.FarField.field_of_scale`)

**Recover the profile pressure by scaling.** Under the positive scale and logarithmic identity, the profile pressure is r² times the rescaled physical-window pressure. (`_private.Breakdown.CertTorus.WindowResidual.0.Breakdown.FarField.pressure_of_scale`)

**Membership in the physical window.** The stated logarithmic correspondence sends a similarity time in its open interval to a physical time 1 − r² in (a, b). (`_private.Breakdown.CertTorus.WindowResidual.0.Breakdown.FarField.window_mem`)

**Logarithm of the scale squared.** The logarithm of the squared exponential scale equals the negative similarity-time difference. (`_private.Breakdown.CertTorus.WindowResidual.0.Breakdown.FarField.log_scale_sq`)

**Derivative of the time scale.** The exponential scale exp(−(σ − s₀)/2) has derivative −1/2 times itself. (`_private.Breakdown.CertTorus.WindowResidual.0.Breakdown.FarField.scale_hasDerivAt`)

**Differentiate the rescaled window.** Under the local smoothness and physical time-derivative hypotheses, the similarity velocity has the stated product-and-chain-rule time derivative. (`_private.Breakdown.CertTorus.WindowResidual.0.Breakdown.FarField.window_hasDerivAt`)

**Transfer the window residual.** A smooth solenoidal physical solution with the stated smooth rescaled pressure on [a, b], where 0 ≤ a < b < 1, gives smooth orbit velocity and pressure with zero similarity residual and zero divergence on the corresponding open logarithmic time window. (`Breakdown.FarField.windowResidual_holds`)
<!-- /passage:front -->

