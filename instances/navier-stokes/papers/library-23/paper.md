
<!-- passage:front -->
# Library guide 23: Breakdown/FracCert

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) **23** [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.FracCert.ActiveEnclosure` to `Breakdown.FracCert.KernelDecay` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.FracCert.ActiveEnclosure

Bounds the active transformed held multipliers by testing the residual against certificate rows and controlling pin and nonlinear errors.

This belongs to the fractional analogue of the paper §7 certificate strategy; it supplies definitions, quantitative inverse bounds or the held-solution bridge, while its fractional conclusions are outside the ordinary-dissipation argument claimed in the paper.

Source: `lean/Breakdown/FracCert/ActiveEnclosure.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.ActiveEnclosureInternal`.

**L² fields pair integrably.** Proved result `pair_integrable`: If X,Y ∈ L²(ℝ³;ℝ³), then their pointwise inner product X·Y is integrable on ℝ³. Source: `Breakdown.FracCert.ActiveEnclosure:15`.

**L² energy equals norm squared.** Proved result `sq_integral_eq`: For X ∈ L²(ℝ³;ℝ³), the integral ∫|X(y)|² dy equals the square of its L² norm.

**Cauchy-Schwarz bounds integral pairings.** Proved result `abs_pair_le`: For square-integrable fields X and Y, |∫X·Y| ≤ (∫|X|²)¹ᐟ²(∫|Y|²)¹ᐟ². Source: `Breakdown.FracCert.ActiveEnclosure:28`.

**Cauchy-Schwarz bounds finite sums.** Proved result `sum_mul_le_sqrt`: For any two finite real families (fⱼ) and (gⱼ), ∑ⱼfⱼgⱼ ≤ (∑ⱼfⱼ²)¹ᐟ²(∑ⱼgⱼ²)¹ᐟ².

**Two products obey Cauchy-Schwarz.** Proved result `two_mul_le`: For real a,b,c,e, the two terms satisfy ab + ce ≤ √(a²+c²)√(b²+e²).

**Finite matrix energy gives L² columns.** Proved result `col_memLp`: If a measurable matrix field G has integrable squared Frobenius norm, each column Geᵢ is a square-integrable vector field on ℝ³. Source: `Breakdown.FracCert.ActiveEnclosure:50`.

**Matrix pairings obey Cauchy-Schwarz.** Proved result `entry_pair`: If G and χ are measurable matrix fields with finite squared Frobenius integrals, G:χ is integrable and |∫G:χ| ≤ (∫|G|²)¹ᐟ²(∫|χ|²)¹ᐟ².

**Second traces belong to L².** Proved result `trace_memLp`: For a solenoidal symmetry-class field v ∈ L⁶ with weak gradient and weak second derivatives in L², the trace of its weak Hessian, Δv, belongs to L².

**Inverse-radius decay is in L⁶.** Proved result `decay_six`: The sixth power of (1+|y|)⁻¹ is integrable over ℝ³, so this radial decay rate belongs to L⁶.

**Mixed powers admit a sum bound.** Proved result `pointwise_split`: For nonnegative real t and b, t⁴b² ≤ t⁶+b⁶.

**Decaying matrices send L⁶ fields to L².** Proved result `decay_apply_memLp`: If A is a continuous matrix field with |A(y)| ≤ C(1+|y|)⁻² and v ∈ L⁶ is measurable, then the vector field A(y)v(y) belongs to L²(ℝ³).

**Basis vectors reconstruct linear maps.** Proved result `apply_expand`: For a linear map A on ℝ³ and x = ∑ᵢxᵢeᵢ, one has Ax = ∑ᵢxᵢAeᵢ.

**Bounded vectors preserve L² bounds.** Proved result `bounded_apply_memLp`: Under the stated hypotheses, bounded vectors preserve matrix L² bounds.

**Certificate profiles have uniform decay.** Proved result `profile_bounds_of`: A valid fractional certificate supplies one constant C such that |Wₚ(y)| ≤ C(1+|y|)⁻¹ and |∇Wₚ(y)| ≤ C(1+|y|)⁻² for every parameter p in its box and every y ∈ ℝ³.

**Profile decay gives a global bound.** Proved result `profile_le`: If a profile satisfies |Wₚ(y)| ≤ C(1+|y|)⁻¹ everywhere, then |Wₚ(y)| ≤ |C| everywhere.

**Finite actuator sums belong to L².** Proved result `sum_smul_memLp`: Any finite linear combination ∑ᵢcᵢbᵢ of square-integrable actuator fields bᵢ is square-integrable.

**The local linear field belongs to L².** Proved result `local_memLp`: For a valid fractional certificate, a parameter in its box and an admissible linear state, the local linearized field with all actuator coefficients zero belongs to L².

**The certificate defect belongs to L².** Proved result `defect_memLp`: For a valid fractional certificate and every parameter in its box, the residual of the approximate profile, including its prescribed actuator forcing, belongs to L²(ℝ³).

**Difference squares have a sum bound.** Proved result `norm_sub_sq_le`: For vectors a,b ∈ ℝ³, |a−b|² ≤ 2|a|²+2|b|².

**Matrix difference energy has a sum bound.** Proved result `entrySq_sub_le`: For matrices A and B on ℝ³, their squared Frobenius distance satisfies |A−B|² ≤ 2(|A|²+|B|²).

**Weighted energy controls gradient energy.** Proved result `energy_facts`: For a valid certificate and an admissible field, E = ∫|Δu|²+∫w|∇u|² is nonnegative and satisfies w₀∫|∇u|² ≤ E, where w₀ is the certificate's lower weight bound.

**Pin errors obey the certificate gap.** Proved result `pin_bound`: If an admissible field has all exact pin pairings zero, its smooth-pin combination satisfies |∑ₗcₗ∫∇u:χₗ| ≤ |c| δₚᵢₙ‖∇u‖₂, where δₚᵢₙ is the valid certificate's pin approximation bound.

**Source namespace:** `Breakdown.SteadyCert`.

**Active multipliers satisfy the enclosure.** Proved result `activeEnclosure`: Under the stated assumptions, this establishes that for a held solution within the certified radius at a test-box parameter, each active coordinate of the transformed corrected multiplier differs from its slope times the parameter by at most the absolute slope times that coordinate radius.

### Breakdown.FracCert.AprioriBound

Turns certificate coercivity, fractional splitting estimates and finite row and pin errors into the quantitative inverse bound for a linear correction state.

This belongs to the fractional analogue of the paper §7 certificate strategy; it supplies definitions, quantitative inverse bounds or the held-solution bridge, while its fractional conclusions are outside the ordinary-dissipation argument claimed in the paper.

Source: `lean/Breakdown/FracCert/AprioriBound.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**L² fields pair integrably.** Proved result `int_inner_two`: For A,B ∈ L²(ℝ³;ℝ³), the scalar function A·B belongs to L¹(ℝ³).

**Cauchy-Schwarz bounds the L² pairing.** Proved result `pair_le`: For A,B ∈ L²(ℝ³;ℝ³), their integrated pairing satisfies ∫A·B ≤ ‖A‖₂‖B‖₂.

**Compact L² fields pair with local L².** Proved result `int_inner_loc`: If X is measurable and locally square-integrable, and e ∈ L² vanishes outside some ball, then X·e is integrable on ℝ³.

**Integral pairings preserve sums.** Proved result `pair_add`: If A·e and B·e are integrable, then ∫(A+B)·e = ∫A·e+∫B·e.

**Integral pairings preserve differences.** Proved result `pair_sub`: If A·e and B·e are integrable, then ∫(A−B)·e = ∫A·e−∫B·e.

**Sum pairings remain integrable.** Proved result `int_add`: Integrability of A·e and B·e implies integrability of (A+B)·e.

**Difference pairings remain integrable.** Proved result `int_sub`: Integrability of A·e and B·e implies integrability of (A−B)·e.

**Weighted norms obey a triangle bound.** Proved result `wsum_tri`: Under the stated hypotheses, weighted finite norms obey a triangle bound.

**Weighted norms ignore negation.** Proved result `wsum_neg`: For finite real families τ and u, √(∑ᵢτᵢ(−uᵢ)²) = √(∑ᵢτᵢuᵢ²); this identity needs no sign restriction on the weights.

**Two-coordinate errors have a norm bound.** Proved result `plane_tri`: For Y ≥ 0 and real r,s,a,b, (r+aY)²+(s+bY)² ≤ (√(r²+s²)+Y√(a²+b²))².

**A quadratic inequality gives a bound.** Proved result `quad_solve`: Under the stated hypotheses, a quadratic inequality gives a root bound.

**Mixed powers admit a sum bound.** Proved result `sq_mul_le`: For nonnegative u and w, the mixed term satisfies u²w² ≤ u³+w⁶.

**Matrix energy controls vector action.** Proved result `op_entry`: For any matrix L and vector x in ℝ³, |Lx|² ≤ |L|²|x|², with |L| the Frobenius norm.

**The second trace is continuous.** Proved result `trace_cont`: The map sending a vector-valued bilinear form H to ∑ⱼH(eⱼ,eⱼ) is continuous.

**Second traces belong to L².** Proved result `trace_two`: For an admissible second-order field, tracing its square-integrable weak Hessian gives a square-integrable Laplacian.

**Profile cross products belong to L².** Proved result `sym_two`: For a valid certificate, p in its parameter box and an admissible field v, the symmetrized cross-convection ½((Wₚ·∇)v+(v·∇)Wₚ) belongs to L².

**The local bordered field belongs to L².** Proved result `local_two`: For a valid certificate and an admissible linear state at p in its parameter box, adding any finite actuator combination to the local linearized field preserves L² integrability.

**Row errors obey a three-term bound.** Proved result `rows_tri`: If the row weights are nonnegative, X=A−B−C and each field has integrable pairings with every row, the weighted Euclidean norm of X's row pairings is at most the sum of the corresponding norms for A, B and C.

**Coefficient norms obey a triangle bound.** Proved result `vec_tri`: For finite coefficient vectors u and w, |u+w| ≤ |u|+|w| in the Euclidean norm.

**The zero field is a gradient.** Proved result `grad_zero`: The zero vector field is the weak gradient of the zero scalar potential, with both fields locally square-integrable.

**Negation preserves weak gradients.** Proved result `grad_neg`: If Q is the weak gradient of a locally square-integrable potential and Q is locally square-integrable, then −Q has the same properties with the negative potential.

**Weak gradients have local L² regularity.** Proved result `grad_parts`: A weak gradient field in the pressure class is measurable and has finite squared norm on every compact subset of ℝ³.

**Coercivity absorbs row and pin errors.** Proved result `chain`: Under the stated hypotheses, coercivity combines with row and pin errors.

**The certificate gives the inverse bound.** Proved result `aprioriBound`: Under the stated assumptions, this establishes that a valid fractional certificate bounds a linear correction state and its multipliers by the certificate function of its projected residual norm, gradient-insensitive row residuals and pin size.

### Breakdown.FracCert.BallShift

Proves the local translation estimate behind compactness by mollifying weakly differentiable fields and bounding their translated L² differences.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/BallShift.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.BallShiftInternal`.

**Squared averages are bounded by averages.** Proved result `average_sq_le`: For a nonnegative integrable density p with ∫p=1, |∫p(t)f(t)dt|² ≤ ∫p(t)|f(t)|²dt, allowing the right-hand side to be infinite.

**Finite sums pass below lower integrals.** Proved result `sum_three_le`: For any three nonnegative functions on ℝ³, the sum of their lower integrals is bounded above by the lower integral of their sum.

**Mollified derivatives recover weak ones.** Proved result `deriv_eq`: Let G be the weak gradient of u, with 1_Bᵣ₊₂u locally integrable, and let ρ be smooth with compact support in B₁. For v=ρ*(1_Bᵣ₊₂u) and |x|≤R+1, ∂ⱼv(x)=∫ρ(x−t)G(t)eⱼdt.

**Mollified gradient energy is bounded.** Proved result `grad_sq_le`: Let G be the weak gradient of u, with 1_Bᵣ₊₂u locally integrable, and let ρ≥0 be smooth, supported in B₁ and have integral one. Then v=ρ*(1_Bᵣ₊₂u) satisfies |∇v(x)|²≤∫ρ(x−t)|G(t)|²dt for |x|≤R+1, allowing an infinite right side.

**Translated mollifiers have energy bounds.** Proved result `smooth_ball_le`: Let G be the weak gradient of u, let 1_B(R+2)u be locally integrable, and let ρ≥0 be smooth, supported in B₁ and have integral one. For v=ρ*(1_B(R+2)u) and |h|≤1, the nonnegative integrals satisfy ∫ over B̄R |v(y+h)−v(y)|²dy≤|h|²∫max(E,0), possibly with infinite right side, whenever measurable E equals |G|² almost everywhere.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak gradients bound local translations.** Proved result `ballShift`: Under the stated assumptions, this establishes that for a field with the stated local L² regularity and square-integrable weak gradient, the integral over the radius-R ball of the squared difference between the field and its translate is at most the squared translation length times the global gradient energy whenever the translation has norm at most one.

### Breakdown.FracCert.CertTestBox

Extracts containment of the active and stiff test region inside the certificate parameter box.

This belongs to the fractional analogue of the paper §7 certificate strategy; it supplies definitions, quantitative inverse bounds or the held-solution bridge, while its fractional conclusions are outside the ordinary-dissipation argument claimed in the paper.

Source: `lean/Breakdown/FracCert/CertTestBox.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**The test box lies in the parameter box.** Proved result `testBoxSubset`: Under the stated assumptions, this establishes that a valid fractional certificate places its test box inside its parameter box.

### Breakdown.FracCert.CertificateWeakProfile

Connects a zero of the held multiplier map to a nontrivial weak fractional rotating profile, conditional on the two bridge interfaces.

This belongs to the fractional analogue of the paper §7 certificate strategy; it supplies definitions, quantitative inverse bounds or the held-solution bridge, while its fractional conclusions are outside the ordinary-dissipation argument claimed in the paper.

Source: `lean/Breakdown/FracCert/CertificateWeakProfile.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Cancelled held states give weak profiles.** Proved result `certificateWeakProfile`: Assuming the held-multiplier zero theorem and the implication from cancelled held solutions to weak profiles, the fractional certificate hypothesis yields a nontrivial weak rotating fractional profile.

### Breakdown.FracCert.DecayBase

Obtains the first spatial decay rate for a fractional profile by splitting its tensor square into a small tail and a compact core, then improving a subcritical weight.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayBase.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.FarFieldAddInternal`.

**The projected heat kernel is measurable.** Proved result `kernel_measurable`: For every α and every component, the projected fractional heat-divergence kernel is measurable jointly in time and position.

**The projected heat kernel is integrable.** Proved result `kernel_integrable`: Assuming the projected-kernel decay estimate, each component of the heat-divergence kernel is integrable in space whenever α>0 and t>0.

**Bounded tensors pair with the kernel.** Proved result `comp_integrable`: Assuming the projected-kernel decay estimate, a bounded continuous tensor F can be paired integrably with each translated real kernel component for α>0 and t>0.

**Heat-divergence convolution is additive.** Proved result `heatDivConv_add`: Assuming the kernel decay estimate, convolution by the projected heat-divergence kernel preserves sums of bounded continuous tensors for α>0 and t>0.

**The total projected kernel mass.** Definition `kernelMass`: This defines the total mass of the time-one projected heat-divergence kernel by summing the L¹ norms of all twenty-seven scalar components.

**Kernel mass is nonnegative.** Proved result `kernelMass_nonneg`: The sum over all components of the spatial integrals of the time-one kernel norms is nonnegative for every α. Source: `Breakdown.FracCert.DecayBase:54`.

**Three coordinate bounds control the norm.** Proved result `norm_le_three`: If each of the three coordinates of v has absolute value at most c, then |v| ≤ 3c.

**Kernel mass bounds heat divergence.** Proved result `heatDivConv_norm_le`: Assuming the kernel decay estimate, |F(y)| ≤ B implies |e^(−t(−Δ)^α)P div F(x)| ≤ 3B t^(−1/(2α))Mα for α,t>0, where Mα is the total componentwise L¹ mass of the time-one kernel. Source: `Breakdown.FracCert.DecayBase:72`.

**Source namespace:** `Breakdown.FracCert`.

**The far-field operator is additive.** Proposition `FarFieldAddStatement`: This proposition requires that for 1<α<5/4, the far-field operator preserves sums of bounded continuous tensor fields.

**Source namespace:** `Breakdown.FracCert.FarFieldAddInternal`.

**Negative exponentials are below one.** Proved result `exp_neg_lt_one`: For every τ>0, e^(−τ)<1. Source: `Breakdown.FracCert.DecayBase:122`.

**The far-field integrand is additive.** Proved result `integrand_add`: Assuming the kernel decay estimate, the rotated and dilated heat-divergence integrand at time τ>0 preserves sums of bounded continuous tensors when α>0.

**Coordinate embeddings are measurable.** Proved result `single_measurable`: For each coordinate direction eᵢ in ℝ³, the map r↦reᵢ is measurable. Source: `Breakdown.FracCert.DecayBase:139`.

**Rotations preserve measurability.** Proved result `meas_rot`: If an angle f(τ) and a vector g(τ) depend measurably on τ, then rotating g(τ) about the axis by f(τ) gives a measurable vector-valued function.

**Heat convolutions vary measurably.** Proved result `meas_heat`: For a continuous tensor F, evaluating its heat-divergence convolution at measurable time t(τ) and position x(τ) gives a measurable function of τ. Source: `Breakdown.FracCert.DecayBase:160`.

**The far-field integrand is measurable.** Proved result `integrand_measurable`: For a continuous tensor F, fixed α, rotation rate a and point y, the rotated, dilated heat-divergence integrand with heat time 1−e^(−τ) is measurable in τ.

**Small heat times have a lower bound.** Proved result `one_sub_exp_ge`: Under the stated hypotheses, small heat times have a linear lower bound. Source: `Breakdown.FracCert.DecayBase:191`.

**The time singularity is integrable.** Proved result `weight_integrable`: For α>1, the function e^(−τ(1−1/(2α)))(1−e^(−τ))^(−1/(2α)) is integrable on (0,∞). Source: `Breakdown.FracCert.DecayBase:197`.

**The far-field integrand is integrable.** Proved result `integrand_integrable`: Assuming the kernel decay estimate and α>1, the far-field integral's rotated, dilated heat-divergence integrand is integrable over τ>0 at each point when F is bounded and continuous.

**Source namespace:** `Breakdown.FracCert`.

**Kernel decay gives far-field additivity.** Proved result `farFieldAdd_of`: Under the stated assumptions, this establishes that for 1<α<5/4, the far-field operator preserves sums of bounded continuous tensor fields.

**Source namespace:** `Breakdown.FracCert.DecayBaseInternal`.

**The tensor product of two fields.** Definition `outer`: This defines the tensor product of two vector fields by the entries uⱼ(y)vₖ(y).

**Tensor norms obey a product bound.** Proved result `norm_outer_le`: For vector fields u and v, the pointwise tensor product satisfies |u(y)⊗v(y)| ≤ |u(y)||v(y)| in the tensor norm used here.

**Tensor products preserve continuity.** Proved result `continuous_outer`: If u and v are continuous vector fields, y↦u(y)⊗v(y) is continuous.

**Tensor products distribute on the right.** Proved result `outer_add_right`: The pointwise tensor identity u⊗(v+w)=u⊗v+u⊗w holds for arbitrary vector fields.

**Tensor products distribute on the left.** Proved result `outer_add_left`: The pointwise tensor identity (u+v)⊗w=u⊗w+v⊗w holds for arbitrary vector fields.

**All moments give bounded continuity.** Proved result `field_facts`: Under the stated hypotheses, all moments give a bounded continuous field.

**The physical field vanishes at infinity.** Proved result `field_small`: The physical field associated with a frequency-space profile tends uniformly to zero as |y|→∞: for every ε>0 it has norm at most ε outside some ball.

**The far field inherits a minimum weight.** Proved result `farField_zero_order`: Assuming the far-field derivative estimate, 1<α<5/4, 0≤β<3 and β≠2α−1, a continuous tensor bounded by A(1+|y|)^(−β) yields a continuous far-field output bounded by 2CA(1+|y|)^(−min(β,2α−1)), for a constant independent of F and A.

**A small tail gives subcritical decay.** Proved result `decay_first`: Assuming the far-field bound and additivity, a bounded continuous fixed point V of the quadratic far-field map that tends to zero at infinity satisfies |V(y)| ≤ G(1+|y|)^(−β) for each 0≤β< min(3,2α−1), when 1<α<5/4.

**Subcritical decay gives the profile rate.** Proved result `decay_second`: Assuming the far-field estimate and 1<α<5/4, a continuous fixed point already decaying at exponent ¾(2α−1) improves to |V(y)| ≤ C(1+|y|)^(−(2α−1)).

**Source namespace:** `Breakdown.FracCert`.

**Weak profiles have the base decay rate.** Proved result `profileDecayBase_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a weak rotating profile with all Fourier moments has velocity bounded by C(1+‖y‖)^(−(2α−1)).

### Breakdown.FracCert.DecayFarField

Integrates the rescaled projected heat operator in time, proving differentiability and the minimum of the input and self-similar spatial decay exponents.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayFarField.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert`.

**Heat derivatives have uniform regularity.** Proposition `HeatDivRegularStatement`: This proposition requires that for 1<α<5/4 and 0≤β<3, a Cʲ tensor with bounded jth derivative and a β-weighted value bound has Cʲ heat-divergence convolutions, jointly continuous derivatives through order j and bounds Ct^(−1/(2α))(A+B) for 0< t≤1.

**Source namespace:** `Breakdown.FracCert.DecayFarField.Internal`.

**The rotating and scaled heat integrand.** Definition `integrand`: This defines the far-field time integrand by rotating and self-similarly scaling the heat-divergence convolution at time 1−exp(−τ).

**Dominated integrals preserve derivatives.** Proved result `integral_contDiff`: If Φ(τ,·) is Cʲ for every τ>0, its spatial derivatives of orders 0 through j are measurable in τ, and all are bounded uniformly in y by one integrable function of τ, then ∫₀∞Φ(τ,y)dτ is Cʲ. Its jth derivative is the integral of the jth spatial derivatives.

**The integrand retains derivatives.** Proved result `integrand_contDiff`: Under the stated hypotheses, the time integrand retains spatial derivatives.

**Scaling bounds integrand derivatives.** Proved result `integrand_norm_le`: If H is the Cᵏ heat-divergence convolution at time 1−e^(−τ) and Φτ is its rotated, dilated far-field integrand, then ‖DᵏΦτ(y)‖≤e^(−τ(1−1/(2α)))e^(−kτ/(2α))‖DᵏH(e^(−τ/(2α))Rₐτ⁻¹y)‖.

**The transformed heat time is positive.** Proved result `t_pos`: For τ>0, the transformed heat time 1−e^(−τ) is strictly positive. Source: `Breakdown.FracCert.DecayFarField:148`.

**Integrable majorants give integrability.** Proved result `integrableOn_of_abs_le`: Under the stated hypotheses, an integrable majorant gives integrability.

**Heat-time powers are continuous.** Proved result `tpow_continuousOn`: For any real g, τ↦(1−e^(−τ))^(−g) is continuous on (0,∞).

**Near-time singularities have bounds.** Proved result `tpow_le_near`: Under the stated hypotheses, the near-time singularity has a power bound.

**Large times bound the heat-time factor.** Proved result `tpow_le_far`: For g≥0 and τ≥1, (1−e^(−τ))^(−g) ≤ (1−e^(−1))^(−g).

**Heat-time powers are nonnegative.** Proved result `tpow_nonneg`: For any real g and τ>0, (1−e^(−τ))^(−g) is nonnegative.

**Damped time singularities are integrable.** Proved result `weight_integrable`: If 0≤g<1 and c>0, the damped singular weight e^(−cτ)(1−e^(−τ))^(−g) is integrable over τ>0.

**The weighted time kernel is continuous.** Proved result `base_cont`: For real g,s,b and y≥0, the function e^(−gsτ)(1−e^(−τ))^(−g)(1+e^(−gτ)y)^(−b) is continuous on τ>0.

**The spatial decay factor is at most one.** Proved result `upow_le_one`: If b,y≥0, then (1+e^(−gτ)y)^(−b) ≤ 1 for all real g and τ.

**Spatial decay only reduces the integrand.** Proved result `base_le`: For b,y≥0 and τ>0, multiplying e^(−gsτ)(1−e^(−τ))^(−g) by (1+e^(−gτ)y)^(−b) can only decrease it.

**The weighted time kernel is integrable.** Proved result `base_integrable`: If 0< g<1, s>0 and b,y≥0, the weight e^(−gsτ)(1−e^(−τ))^(−g)(1+e^(−gτ)y)^(−b) is integrable on (0,∞).

**The translated scalar decay profile.** Definition `shape`: This defines the scalar profile exp(−gsx)(1+exp(−gx))^(−b) used after a logarithmic shift in the time integral.

**The scalar decay profile is nonnegative.** Proved result `shape_nonneg`: The scalar comparison function e^(−gsx)(1+e^(−gx))^(−b) is nonnegative for all real parameters and x.

**The scalar decay profile is integrable.** Proved result `shape_integrable`: For g>0 and 0< s< b, x↦e^(−gsx)(1+e^(−gx))^(−b) is integrable over the whole real line.

**Logarithmic shifts extract decay.** Proved result `shape_identity`: Under the stated hypotheses, a logarithmic shift extracts spatial decay.

**Time integration gives a minimum weight.** Proved result `scalar_bound`: If 0< g<1, s>0, b≥0 and b≠s, there is a uniform K bounding (1+y)^min(b,s) times ∫₀∞e^(−gsτ)(1−e^(−τ))^(−g)(1+e^(−gτ)y)^(−b)dτ for every y≥0; each integral is finite.

**Output composition preserves continuity.** Proved result `cont_left`: If a linear output map and a k-linear map both vary continuously on a parameter set, their composition on the output also varies continuously there.

**Input composition preserves continuity.** Proved result `cont_right`: If a linear input map and a k-linear map both vary continuously on a parameter set, applying that linear map to every input preserves continuity in the parameter.

**Rotation operators vary continuously.** Proved result `rot_clm_cont`: For a fixed angular speed a, the rotation Rₐτ depends continuously on τ in operator norm.

**Inverse rotations vary continuously.** Proved result `rot_symm_clm_cont`: For a fixed angular speed a, the inverse rotation Rₐτ⁻¹ depends continuously on τ in operator norm.

**Integrand derivatives follow scaling.** Proved result `integrand_iteratedFDeriv`: For a Cᵏ heat-divergence convolution, the kth derivative of its rotated, dilated integrand is obtained by rotating the output and applying e^(−τ/(2α))Rₐτ⁻¹ to every input, with output factor e^(−τ(1−1/(2α))).

**Integrand derivatives are measurable.** Proved result `integrand_aesm`: If the heat-divergence convolution is Cʲ in space and its derivatives through order j are jointly continuous for positive time, every corresponding spatial derivative of the far-field integrand is measurable in τ>0 at each fixed y.

**Source namespace:** `Breakdown.FracCert`.

**Heat bounds give far-field decay.** Proved result `farFieldBound_of`: Under the stated assumptions, this establishes that under the stated fractional and tensor-decay assumptions with b≠2α−1+j, the far-field operator is Cʲ and its jth derivative decays with weight exponent min(b,2α−1+j).

### Breakdown.FracCert.DecayFixedPoint

Identifies a weak fractional profile with the far-field integral by matching solenoidal and gradient frequency tests, then removing annular restrictions.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayFixedPoint.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayFixedPointInternal`.

**All moments give a continuous profile.** Proved result `profileField_continuous`: If a frequency-space profile has finite homogeneous Sobolev moments of every positive integer order, its physical representative is continuous on ℝ³. Source: `Breakdown.FracCert.DecayFixedPoint:20`.

**All moments give a bounded profile.** Proved result `profileField_bounded`: Finite homogeneous Sobolev moments of every positive integer order give a constant C≥0 bounding the physical profile at every point of ℝ³. Source: `Breakdown.FracCert.DecayFixedPoint:26`.

**Tensor squares preserve continuity.** Proved result `tensorSq_continuous`: If V is continuous, its tensor square y↦V(y)⊗V(y) is continuous. Source: `Breakdown.FracCert.DecayFixedPoint:36`.

**Tensor squares have a squared bound.** Proved result `tensorSq_norm_le`: If |V(y)|≤C everywhere with C≥0, then |V(y)⊗V(y)|≤C² everywhere. Source: `Breakdown.FracCert.DecayFixedPoint:42`.

**The profile far field is continuous.** Proved result `farField_continuous`: Assuming the far-field bound and 1<α<5/4, applying the far-field operator to the tensor square of a profile with all positive integer Sobolev moments gives a continuous vector field.

**Weighted L² pairs with compact symbols.** Proved result `pairing_integrable`: Under the stated hypotheses, weighted L² fields pair with compact symbols.

**Two test classes determine annuli.** Proved result `annulus_of_parts`: Under the stated hypotheses, solenoidal and gradient tests determine annuli.

**Source namespace:** `Breakdown.FracCert`.

**Annular tests identify the fixed point.** Proved result `profileFixedPoint_of_annulus`: Under the stated assumptions, this establishes that for 1<α<5/4, a weak rotating profile with all Fourier moments is pointwise the far-field operator applied to its velocity tensor square.

**Annular pairings agree.** Proved result `fixedPointAnnulus_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a weak rotating profile with all moments has zero difference from its far field in pairing against every real-symmetric smooth frequency test compactly supported away from zero.

**The profile is a far-field fixed point.** Proved result `profileFixedPoint_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a weak rotating profile with all Fourier moments is pointwise the far-field operator applied to its velocity tensor square.

### Breakdown.FracCert.DecayFixedPointGradient

Shows the physical field of an energy-space element annihilates frequency-localized gradient tests by Fourier orthogonality.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayFixedPointGradient.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayGradientInternal`.

**Fourier inversion exchanges pairings.** Proved result `pair_scalar`: Under the stated hypotheses, inverse Fourier transforms exchange pairings.

**L¹ symbols have continuous inverses.** Proved result `continuous_inverseTransform_of`: Under the stated hypotheses, integrable symbols have continuous inverses.

**Symbol L¹ mass bounds inverse transforms.** Proved result `norm_inverseTransform_le_of`: At every x, the absolute value of the inverse Fourier transform of a scalar symbol a is at most ∫|a(ξ)|dξ.

**Source namespace:** `Breakdown.FracCert`.

**Profiles annihilate gradient tests.** Proved result `profileGradientFree`: Under the stated assumptions, this establishes that the physical profile of an energy-space element with all moments annihilates every real-symmetric smooth annular frequency test whose value is parallel to its frequency.

### Breakdown.FracCert.DecayFixedPointParts

States the weighted integrability and test-pairing contracts used to convert the weak profile identity into a pointwise far-field fixed point.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayFixedPointParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert`.

**The far field has weighted L² size.** Proposition `FarFieldWeightedStatement`: This proposition requires that for 1<α<5/4, the far-field operator applied to the tensor square of a profile with all moments belongs to L² after multiplication by (1+‖y‖)⁻¹.

**Annular tests kill fixed-point errors.** Proposition `FixedPointAnnulusStatement`: This proposition requires that for 1<α<5/4, a weak rotating profile with all moments has zero difference from its far field in pairing against every real-symmetric smooth frequency test compactly supported away from zero.

**Weak profiles have the mild pairing.** Proposition `ProfileMildFormStatement`: This proposition requires that for 1<α<5/4, a weak rotating profile with all moments pairs against each nice test as the negative positive-time integral of its trilinear pairing with the heat-evolved similarity-adjoint test.

**Far-field pairings give the mild form.** Proposition `FarFieldPairingStatement`: This proposition requires that for 1<α<5/4, the far field of a profile tensor square with all moments pairs against each nice test as the negative positive-time integral of its trilinear pairing with the heat-evolved similarity-adjoint test.

**Profiles annihilate gradient tests.** Proposition `ProfileGradientFreeStatement`: This proposition requires that the physical profile of an energy-space element with all moments annihilates every real-symmetric smooth annular frequency test whose value is parallel to its frequency.

**Far fields annihilate gradient tests.** Proposition `FarFieldGradientFreeStatement`: This proposition requires that for 1<α<5/4, the far field of a profile tensor square with all moments annihilates real-symmetric smooth annular frequency tests parallel to their frequencies.

### Breakdown.FracCert.DecayFixedPointWeight

Reconstructs an energy-space velocity gradient from its coordinate partials and applies the inverse-square estimate to obtain weighted velocity integrability.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayFixedPointWeight.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayWeightInternal`.

**The gradient assembled from partials.** Definition `gradOf`: This assembles the velocity gradient from its three energy-space coordinate partial fields as a continuous linear map at each point.

**Gradient columns are the partial fields.** Proved result `gradOf_apply`: Applying the assembled gradient to the jth coordinate vector gives the jth energy-space partial field at that point.

**The assembled gradient is measurable.** Proved result `gradOf_aesm`: For a frequency-space profile U, assembling the three L² weak partial derivatives as the columns of a matrix field produces a measurable field.

**The assembled gradient has finite energy.** Proved result `gradOf_entrySq`: The matrix assembled from the three weak partial derivatives of a frequency-space profile has integrable squared Frobenius norm.

**The assembled gradient is a weak one.** Proved result `gradOf_weak`: The matrix whose columns are the three weak partial derivatives of U is the distributional gradient of its associated L⁶ velocity.

**Source namespace:** `Breakdown.FracCert`.

**Energy velocities admit radial weighting.** Proved result `profileInverseWeight`: Under the stated assumptions, this establishes that the physical velocity of an energy-space element with all moments belongs to L² after multiplication by (1+‖y‖)⁻¹.

### Breakdown.FracCert.DecayHeatDiv

Proves weighted derivative bounds for projected heat-divergence convolutions by separating a compact kernel core from a differentiated far kernel.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayHeatDiv.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.DecayHeatDiv`.

**Compact kernels transfer derivatives.** Proved result `near_deriv`: If φ is continuous with compact support and G is Cʲ, then φ*G is Cʲ and Dʲ(φ*G)(x)=∫φ(z)DʲG(x−z)dz.

**Nearby inverse-fourth weights compare.** Proved result `shift16`: Under the stated hypotheses, nearby radii compare inverse-fourth weights.

**Far convolutions admit differentiation.** Proved result `far_deriv`: Under the stated hypotheses, far kernels differentiate under convolution.

**Exterior cutoffs rescale from radius one.** Proved result `cutoff_scale`: For R>0, the exterior cutoff satisfies 1−χᵣ(y)=1−χ₁(y/R).

**Exterior cutoffs have derivative bounds.** Proved result `cutoff_deriv`: Under the stated hypotheses, exterior cutoff derivatives obey power bounds.

**Cutoff kernels have derivative bounds.** Proved result `far_kernel`: Under the stated hypotheses, cutoff kernels have far derivative bounds.

**Exterior derivatives decay integrably.** Proved result `far_kernel_qual`: Under the stated hypotheses, exterior kernel derivatives decay integrably.

**Spatial scaling cancels inverse powers.** Proved result `scale_pow`: For s>0, r≥0 and any real p, s^(−p)(s⁻¹r)^(−p)=r^(−p).

**Quotient powers separate their scales.** Proved result `div_pow_neg`: For s,a>0 and any real p, (s/a)^(−p)=aᵖs^(−p).

**Dilation gives the cubic Jacobian.** Proved result `scale_int`: For s>0 and a scalar function F on ℝ³, the dilation formula is ∫F(w/s)dw=s³∫F(w)dw.

**Positive dilation scales vector norms.** Proved result `norm_inv_smul`: For s>0 and y∈ℝ³, |s⁻¹y|=s⁻¹|y|.

**Far convolution tails have decay bounds.** Proved result `far_integral`: Under the stated hypotheses, far convolution tails have weighted bounds.

**Convolutions split into near and far.** Proved result `split_eq`: Under the stated hypotheses, convolutions split into near and far terms.

**The weight cancels kernel decay.** Proved result `weight_alg`: Under the stated hypotheses, the permitted weight cancels kernel decay.

**Weighted derivatives control convolution.** Proved result `conv_core`: For 0≤β<3 and 0≤b≤β+1+j, let k be smooth and integrable with ∫|k|≤L, bounds |Dⁿk(y)|≤D|y|^(−4−n) for y≠0 and n≤j, and analogous bounds at every higher order. If f is Cʲ with (1+|y|)^β|f|≤B and (1+|y|)^b|Dʲf|≤A, then k*f is Cʲ and (1+|x|)^b|Dʲ(k*f)|≤C(LA+DB), with C≥0 depending only on β,b,j.

**The coordinate embedding as a linear map.** Definition `unitMap`: This defines the continuous linear map sending a scalar to that scalar times the ith coordinate vector.

**A single heat-divergence component.** Definition `comp`: This defines one scalar component integral pairing the real projected heat-divergence kernel with the corresponding tensor entry.

**Heat divergence sums its components.** Proved result `heatDivConv_eq`: The projected heat-divergence convolution is the sum of its scalar component convolutions, inserted into the three coordinate directions.

**Source namespace:** `Breakdown.FracCert`.

**Kernel bounds give weighted heat bounds.** Proved result `heatDivBound_of`: Under the stated assumptions, this establishes that for 1<α<5/4, 0≤β<3 and 0≤b≤β+1+j, weighted bounds A and B on a tensor and its jth derivative imply a weighted jth heat-divergence bound Ct^(−1/(2α))(A+B) for 0< t≤1.

### Breakdown.FracCert.DecayNonzero

Transfers nonzero energy-space data to a pointwise nonzero physical profile using integrability of its Fourier symbol.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayNonzero.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert`.

**Nonzero energy gives a nonzero profile.** Proved result `profileNonzero_of`: Under the stated assumptions, this establishes that a nonzero energy-space element with all Fourier moments has a physical profile that is nonzero at some point.

### Breakdown.FracCert.DecayPower

Applies the homogeneous Fourier multiplier estimate to the fractional Laplacian, obtaining smoothness and the stronger spatial decay of the power term.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPower.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayPowerInternal`.

**Inversion commutes with coordinates.** Proved result `inverseTransform_coord`: Under the stated hypotheses, inverse transforms commute with coordinates.

**Conjugate symmetry gives a real inverse.** Proved result `inverseTransform_real`: If a scalar symbol satisfies p(−ξ)=overline{p(ξ)}, its inverse Fourier transform is real-valued at every point.

**L¹ symbols give inverse transforms.** Proved result `transform_of`: Under the stated hypotheses, integrable symbols give inverse transforms.

**Weighted bounds give decay bounds.** Proved result `le_of_weighted`: For r≥0, the weighted inequality (1+r)^e a≤C implies a≤C(1+r)^(−e).

**Opposite weights cancel.** Proved result `weight_cancel`: For r≥0 and any real e, the two powers satisfy (1+r)^e(1+r)^(−e)=1.

**The power multiplier has cubic growth.** Proved result `power_le`: Under the stated hypotheses, the fractional multiplier has cubic growth.

**The power symbol is homogeneous.** Proved result `homogeneous_power`: The fractional-power multiplier (2π|ξ|)^(2α) is smooth away from zero and homogeneous of degree 2α under positive dilation.

**Source namespace:** `Breakdown.FracCert`.

**Fractional powers have stronger decay.** Proved result `powerDecay_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a weak rotating profile with all moments and profile decay has a smooth fractional power whose jth derivative is bounded by C(1+‖y‖)^(−(4α−1+j)).

### Breakdown.FracCert.DecayPressure

Identifies the physical pressure with a decaying Fourier pressure model up to a harmonic function with vanishing gradient, obtaining decay of every pressure derivative.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPressure.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayPressure`.

**Derivatives pair with the gradient.** Proved result `fderiv_apply_eq_inner`: Under the stated hypotheses, derivatives pair with the scalar gradient.

**Gradient norm bounds derivative norm.** Proved result `norm_fderiv_le_grad`: For a scalar function ψ, the operator norm of its derivative at y is bounded by |∇ψ(y)|.

**Axial turns do not increase norms.** Proved result `norm_turn_le`: The axial rotation generator J(y₁,y₂,y₃)=(−y₂,y₁,0) satisfies |Jy|≤|y|.

**Profile decay powers compare.** Proved result `weight_facts`: For α>1 and r≥0, r(1+r)^(−2α), (1+r)^(−2α) and (1+r)^(−(4α−1)) are each bounded by (1+r)^(−(2α−1)); this last weight lies between zero and one.

**The equation bounds pressure gradients.** Proved result `grad_bound`: Under the stated hypotheses, the equation bounds the pressure gradient.

**Source namespace:** `Breakdown.FracCert`.

**A decaying model gives pressure decay.** Proved result `pressureDecay_of_parts`: Under the stated assumptions, this establishes that for 1<α<5/4, a smooth pressure solving the profile equation for a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

**Solenoidal powers close pressure decay.** Proved result `pressureDecay_of_model`: Under the stated assumptions, this establishes that for 1<α<5/4, a smooth pressure solving the profile equation for a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

**The pressure model gives pressure decay.** Proved result `pressureDecay_of_pressureModel`: Under the stated assumptions, this establishes that for 1<α<5/4, a smooth pressure solving the profile equation for a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

**Trace and decay give a pressure model.** Proved result `pressureModel_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a weak rotating profile with all moments and profile decay admits a smooth pressure solving ΔQ=−div(V·∇V) whose (j+1)st derivative decays at rate 4α−1+j.

**Pressure trace estimates give decay.** Proved result `pressureDecay_of_split`: Under the stated assumptions, this establishes that for 1<α<5/4, a smooth pressure solving the profile equation for a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

**Weighted products give pressure decay.** Proved result `pressureDecay_of_reduced`: Under the stated assumptions, this establishes that for 1<α<5/4, a smooth pressure solving the profile equation for a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

**Fourier formulas give pressure decay.** Proved result `pressureDecay_of_representation`: Under the stated assumptions, this establishes that for 1<α<5/4, a smooth pressure solving the profile equation for a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

**Homogeneous bounds give pressure decay.** Proved result `pressureDecay_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a smooth pressure solving the profile equation for a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

### Breakdown.FracCert.DecayPressureDiv

Takes the divergence of the smooth rotating profile equation, cancels the solenoidal drift and fractional terms, and identifies the pressure Poisson equation.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPressureDiv.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayPressureDiv`.

**The matrix trace as a linear functional.** Definition `traceL`: This defines the matrix trace as the continuous linear functional summing the three diagonal entries.

**The trace sums diagonal entries.** Proved result `traceL_apply`: For a linear map L on ℝ³, its trace is ∑ᵢ(Leᵢ)ᵢ.

**Divergence is the derivative trace.** Proved result `div_eq`: For a vector field f, div f(x) equals the trace of its derivative matrix at x.

**The infinitesimal turn as a linear map.** Definition `turnL`: This defines the continuous linear map sending (x₁,x₂,x₃) to (−x₂,x₁,0).

**The spatial turn is (−x₂,x₁,0).** Proved result `turnL_eq`: The bundled spatial turn sends (x₁,x₂,x₃) to (−x₂,x₁,0).

**The turn map is the axial generator.** Proved result `turnL_apply`: The linear turn operator used in the divergence calculation acts as the axial generator J(y₁,y₂,y₃)=(−y₂,y₁,0).

**Trace commutes with the axial turn.** Proved result `trace_comm_turn`: For every linear map L and the axial generator J, tr(LJ)=tr(JL).

**The Laplacian is gradient divergence.** Proved result `trace_eq_div_grad`: Under the stated hypotheses, the scalar Laplacian is gradient divergence.

**The residual gives pressure Laplacians.** Proved result `trace_of_residual`: Under the stated hypotheses, the residual gives the pressure Laplacian.

**Source namespace:** `Breakdown.FracCert`.

**Solenoidal powers give pressure traces.** Proved result `residualDivergence_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and a weak rotating profile with all moments and profile decay, every smooth pressure satisfying the profile residual equation also satisfies ΔP=−div(V·∇V).

**Fractional powers remain divergence free.** Proved result `powerDivergenceFree_of`: Under the stated assumptions, this establishes that for 1<α<5/4, the fractional power of a weak rotating profile with all moments and profile decay has zero classical divergence.

### Breakdown.FracCert.DecayPressureModel

Obtains the derivative decay of the Fourier-defined pressure by applying the degree-zero multiplier estimate to weighted velocity products.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPressureModel.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayPressureModel`.

**Pressure multipliers have degree zero.** Proved result `multiplier_homogeneous`: Each pressure multiplier −ξᵢξⱼ/|ξ|² is smooth off the origin and homogeneous of degree zero under positive dilation.

**Homogeneous bounds give pressure decay.** Proved result `modelPressureDecay_of`: Under the stated assumptions, this establishes that for 1<α<5/4, the Fourier pressure of a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

### Breakdown.FracCert.DecayPressureParts

Defines the pressure multiplier and the representation, Poisson, decay and harmonic-uniqueness contracts used in pressure regularity.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPressureParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert`.

**A smooth decaying pressure model exists.** Proposition `PressureModelStatement`: This proposition requires that for 1<α<5/4, a weak rotating profile with all moments and profile decay admits a smooth pressure solving ΔQ=−div(V·∇V) whose (j+1)st derivative decays at rate 4α−1+j.

**Model pressure satisfies Poisson.** Proposition `PressureTraceStatement`: This proposition requires that for 1<α<5/4, the Fourier pressure of a weak rotating profile with all moments and profile decay satisfies ΔP=−div(V·∇V) pointwise.

**Model pressure derivatives have decay.** Proposition `ModelPressureDecayStatement`: This proposition requires that for 1<α<5/4, the Fourier pressure of a weak rotating profile with all moments and profile decay has its (j+1)st derivative bounded by C(1+‖y‖)^(−(4α−1+j)).

**The pressure Fourier multiplier.** Definition `pressureMultiplier`: This defines the degree-zero pressure multiplier −ξᵢξⱼ/‖ξ‖², viewed as a complex scalar.

**Velocity products have weighted bounds.** Proposition `ProductWeightedSmoothStatement`: This proposition requires that for 1<α<5/4, each coordinate product of a weak rotating profile with all moments and profile decay is weighted smooth with base decay exponent 4α−2.

**Pressure is a sum of Fourier multipliers.** Proposition `PressureRepresentationStatement`: This proposition requires that for 1<α<5/4 and a weak rotating profile with all moments and profile decay, its coordinate velocity products have Fourier transforms whose pressure-multiplier products have all L¹ moments and whose inverse transforms sum in real part to the pressure.

**The profile pressure satisfies Poisson.** Proposition `ResidualDivergenceStatement`: This proposition requires that for 1<α<5/4 and a weak rotating profile with all moments and profile decay, every smooth pressure satisfying the profile residual equation also satisfies ΔP=−div(V·∇V).

**Fractional powers are divergence free.** Proposition `PowerDivergenceFreeStatement`: This proposition requires that for 1<α<5/4, the fractional power of a weak rotating profile with all moments and profile decay has zero classical divergence.

**Decaying harmonic gradients vanish.** Proposition `DecayingGradientVanishesStatement`: This proposition requires that an infinitely differentiable harmonic scalar function whose gradient is bounded by K(1+‖y‖)^(−s) for some s>0 has zero gradient everywhere.

### Breakdown.FracCert.DecayPressureRep

Relates the convolution-defined profile pressure to bounded measurable degree-zero multipliers acting on Fourier transforms of velocity products.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPressureRep.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayPressureRep`.

**Pressure multiplier norms are ≤1.** Proved result `multiplier_norm_le`: Under the stated hypotheses, pressure multipliers have norm at most one.

**Pressure multipliers are measurable.** Proved result `multiplier_measurable`: Each pressure multiplier ξ↦−ξᵢξⱼ/|ξ|² is measurable on ℝ³, with its specified value at ξ=0.

**Pressure has its Fourier representation.** Proved result `pressureRepresentation_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and a weak rotating profile with all moments and profile decay, its coordinate velocity products have Fourier transforms whose pressure-multiplier products have all L¹ moments and whose inverse transforms sum in real part to the pressure.

### Breakdown.FracCert.DecayPressureTrace

Proves the pressure model Poisson identity from its Fourier representation and transfers profile derivative decay to every velocity product.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPressureTrace.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayPressureTrace`.

**Coordinate squares give the norm².** Proved result `sum_sq_coord`: Under the stated hypotheses, coordinate squares sum to the squared norm.

**Divergence preserves sums.** Proved result `divergenceAt_add'`: At a point where f and g are differentiable, div(f+g)=div f+div g.

**The model has the required trace.** Proved result `pressureTrace_of`: Under the stated assumptions, this establishes that for 1<α<5/4, the Fourier pressure of a weak rotating profile with all moments and profile decay satisfies ΔP=−div(V·∇V) pointwise.

**Profile products are weighted smooth.** Proved result `productWeightedSmooth_of`: Under the stated assumptions, this establishes that for 1<α<5/4, each coordinate product of a weak rotating profile with all moments and profile decay is weighted smooth with base decay exponent 4α−2.

### Breakdown.FracCert.DecayPressureVanish

Proves the harmonic uniqueness step for pressure by a maximum-principle argument applied to directional derivatives that decay at infinity.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayPressureVanish.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayPressureVanish`.

**Local maxima have nonpositive Hessians.** Proved result `second_le_of_localMax`: At a local maximum x of a smooth scalar function w, its Hessian satisfies D²w(x)[v,v]≤0 for every direction v.

**Local maxima have nonpositive Laplacians.** Proved result `trace_le_of_localMax`: At a local maximum of a smooth scalar function, the sum of its three second coordinate derivatives, Δw, is nonpositive.

**The Laplacian of ε‖x‖² is 6ε.** Proved result `trace_quadratic`: Under the stated hypotheses, quadratic Laplacians equal six times scale.

**Harmonic upper decay gives a sign.** Proved result `nonpos_of_decay`: Under the stated hypotheses, harmonic upper decay forces nonpositivity.

**Harmonic derivatives remain harmonic.** Proved result `dir_harmonic`: Under the stated hypotheses, derivatives of harmonic fields are harmonic.

**Decaying harmonic gradients vanish.** Proved result `decayingGradientVanishes`: Under the stated assumptions, this establishes that an infinitely differentiable harmonic scalar function whose gradient is bounded by K(1+‖y‖)^(−s) for some s>0 has zero gradient everywhere.

### Breakdown.FracCert.DecayStep

Bootstraps the base velocity decay to the expected decay of every spatial derivative through the tensor-square fixed-point equation.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/DecayStep.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.DecayStep.Internal`.

**The tensor product as a bilinear map.** Definition `pairMap`: This defines the continuous bilinear map sending two vectors to the tensor with entries vᵢwₖ.

**The tensor map has norm at most one.** Proved result `norm_pairMap_le`: The bilinear map (u,v)↦u⊗v, with the coordinate tensor norm used here, has operator norm at most one.

**Tensor squares are bilinear evaluations.** Proved result `tensorSq_eq`: The tensor square of a field V is obtained by evaluating the tensor-product bilinear map on (V(y),V(y)) at each point.

**Product decay weights add.** Proved result `prod_weight`: If w≥1, c≤e₁+e₂, x₁,x₂≥0 and w^eᵢxᵢ≤Gᵢ for i=1,2, then wᶜx₁x₂≤G₁G₂.

**Decay bounds become weighted bounds.** Proved result `weight_of`: For a positive weight w, x≤Cw^(−e) implies wᵉx≤C.

**Weighted bounds become decay bounds.** Proved result `unweight_of`: For a positive weight w, wᵉx≤K implies x≤Kw^(−e).

**Lower derivatives give the next decay.** Proved result `decay_core`: Under the stated hypotheses, lower derivative decay gives the next rate.

**Source namespace:** `Breakdown.FracCert`.

**Profile derivatives gain decay.** Proved result `profileDecayStep_of`: Under the stated assumptions, this establishes that for 1<α<5/4, the expected decay bounds on all lower derivatives of a weak rotating profile with all moments imply the jth derivative bound C(1+‖y‖)^(−(2α−1+j)).

### Breakdown.FracCert.DefectRightSide

Verifies the L² and symmetry properties needed to use the profile defect and correction convection as a right-hand side for the held contraction.

This belongs to the fractional analogue of the paper §7 certificate strategy; it supplies definitions, quantitative inverse bounds or the held-solution bridge, while its fractional conclusions are outside the ordinary-dissipation argument claimed in the paper.

Source: `lean/Breakdown/FracCert/DefectRightSide.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Compatible symmetries retain the defect.** Proved result `defect_at`: Under the stated hypotheses, compatible symmetries preserve the defect.

**Compatible symmetries retain the forcing.** Proved result `rhs_at`: Under the stated hypotheses, compatible symmetries preserve the forcing.

**Profile self-convection belongs to L².** Proved result `quad_memLp`: For a valid fractional certificate and every p in its parameter box, the profile's self-convection (Wₚ·∇)Wₚ belongs to L²(ℝ³).

**The defect gives admissible forcing.** Proved result `defectRightSide`: Under the stated assumptions, this establishes that a valid fractional certificate makes its defect square integrable and makes minus that defect minus the correction convection an admissible symmetry-class forcing.

### Breakdown.FracCert.Defs

Defines the fractional certificate language: weak derivatives, symmetry and gradient spaces, weighted energies, projected residuals, bordered operators and the scalar bounds used in validation.

This belongs to the fractional analogue of the paper §7 certificate strategy; it supplies definitions, quantitative inverse bounds or the held-solution bridge, while its fractional conclusions are outside the ordinary-dissipation argument claimed in the paper.

Source: `lean/Breakdown/FracCert/Defs.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert`.

**The squared matrix-entry norm.** Definition `entrySq`: This defines the squared matrix-entry norm by summing ‖G(eᵢ)‖² over the three coordinate vectors.

**The matrix-entry inner product.** Definition `entryInner`: This defines the matrix-entry inner product by summing the inner products of corresponding columns.

**The trace of second derivatives.** Definition `secondTrace`: This defines the vector-valued second trace by summing H(eⱼ,eⱼ) over the three coordinate directions.

**The discrete axial turn.** Definition `turnStep`: This defines axial rotation through angle 2π/m, leaving the third coordinate fixed.

**Reflection of the third coordinate.** Definition `mirror`: This defines reflection by retaining the first two coordinates and negating the third.

**The equivariant vector-field class.** Definition `IsClassField`: This predicate requires a vector field to commute almost everywhere with the discrete axial turn and with reflection.

**The invariant scalar-field class.** Definition `IsClassScalar`: This predicate requires a scalar field to be pointwise invariant under the discrete axial turn and reflection.

**Smooth compact vector tests.** Definition `IsTestVectorField`: This predicate requires a vector test field to be infinitely differentiable and compactly supported.

**Smooth compact scalar tests.** Definition `IsTestScalar`: This predicate requires a scalar test function to be infinitely differentiable and compactly supported.

**The weak gradient identity.** Definition `IsWeakGradientOf`: This predicate specifies G as the weak gradient of v through integration by parts against every compact smooth scalar test in each coordinate direction.

**The weak second-derivative identity.** Definition `IsWeakSecondDerivOf`: This predicate specifies H as the weak derivative of G through coordinatewise integration by parts against compact smooth scalar tests.

**Integrability on every compact set.** Definition `IsLocalSquareIntegrable`: This predicate requires the supplied scalar function to be integrable on every compact set.

**Locally L² gradient fields.** Definition `IsGradientField`: This predicate requires a measurable vector field with locally integrable squared norm and a potential with locally integrable square satisfying the scalar weak-gradient identities.

**Square-integrable solenoidal fields.** Definition `IsSolenoidalL2`: This predicate requires a vector field to belong to L² and to annihilate the gradients of all compact smooth scalar tests.

**The integral L² norm.** Definition `l2Norm`: This defines the integral L² size as the square root of ∫‖F(y)‖² dy.

**The integral L² pairing.** Definition `l2Pair`: This defines the real integral pairing ∫⟨F(y),E(y)⟩ dy.

**The gradient-quotient residual norm.** Definition `projectedNorm`: This defines the projected residual norm as the infimum of the L² norms of F+Q over weak gradient fields Q for which F+Q belongs to L².

**A second-order solenoidal symmetry field.** Structure `IsSecondOrderField`: This proposition bundles measurable velocity and derivative fields, L⁶ velocity, finite gradient and full Hessian energies, the two weak-derivative identities, almost-everywhere zero divergence and the discrete rotation and reflection symmetry.

**The weak fractional-power identity.** Definition `IsWeakFractionalPower`: This predicate requires P to belong to L² and to represent the fractional power of v by transferring the fractional operator to every compact smooth vector test.

**The rotating self-similar drift.** Definition `driftField`: This defines the rotating self-similar drift (1−1/(2α))v+G(y)/(2α)+a(G(Jy)−Jv).

**The weighted derivative energy.** Definition `weightedEnergy`: This defines weighted derivative energy as the squared L² norm of the second trace plus the integral of the weight times the squared matrix-entry norm of G.

**The energy and multiplier size.** Definition `sizeNorm`: This defines the correction size as the square root of weighted derivative energy plus μ² times the squared Euclidean norm of the multiplier vector.

**The gradient pin functional.** Definition `pinValue`: This defines a pin functional by the integral matrix-entry pairing of the correction gradient with the supplied pin field.

**The coefficient vector norm.** Definition `vecNorm`: This defines the coefficient-vector norm as the square root of the sum of its squared entries.

**The symmetric convection product.** Definition `symProduct`: This defines the symmetric convection product as one half of G(W)+DW(v).

**The weighted residual row size.** Definition `rowSize`: This defines the residual row size as the square root of the weighted sum of squared pairings with the finite row fields.

**The row size modulo gradients.** Definition `rowSeminorm`: This defines the row seminorm modulo gradients as the infimum of the row sizes of F+Q over weak gradient fields Q.

**The scalar inverse-bound function.** Definition `boundConst`: This defines the explicit quadratic-root inverse bound from the form scale, contraction factor, coercivity gap, pin weight and three residual sizes.

**The small quadratic solution radius.** Definition `radiusOf`: This defines the smaller quadratic solution radius in its rationalized form 2ρ/(1+√(1−4KNLρ)).

**The coordinate parameter box.** Definition `box`: This defines the parameter box by the coordinate bounds |pᵢ|≤radᵢ.

**The negative second trace.** Definition `negSecondTrace`: This defines the negative second trace by negating the sum of the three diagonal second derivatives.

**Source namespace:** `Breakdown.SteadyCert.FracCertData`.

**The approximate profile gradient.** Definition `gradProfile`: This defines the approximate profile gradient as the Fréchet derivative of the parameterized profile.

**The local bordered operator.** Definition `localField`: This defines the local bordered operator as drift minus the split viscosity times the second trace, plus twice the symmetric profile-correction convection and the actuator combination.

**The fractional splitting correction.** Definition `splitField`: This defines the fractional splitting correction as the weak fractional power plus the split viscosity times the second trace.

**The certificate derivative energy.** Definition `energy`: This specializes the weighted derivative energy to the certificate's weight.

**The certificate correction size.** Definition `size`: This specializes the correction size to the certificate's weight and multiplier scale.

**The nonnegative splitting energy.** Definition `splitEnergy`: This defines the square root of the splitting pairing against the negative trace plus reduced coercivity times the trace energy and minimum-weight gradient energy.

**The certificate pin vector.** Definition `pins`: This defines the finite pin vector by pairing the correction gradient with each certificate pin field.

**The approximate profile defect.** Definition `defect`: This defines the profile defect as the approximate profile drift, fractional power, self-convection and multiplier-weighted actuator sum.

**The certificate residual row size.** Definition `rows`: This specializes the weighted row size to the certificate's row fields and row weights.

**The certificate rows modulo gradients.** Definition `rowsModGrad`: This specializes the row seminorm modulo gradients to the certificate's row fields and weights.

**The remaining coercivity gap.** Definition `reducedGap`: This defines the coercivity gap remaining after subtracting the low-frequency loss from reduced coercivity.

**The scalar contraction factor.** Definition `contraction`: This defines the contraction factor from the split bound, row loss, pin loss, pin weight and remaining coercivity gap through the displayed square-root expression.

**The certificate inverse-bound function.** Definition `boundFn`: This specializes the explicit inverse-bound function to the certificate's form scale, contraction, coercivity gap and pin weight.

**The residual-to-size constant.** Definition `rowConst`: This defines the residual-to-size constant by evaluating the inverse-bound function at residual norm one, row input √rowMax and zero pin input.

**The certified held radius.** Definition `heldRadius`: This defines the held radius by applying the quadratic radius formula to the residual-to-size constant, nonlinear product constant and defect size bound.

**The active and stiff test region.** Definition `testBox`: This defines the held test region from the active coordinate set, coordinate radii, slopes and stiff ellipsoid radius.

**The actuator-adjoint frame error.** Definition `adjointError`: This defines the actuator-adjoint error vector by subtracting the chosen frame column from the actuator pairings with the jth adjoint field.

**The slope-adjusted multiplier error.** Definition `adjustedMultiplier`: This defines the transformed multiplier error after subtracting both the defect pairing with the jth adjoint and the expected slope times parameter coordinate.

**A fractional certificate exists.** Proposition. For an exponent α, some certificate data satisfy the fractional certificate conditions. ([`FracCertificateHypothesis`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCert/Defs.lean#L327))

**Fractional certificate conditions.** Structure. The fractional certificate conditions on certificate data for an exponent α: polynomial order at least 3, a coercivity constant between zero and the split viscosity, a positive pin weight, row maximum and multiplier scale, a measurable weight in the symmetry class bounded between positive constants, nonnegative radii, nonzero slopes, an ellipsoid radius bounded by the inactive slopes, and a frame that distorts lengths by a factor less than one. ([`IsFracCert`](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCert/Defs.lean#L223))

### Breakdown.FracCert.DriftEnergy

Proves the drift-gradient energy identity by a localized divergence calculation and removal of radial cutoffs with controlled boundary terms.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/DriftEnergy.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Axial turns do not increase norms.** Proved result `norm_axialTurn_le`: The axial generator J(y₁,y₂,y₃)=(−y₂,y₁,0) has |Jy|≤|y| for every y. Source: `Breakdown.FracCert.DriftEnergy:13`.

**The axial turn is continuous.** Proved result `continuous_axialTurn`: The map y↦(−y₂,y₁,0), which generates axial rotations, is continuous on ℝ³.

**Coordinate unit vectors have norm one.** Proved result `norm_unitVector`: Each of the three coordinate basis vectors in ℝ³ has Euclidean norm one.

**Cutoff derivatives vanish far away.** Proved result `fderiv_cutoff_far`: For a positive cutoff radius r, ∇χᵣ(y)=0 whenever |y|>2r.

**Cutoff derivatives vanish near zero.** Proved result `fderiv_cutoff_near`: For a positive cutoff radius r, ∇χᵣ(y)=0 whenever |y|< r.

**Radial cutoffs have uniform bounds.** Proved result `cutoff_bounds`: Under the stated hypotheses, radial cutoff derivatives have uniform bounds.

**Hessian entries are measurable.** Proved result `aesm_apply_second`: If the vector-valued Hessian field H is measurable, each field H(y)[eᵢ,eⱼ] is measurable.

**Gradient columns are measurable.** Proved result `aesm_apply_first`: If the matrix field G is measurable, each of its coordinate columns G(y)eᵢ is measurable.

**The negative second trace belongs to L².** Proved result `memLp_negSecondTrace`: For an admissible second-order field, the negative trace of its weak Hessian, −Δv, belongs to L²(ℝ³).

**The drift boundary is energy controlled.** Proved result `boundary_bound`: If |∇χ(y)|≤c and |y||∇χ(y)|≤2c, the absolute drift boundary term is at most (3c/2)(|Dα,a v|²+|G|²)+c(|1/(2α)|+|a|)|G|² at y, where Dα,a is the dilation-and-rotation drift and G is the gradient field.

**The spatial turn is (−x₂,x₁,0).** Proved result `axialTurn_eq`: The axial generator sends (x₁,x₂,x₃) to (−x₂,x₁,0).

**The axial turn is smooth.** Proved result `contDiff_axialTurn`: The axial generator y↦(−y₂,y₁,0) is smooth of every order. Source: `Breakdown.FracCert.DriftEnergy:153`.

**Smooth inputs give a smooth drift flux.** Proved result `contDiff_driftFlux`: If u and the scalar cutoff χ are smooth, each coordinate flux in the localized drift-energy identity is smooth.

**Compact derivatives integrate to zero.** Proved result `integral_fderiv_eq_zero`: For a compactly supported C¹ scalar function f and a fixed vector e, ∫Df(y)[e]dy=0.

**A compact factor gives compact support.** Proved result `compactSupport_of_factor`: If χ has compact support and g vanishes wherever χ vanishes, then g also has compact support.

**Divergence gives the local identity.** Proved result `driftLocalSmooth_of`: Under the stated assumptions, this establishes that for a smooth velocity and compact smooth cutoff, the localized drift-trace pairing equals (1−3/(4α)) times the localized gradient energy plus the boundary integral.

**The axial turn as a linear map.** Definition `turnMap`: This defines the infinitesimal axial turn as a continuous linear map on spatial vectors.

**The spatial turn is (−x₂,x₁,0).** Proved result `turnMap_eq`: The continuous spatial turn sends (x₁,x₂,x₃) to (−x₂,x₁,0), agreeing with the axial generator.

**Coordinates reconstruct each vector.** Proved result `expand_vec`: Every x∈ℝ³ has the expansion x=x₁e₁+x₂e₂+x₃e₃.

**The turn map acts on the basis.** Proved result `turnMap_units`: The axial generator sends e₁ to e₂, e₂ to −e₁ and e₃ to zero.

**Coordinates reconstruct the turn map.** Proved result `turnMap_expand`: For z∈ℝ³, the axial generator has the coordinate formula Jz=−z₂e₁+z₁e₂.

**Drift flux has the energy divergence.** Proved result `driftDivergence`: Under the stated assumptions, this establishes that for smooth velocity and cutoff, the divergence of the defined flux equals the localized drift-trace pairing density minus (1−3/(4α)) times the gradient-energy density and minus the boundary density.

**Smooth limits give the local identity.** Proved result `driftLocal_of`: Under the stated assumptions, this establishes that for any second-order field and compact smooth cutoff, the cutoff pairing of drift with the negative second trace equals (1−3/(4α)) times the cutoff gradient energy plus the explicitly defined boundary integral.

**Local identities give drift energy.** Proved result `driftEnergy_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and an L² drift, its pairing with the negative second trace of a second-order field equals (1−3/(4α)) times the gradient energy.

**Drift pairing equals gradient energy.** Proved result `driftEnergy`: Under the stated assumptions, this establishes that for 1<α<5/4 and an L² drift, its pairing with the negative second trace of a second-order field equals (1−3/(4α)) times the gradient energy.

### Breakdown.FracCert.DriftEnergyLocal

Proves the local weak drift identity by mollifying the velocity and its weak derivatives, organizing convergence of L² factors and compactly weighted integrals.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/DriftEnergyLocal.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**The cutoff drift boundary term.** Definition `driftBoundary`: This defines the cutoff boundary term as the sum of cutoff-gradient pairings between drift and gradient columns, minus one half of the cutoff derivative along the spatial drift times gradient energy density.

**The localized drift energy identity.** Proposition `DriftLocalStatement`: This proposition requires that for any second-order field and compact smooth cutoff, the cutoff pairing of drift with the negative second trace equals (1−3/(4α)) times the cutoff gradient energy plus the explicitly defined boundary integral.

**The smooth localized drift identity.** Proposition `DriftLocalSmoothStatement`: This proposition requires that for a smooth velocity and compact smooth cutoff, the localized drift-trace pairing equals (1−3/(4α)) times the localized gradient energy plus the boundary integral.

**Smooth fields approximate drift data.** Proposition `DriftLocalApproxStatement`: This proposition requires that every second-order field and compact smooth cutoff admit smooth approximations for which the localized drift-trace pairing, gradient energy and boundary integral all converge to their weak-field counterparts.

**The localized drift flux.** Definition `driftFlux`: This defines the ith localized flux as the cutoff times minus the drift-gradient-column pairing plus one half of the ith spatial drift coefficient times gradient energy density.

**Drift flux has the energy divergence.** Proposition `DriftDivergenceStatement`: This proposition requires that for smooth velocity and cutoff, the divergence of the defined flux equals the localized drift-trace pairing density minus (1−3/(4α)) times the gradient-energy density and minus the boundary density.

**A shrinking smooth averaging bump.** Definition `approxBump`: This defines a smooth bump centered at zero with inner radius 1/(2(n+1)) and outer radius 1/(n+1).

**Convolution with the normalized bump.** Definition `smoothen`: This defines smoothing by convolution with the normalized shrinking bump.

**Bump radii are at most one.** Proved result `approxBump_rOut_le`: Every outer support radius in the chosen mollifier sequence is at most one.

**Bump radii tend to zero.** Proved result `approxBump_rOut_tendsto`: The outer support radii of the chosen mollifiers tend to zero as their index tends to infinity.

**Mollification gives smooth fields.** Proved result `smoothen_contDiff`: Convolving a locally integrable function taking values in a real Banach space with any mollifier in the chosen sequence gives a smooth function.

**Mollifiers commute with weak derivatives.** Proved result `smoothen_partial`: Under the stated hypotheses, mollification commutes with weak derivatives.

**The normalized bump has unit mass.** Proved result `approxBump_lintegral`: Each normalized bump in the mollifier sequence has nonnegative integral mass one.

**Mollifiers do not increase L² energy.** Proved result `smoothen_sq_le`: Under the stated hypotheses, mollification does not increase L² energy.

**L² seminorm² equals the square integral.** Proved result `eLpNorm_two_sq_space`: Under the stated hypotheses, squared L² seminorms equal squared integrals.

**Zero square-mass limit gives norm decay.** Proved result `eLpNorm_tendsto_of_sq_space`: Under the stated hypotheses, vanishing squared mass gives vanishing norm.

**Mollification contracts L² differences.** Proved result `smoothen_sub_eLpNorm_le`: For locally integrable Banach-valued functions f and g, convolution with a normalized mollifier satisfies ‖ρₙ*f−ρₙ*g‖₂≤‖f−g‖₂, including when the right side is infinite.

**Compact continuous fields recover in L².** Proved result `smoothen_sq_tendsto_of_continuous`: If g is continuous and compactly supported, ∫|ρₙ*g−g|² tends to zero as the mollifier radius tends to zero.

**Mollifiers recover L² fields.** Proved result `smoothen_eLpNorm_tendsto`: For every Banach-valued f∈L², ‖ρₙ*f−f‖₂ tends to zero.

**Mollifiers recover fields locally in L².** Proved result `smoothen_local_tendsto`: If K is compact and f is square-integrable on its closed unit neighbourhood, the mollifications converge to f in L²(K).

**Strong L² convergence on a fixed set.** Definition `SqLim`: This predicate requires every sequence member and its proposed limit to lie in L² on K and the L² seminorm of their differences to tend to zero.

**Continuous fields are locally L².** Proved result `memLp_restrict_of_continuous`: A continuous normed-space-valued function is square-integrable on every compact subset of ℝ³.

**Mollifiers converge on compact sets.** Proved result `smoothen`: For compact K, a locally integrable f that is square-integrable on the closed unit neighbourhood of K is the strong L²(K) limit of its smooth mollifications, all of which belong to L²(K).

**Equal fields retain strong L² limits.** Proved result `congr`: Under the stated hypotheses, equal fields retain strong L² convergence.

**Strong L² convergence respects sums.** Proved result `add`: If Fₙ→f and Gₙ→g strongly in L²(K), with all functions square-integrable there, then Fₙ+Gₙ→f+g strongly in L²(K).

**Pointwise errors transfer L² limits.** Proved result `of_le`: Under the stated hypotheses, pointwise error bounds transfer L² limits.

**Continuous weights retain L² limits.** Proved result `smul_fun`: Under the stated hypotheses, continuous weights preserve local L² limits.

**Linear maps preserve strong L² limits.** Proved result `clm`: Applying a fixed bounded linear map to a strongly convergent L²(K) sequence preserves the strong limit when K is compact.

**Negation preserves strong L² limits.** Proved result `neg`: For compact K, Fₙ→f strongly in L²(K) implies −Fₙ→−f strongly in L²(K).

**Differences preserve strong L² limits.** Proved result `sub`: For compact K, strong L²(K) convergence Fₙ→f and Gₙ→g implies Fₙ−Gₙ→f−g strongly in L²(K).

**Three strong L² limits may be summed.** Proved result `sum3`: If each of three sequences Fᵢ,ₙ converges strongly to fᵢ in L²(K), then their sum converges strongly to ∑ᵢfᵢ in L²(K).

**Strong L² pairings converge.** Proved result `tendsto_inner`: Under the stated hypotheses, strong L² pairs have convergent integrals.

**Local L² fields pair integrably.** Proved result `integrableOn_inner`: If vector fields A and B are square-integrable on K, their scalar product is integrable on K.

**Convergence of scalar integrals.** Definition `IntLim`: This predicate requires integrability of every scalar integrand and its proposed limit, together with convergence of the real integrals.

**Equal integrands retain integral limits.** Proved result `congr`: Under the stated hypotheses, equal integrands retain integral convergence.

**Integral convergence respects sums.** Proved result `add`: If Pₙ,Qₙ,p,q are integrable and their integrals converge respectively to ∫p and ∫q, then ∫(Pₙ+Qₙ) converges to ∫(p+q).

**Integral limits respect differences.** Proved result `sub`: Under the stated hypotheses, integral convergence respects differences.

**Three integral limits may be summed.** Proved result `sum3`: For three integrable sequences whose integrals converge to the corresponding limit integrals, the integral of their sum converges to the integral of the sum of the limits.

**Compact weighted pairings pass to limits.** Proved result `base`: If c is continuous and supported in compact K, and Fₙ→f and Gₙ→g strongly in L²(K), then every weighted product is integrable and ∫cFₙ·Gₙ→∫cf·g.

**Basis vectors reconstruct linear maps.** Proved result `clm_expand`: For a linear map A and w∈ℝ³, Aw=∑ᵢwᵢAeᵢ.

**The axial turn as a linear map.** Definition `turnMap`: This equips the infinitesimal axial turn with its continuous linear map structure. Source: `Breakdown.FracCert.DriftEnergyLocal:509`.

**The spatial turn is (−x₂,x₁,0).** Proved result `turnMap_apply`: The continuous spatial turn sends (x₁,x₂,x₃) to (−x₂,x₁,0), agreeing with the axial generator. Source: `Breakdown.FracCert.DriftEnergyLocal:519`.

**Coordinate functions are continuous.** Proved result `coord_continuous`: Each coordinate projection y↦yᵢ is continuous on ℝ³.

**The drift from gradient columns.** Definition `driftOf`: This defines the rotating drift from the velocity vector and three gradient columns through their coordinate expansions.

**Gradient columns recover the drift field.** Proved result `driftField_eq`: The dilation-and-rotation drift (1−1/(2α))u+(1/(2α))Ay+a(AJy−Ju) can be reconstructed pointwise from u and the three columns Aeᵢ.

**Local L² limits preserve the drift.** Proved result `driftOf`: On a compact set, strong L² convergence of the velocity and all three gradient columns implies strong L² convergence of their dilation-and-rotation drift, for fixed α and a.

**Matrix energy is a sum of column pairs.** Proved result `mul_entrySq_eq`: Under the stated hypotheses, matrix energy splits into column pairings.

**Boundary terms split into column pairs.** Proved result `driftBoundary_eq`: Under the stated hypotheses, boundary terms split into column pairings.

**Smooth limits preserve drift integrals.** Proved result `driftLocalApprox`: Under the stated assumptions, this establishes that every second-order field and compact smooth cutoff admit smooth approximations for which the localized drift-trace pairing, gradient energy and boundary integral all converge to their weak-field counterparts.

### Breakdown.FracCert.DriftPower

Derives the mixed drift and fractional-power identity from weak frequency transport and the weighted flow pairing, with the required Fourier integrability.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/DriftPower.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert`.

**The frequency drift-power identity.** Proposition `DriftPairSymbolStatement`: This proposition requires that for 1<α<5/4 and the stated L² weighted-symbol assumptions, the drift-symbol pairing with (2π‖ξ‖)^(2α−2) times the second symbol equals (3/2−5/(4α)) times its (2α−4)-weighted squared integral.

**Source namespace:** `Breakdown.SteadyCert.Internal.DriftPower`.

**Intermediate weights have two bounds.** Proved result `freqPow_le`: Under the stated hypotheses, intermediate weights lie between two bounds.

**Radial frequency powers are measurable.** Proved result `measurable_freqPow`: For every real exponent s, ξ↦(2π|ξ|)ˢ is measurable.

**Endpoint energies control middle weights.** Proved result `integrable_weighted`: Under the stated hypotheses, endpoint energies control intermediate weights.

**The L² representative equals its field.** Proved result `toLpOrZero_ae'`: For an L² vector field f, its chosen L² representative agrees with f almost everywhere.

**Fourier transform preserves L² pairings.** Proved result `l2Pair_eq`: For F,E∈L²(ℝ³;ℝ³), ∫F·E equals the integral of the real inner product of their Fourier transforms.

**Source namespace:** `Breakdown.SteadyCert`.

**Fourier identities give mixed energy.** Proved result `driftPower_of`: Under the stated assumptions, this establishes that for 1<α<5/4, the pairing of an L² drift with the weak fractional power equals (3/2−5/(4α)) times the integral of (2π‖ξ‖)^(2α−4) times the squared negative-second-trace symbol, and that integral is finite.

**The infinitesimal frequency turn.** Definition `freqTurn`: This defines the infinitesimal turn on complex vectors by (z₁,z₂,z₃) ↦ (−z₂,z₁,0).

**Smooth frequency tests away from zero.** Definition `IsFreqTest`: This predicate requires an infinitely differentiable, compactly supported frequency test whose closed support avoids zero.

**The frequency flow adjoint.** Definition `flowAdjoint`: This defines the frequency flow adjoint as (1−1/(2α))ψ+Dψ(ξ)/(2α)−aDψ(Jξ)+aJψ.

**The weak Fourier drift identity.** Proposition `DriftSymbolWeakStatement`: This proposition requires that for 1<α<5/4 and a second-order field with L² drift, the drift symbol pairs with every frequency test as the inverse-square-weighted second symbol paired with the flow adjoint of that test.

**Weak flow derivatives give energy.** Proposition `FlowPairingStatement`: This proposition requires that for 1<α<5/4, an L² weak flow derivative D of a field h with its first and 2α frequency weights in L² satisfies the identity ∫⟨D,(2π‖ξ‖)^(2α)h⟩=(3/2−5/(4α))∫(2π‖ξ‖)^(2α)‖h‖².

**Source namespace:** `Breakdown.SteadyCert.Internal.DriftPower`.

**Frequency powers multiply by adding.** Proved result `freqPow_mul`: Under the stated hypotheses, frequency exponents add under multiplication.

**Inversion negates frequency exponents.** Proved result `freqPow_inv`: Under the stated hypotheses, inverting frequency powers negates exponents.

**Frequency powers are nonnegative.** Proved result `freqPow_nonneg`: For every real s and every ξ, the radial frequency weight (2π|ξ|)ˢ is nonnegative.

**Almost every frequency is nonzero.** Proved result `ae_ne_zero`: The frequency ξ is nonzero at almost every point with respect to Lebesgue measure on ℝ³. Source: `Breakdown.FracCert.DriftPower:137`.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak drift and flow give the pairing.** Proved result `driftPairSymbol_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and the stated L² weighted-symbol assumptions, the drift-symbol pairing with (2π‖ξ‖)^(2α−2) times the second symbol equals (3/2−5/(4α)) times its (2α−4)-weighted squared integral.

### Breakdown.FracCert.DriftPowerSolenoidal

Shows that both the rotating drift and weak fractional power annihilate compact gradient tests, yielding a solenoidal free residual.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/DriftPowerSolenoidal.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.DriftPowerSolenoidalInternal`.

**Basis pairings give vector coordinates.** Proved result `unit_inner`: Under the stated hypotheses, basis pairings recover vector coordinates.

**Reversed pairings give coordinates.** Proved result `unit_inner'`: Under the stated hypotheses, reversed basis pairings recover coordinates.

**Second-order velocities are locally L¹.** Proved result `locInt_velocity`: Under the stated hypotheses, second-order velocities are locally integrable.

**Gradient columns belong to L².** Proved result `memLp_col`: For an admissible second-order field, each weak gradient column ∂ⱼv belongs to L²(ℝ³).

**Gradient columns are locally integrable.** Proved result `locInt_col`: For an admissible second-order field, each weak gradient column ∂ⱼv is locally integrable on ℝ³.

**Compact weights give integrable pairs.** Proved result `integrable_pair`: Under the stated hypotheses, compact scalar weights give integrable pairs.

**Weak gradients give coordinate pairings.** Proved result `weak_pair`: For an admissible field v with weak gradient G and a smooth compactly supported scalar ψ, ∫∂ⱼψ·vᵢ=−∫ψ(Geⱼ)ᵢ for every pair of coordinate indices i,j.

**The velocity annihilates gradients.** Proved result `weak_div`: Under the stated hypotheses, the velocity annihilates scalar gradients.

**Basis vectors reconstruct each vector.** Proved result `basis_sum`: Every vector x∈ℝ³ equals the sum ∑ⱼxⱼeⱼ of its coordinate components.

**Gradients give directional derivatives.** Proved result `grad_inner`: Under the stated hypotheses, gradient pairings are directional derivatives.

**Smooth derivatives are differentiable.** Proved result `diff_fderiv`: For a smooth scalar function φ, its derivative Dφ is differentiable at every point.

**Smooth second derivatives commute.** Proved result `symm2`: For a smooth scalar φ, D²φ(y)[a,b]=D²φ(y)[b,a] for all y,a,b∈ℝ³.

**A coefficient-weighted derivative test.** Definition `coef`: This defines the scalar coefficient test (My)ⱼ times the ith coordinate derivative of the scalar test.

**A derivative along the linear flow.** Definition `flowTest`: This defines the scalar test obtained by differentiating φ along the linear vector field My.

**Linear coordinates have their derivative.** Proved result `coord_hasFDerivAt`: For a linear map M, the derivative of y↦(My)ⱼ is the linear functional h↦(Mh)ⱼ at every y.

**Coefficient tests retain smooth support.** Proved result `test_coef`: Under the stated hypotheses, coefficient tests retain compact smoothness.

**Flow tests retain compact smoothness.** Proved result `test_flow`: If φ is smooth with compact support and M is linear, the scalar function y↦Dφ(y)[My] is also smooth with compact support.

**Coefficient tests obey the product rule.** Proved result `deriv_coef`: For smooth φ, ∂ⱼ((My)ⱼ∂ᵢφ)=Mⱼⱼ∂ᵢφ+(My)ⱼ∂ⱼ∂ᵢφ.

**Flow tests obey the chain rule.** Proved result `deriv_flow`: For smooth φ and a linear map M, D(Dφ(·)[M·])(y)[w]=D²φ(y)[w,My]+Dφ(y)[Mw].

**Matrix actions expand in coefficients.** Proved result `expand_left`: Under the stated hypotheses, matrix actions expand in test coefficients.

**Linear functionals expand in coordinates.** Proved result `lin_expand`: Every linear functional L on ℝ³ satisfies Lx=∑ᵢxᵢL(eᵢ).

**Coefficient derivatives give divergence.** Proved result `pointwise_flow`: Under the stated hypotheses, coefficient derivatives give flow divergence.

**Solenoidality transfers a linear flow.** Proved result `flow_identity`: For an admissible solenoidal field v with weak gradient G, any linear M and any smooth compactly supported φ, ∫G(y)My·∇φ(y)dy=∫Mv(y)·∇φ(y)dy.

**Gradient-flow pairings are integrable.** Proved result `int_left`: For an admissible field v with gradient G and a smooth compactly supported scalar φ, y↦G(y)My·∇φ(y) is integrable for every linear M.

**Velocity-flow pairings are integrable.** Proved result `int_right`: For an admissible field v and a smooth compactly supported scalar φ, y↦Mv(y)·∇φ(y) is integrable for every linear M.

**The axial turn as a linear map.** Definition `turnMap`: This equips the infinitesimal axial turn with its continuous linear map structure. Source: `Breakdown.FracCert.DriftPowerSolenoidal:283`.

**The spatial turn is (−x₂,x₁,0).** Proved result `turnMap_apply`: The continuous spatial turn sends (x₁,x₂,x₃) to (−x₂,x₁,0), agreeing with the axial generator. Source: `Breakdown.FracCert.DriftPowerSolenoidal:296`.

**Local L¹ fields pair with compact tests.** Proved result `integrable_inner_cpt`: Under the stated hypotheses, local integrability pairs with compact tests.

**Smooth scalar gradients are smooth.** Proved result `grad_smooth`: The gradient of a smooth scalar function is a smooth vector field.

**Gradient support remains compact.** Proved result `grad_support`: If a scalar function has compact support, its gradient also has compact support.

**Velocity-gradient pairs are integrable.** Proved result `integrable_div`: Under the stated hypotheses, velocity-gradient pairings are integrable.

**Drift annihilates compact gradients.** Proved result `drift_zero`: For an admissible solenoidal field v, its dilation-and-rotation drift pairs to zero with ∇φ for every smooth compactly supported scalar test φ, for all real α and a.

**Directional derivatives differentiate.** Proved result `dapp`: Under the stated hypotheses, directional derivatives commute with differentiation.

**Derivatives commute with gradients.** Proved result `grad_fderiv`: Under the stated hypotheses, differentiation commutes with the gradient.

**Gradient remainders split into gradients.** Proved result `remainder_grad`: For smooth ξ, the second-order Taylor remainder of ∇ξ is the gradient of ξ(·+z)−ξ−Dξ[z]−½D²ξ[z,z], evaluated at x.

**Translations preserve scalar tests.** Proved result `test_shift`: Translating a smooth compactly supported scalar test by any z∈ℝ³ preserves smoothness and compact support.

**Directional derivatives preserve tests.** Proved result `test_dir`: Under the stated hypotheses, directional derivatives preserve scalar tests.

**Solenoidal fields kill gradient errors.** Proved result `slice_zero`: Under the stated hypotheses, solenoidal velocities kill gradient remainders.

**Far remainders have quadratic growth.** Proved result `far_bound`: Under the stated hypotheses, far Taylor remainders have quadratic growth.

**Remainders vanish outside larger support.** Proved result `zero_far`: Under the stated hypotheses, remainders vanish beyond enlarged support.

**Taylor remainders are jointly continuous.** Proved result `cont_pair`: For smooth f, its second-order Taylor remainder f(x+z)−f(x)−Df(x)[z]−½D²f(x)[z,z] is jointly continuous in x and z.

**Fixed-shift remainders are continuous.** Proved result `cont_slice`: For smooth f and fixed z, its second-order Taylor remainder is continuous as a function of x.

**A mixed product has power bounds.** Proved result `mul_le_pow_six`: For nonnegative a and b, ab≤a⁶+b²+b.

**Translated tests have uniform bounds.** Proved result `translate_bound`: Under the stated hypotheses, translated tests have uniform pairing bounds.

**Local and far powers give integrability.** Proved result `near_far`: A measurable scalar f is integrable on ℝ³ if |f(z)|≤C|z|^(−a) for |z|≤1 with a<3 and |f(z)|≤C|z|^(−b) for |z|≥1 with b>3.

**Natural and real powers combine.** Proved result `rpow_pow_add`: For t≥0, n a nonnegative integer and real r with r≠0 and r+n≠0, tʳtⁿ=t^(r+n).

**Fractional remainders pair integrably.** Proved result `prod_integrable`: If 1<α<3/2, u is locally integrable with ∫|u|⁶<∞ and φ is smooth with compact support, then |z|^(−3−2α)u(x)·R₂φ(x,z) is integrable over ℝ³×ℝ³, where R₂ subtracts the Taylor polynomial through order two.

**Velocities kill fractional gradients.** Proved result `power_zero`: Under the stated hypotheses, velocities annihilate fractional gradient tests.

**Source namespace:** `Breakdown.SteadyCert`.

**Drift plus power is solenoidal in L².** Proved result `driftPowerSolenoidal`: Under the stated assumptions, this establishes that for 1<α<5/4, the sum of the L² rotating drift and weak fractional power of a second-order field is solenoidal in L².

### Breakdown.FracCert.DriftSymbolWeak

Derives the Fourier weak drift identity from physical integration by parts, inverse-transform formulas and the negative-second-trace representation of velocity.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/DriftSymbolWeak.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.Internal.DriftSymbolWeak`.

**Complexification pairs with real parts.** Proved result `inner_complexifyVec`: For a real vector u and a complex vector z, the real inner product of u with z equals u·Re z.

**Fourier tests preserve real pairings.** Proved result `pairing`: Under the stated hypotheses, Fourier tests preserve real field pairings.

**Negative second traces belong to L².** Proved result `memLp_negSecondTrace`: For an admissible second-order field, −Δv belongs to L²(ℝ³).

**The flow adjoint vanishes off support.** Proved result `flowAdjoint_eq_zero`: The adjoint frequency drift of a test ψ vanishes at every frequency outside the closed support of ψ.

**Adjoint support stays within the test.** Proved result `support_flowAdjoint_subset`: Under the stated hypotheses, adjoint support stays inside test support.

**Closed adjoint support stays within test.** Proved result `tsupport_flowAdjoint_subset`: Under the stated hypotheses, closed adjoint support stays inside support.

**The axial turn is smooth.** Proved result `contDiff_axialTurn`: The real axial generator J(y₁,y₂,y₃)=(−y₂,y₁,0) is smooth. Source: `Breakdown.FracCert.DriftSymbolWeak:79`.

**The complex frequency turn is smooth.** Proved result `contDiff_freqTurn`: The complex axial generator J(z₁,z₂,z₃)=(−z₂,z₁,0) is smooth as a map between real vector spaces.

**The flow adjoint preserves smoothness.** Proved result `contDiff_flowAdjoint`: For smooth ψ, the frequency expression (1−1/(2α))ψ+(1/(2α))Dψ[ξ]−aDψ[Jξ]+aJψ is smooth for any real α and a.

**Smooth compact fields are Schwartz.** Proved result `exists_rapid`: Every smooth compactly supported complex vector field can be regarded as a Schwartz function with exactly the same pointwise values.

**The quadratic frequency-power formula.** Proved result `freqPow_two_eq`: The second frequency power is exactly (2π)²‖ξ‖².

**Inverse-square weights are smooth off 0.** Proved result `contDiff_scaled`: Under the stated hypotheses, inverse-square weighting stays smooth off zero.

**Real parts commute with derivatives.** Proved result `lineDeriv_postcomp`: Under the stated hypotheses, taking real parts commutes with derivatives.

**Coordinate squares give squared norm.** Proved result `sum_sq_inner`: For ξ∈ℝ³, the sum ∑ⱼ(ξ·eⱼ)² equals |ξ|².

**Fourier weights give negative traces.** Proved result `sum_second_invTransform`: Under the stated hypotheses, Fourier weights give negative second traces.

**Source namespace:** `Breakdown.SteadyCert`.

**Second-trace tests represent velocity.** Proved result `velocitySecondPhysical_of`: Under the stated assumptions, this establishes that for a second-order field and Schwartz symbols with Φ=(2π‖ξ‖)²Ψ, pairing velocity with the real inverse transform of Φ equals pairing the negative second trace with the real inverse transform of Ψ.

**Physical adjoints give Fourier drift.** Proved result `driftSymbolWeak_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and a second-order field with L² drift, the drift symbol pairs with every frequency test as the inverse-square-weighted second symbol paired with the flow adjoint of that test.

**Transport and inversion give the adjoint.** Proved result `driftAdjointPhysical_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and a second-order field with L² drift, pairing that drift with the real inverse transform of a Schwartz test equals pairing velocity with the real inverse transform of its frequency flow adjoint.

**Three pairing identities give weak drift.** Proved result `driftSymbolWeak_of_parts`: Under the stated assumptions, this establishes that for 1<α<5/4 and a second-order field with L² drift, the drift symbol pairs with every frequency test as the inverse-square-weighted second symbol paired with the flow adjoint of that test.

**Source namespace:** `Breakdown.SteadyCert.Internal.DriftSymbolWeakFreq`.

**Linear weights obey the derivative rule.** Proved result `hasFDerivAt_inner_smul`: For a Schwartz field χ and fixed m, D((x·m)χ(x))(y)[h]=(y·m)Dχ(y)[h]+(h·m)χ(y).

**Linear weights obey the product rule.** Proved result `lineDeriv_inner_smul`: Under the stated hypotheses, linear-weight derivatives obey the product rule.

**Inversion converts weighted derivatives.** Proved result `invTransform_inner_lineDeriv`: Under the stated hypotheses, Fourier inversion converts weighted derivatives.

**The complex turn as a linear map.** Definition `turnL`: This equips the complex frequency turn with its continuous complex linear map structure.

**The complex turn is (−z₂,z₁,0).** Proved result `turnL_apply`: The continuous complex-linear turn sends (z₁,z₂,z₃) to (−z₂,z₁,0), agreeing with the frequency axial generator.

**Fourier inversion commutes with turns.** Proved result `invTransform_turn`: For a Schwartz field f, inverse Fourier transformation commutes with the constant axial generator: the inverse transform of Jf is J applied to the inverse transform of f.

**Coordinates reconstruct each frequency.** Proved result `decomp`: Every frequency vector ξ has the expansion ξ=ξ₁e₁+ξ₂e₂+ξ₃e₃.

**Coordinates reconstruct the axial turn.** Proved result `decomp_turn`: The axial generator applied to ξ is Jξ=−ξ₂e₁+ξ₁e₂.

**Basis pairings give coordinates.** Proved result `inner_unit`: For each coordinate basis vector, ξ·eⱼ=ξⱼ.

**Real parts commute with axial turns.** Proved result `realVec_turn`: Taking the real part of a complex vector commutes with the axial generator: Re(Jz)=J(Re z).

**Real parts commute with differentiation.** Proved result `fderiv_realVec`: For a Schwartz field χ, D(Re χ)(y)[w]=Re(Dχ(y)[w]).

**Radial derivatives expand in coordinates.** Proved result `fderiv_self`: The radial derivative expands as Df(ξ)[ξ]=∑ⱼξⱼ∂ⱼf(ξ).

**Turn derivatives expand in coordinates.** Proved result `fderiv_turn`: The angular derivative generated by J satisfies Df(ξ)[Jξ]=−ξ₂∂₁f(ξ)+ξ₁∂₂f(ξ).

**Source namespace:** `Breakdown.SteadyCert`.

**Inversion converts the flow adjoint.** Proved result `flowAdjointInverse`: Under the stated assumptions, this establishes that taking the real inverse Fourier transform converts the frequency flow adjoint of a Schwartz test into the physical transport adjoint of its real inverse transform.

**Two physical identities give weak drift.** Proved result `driftSymbolWeak_of_two`: Under the stated assumptions, this establishes that for 1<α<5/4 and a second-order field with L² drift, the drift symbol pairs with every frequency test as the inverse-square-weighted second symbol paired with the flow adjoint of that test.

**Source namespace:** `Breakdown.SteadyCert.Internal.DriftSymbolWeakTransport`.

**The spatial turn as a linear map.** Definition `axialL`: This equips the spatial axial turn with its continuous real linear map structure.

**The spatial turn is (−x₂,x₁,0).** Proved result `axialL_apply`: The continuous spatial turn sends (x₁,x₂,x₃) to (−x₂,x₁,0), agreeing with the axial generator.

**Axial turns are skew adjoint.** Proved result `inner_axialTurn`: For u,w∈ℝ³, (Ju)·w=−u·Jw, so the axial generator is skew-adjoint.

**Source namespace:** `Breakdown.SteadyCert`.

**Linear transport gives the drift adjoint.** Proved result `driftTransportPairing_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and a second-order field with L² drift, its drift pairing with every Schwartz vector test equals the velocity pairing with the physical transport adjoint.

**Linear transport gives Fourier drift.** Proved result `driftSymbolWeak_of_transport`: Under the stated assumptions, this establishes that for 1<α<5/4 and a second-order field with L² drift, the drift symbol pairs with every frequency test as the inverse-square-weighted second symbol paired with the flow adjoint of that test.

**Source namespace:** `Breakdown.SteadyCert.Internal.DriftSymbolWeakLinear`.

**Linear maps expand in coordinates.** Proved result `clm_decomp`: For a bounded linear map L from ℝ³ into any real normed space, Lx=∑ₖxₖL(eₖ).

**Linear coordinates have temperate growth.** Proved result `hasTG`: Every coordinate of a linear vector field y↦Wy, together with all its derivatives, has at most polynomial growth.

**Coordinate weights have two derivatives.** Proved result `lineDeriv_coord_smul`: Under the stated hypotheses, coordinate-weight derivatives have two terms.

**Source namespace:** `Breakdown.SteadyCert`.

**Linear transport integrates by parts.** Proved result `linearTransportPair`: Under the stated assumptions, this establishes that for a second-order field and a Schwartz vector test, differentiation of the velocity along a linear field Wy transfers by integration by parts to the negative test derivative along Wy and the trace of W, with all stated pairings integrable.

**The drift has its weak Fourier identity.** Proved result `driftSymbolWeak`: Under the stated assumptions, this establishes that for 1<α<5/4 and a second-order field with L² drift, the drift symbol pairs with every frequency test as the inverse-square-weighted second symbol paired with the flow adjoint of that test.

### Breakdown.FracCert.DriftSymbolWeakParts

States the physical transport, Fourier inversion and second-trace pairing interfaces needed to identify the weak Fourier drift.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/DriftSymbolWeakParts.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert`.

**Drift transfers to the flow adjoint.** Proposition `DriftAdjointPhysicalStatement`: This proposition requires that for 1<α<5/4 and a second-order field with L² drift, pairing that drift with the real inverse transform of a Schwartz test equals pairing velocity with the real inverse transform of its frequency flow adjoint.

**Fourier second traces represent velocity.** Proposition `VelocitySecondPhysicalStatement`: This proposition requires that for a second-order field and Schwartz symbols with Φ=(2π‖ξ‖)²Ψ, pairing velocity with the real inverse transform of Φ equals pairing the negative second trace with the real inverse transform of Ψ.

**Weak Hessians pair with Schwartz tests.** Proposition `SecondTracePairingStatement`: This proposition requires that for a second-order field, pairing velocity with the negative second derivative sum of a Schwartz test equals pairing the negative second trace with that test.

**The physical transport adjoint.** Definition `transportAdjoint`: This defines the physical transport adjoint as (1−2/α)χ−Dχ(y)/(2α)−aDχ(Jy)+aJχ.

**Physical drift integrates by parts.** Proposition `DriftTransportPairingStatement`: This proposition requires that for 1<α<5/4 and a second-order field with L² drift, its drift pairing with every Schwartz vector test equals the velocity pairing with the physical transport adjoint.

**Inversion gives the transport adjoint.** Proposition `FlowAdjointInverseStatement`: This proposition requires that taking the real inverse Fourier transform converts the frequency flow adjoint of a Schwartz test into the physical transport adjoint of its real inverse transform.

**Linear transport integrates by parts.** Proposition `LinearTransportPairStatement`: This proposition requires that for a second-order field and a Schwartz vector test, differentiation of the velocity along a linear field Wy transfers by integration by parts to the negative test derivative along Wy and the trace of W, with all stated pairings integrable.

### Breakdown.FracCert.DriftWeakLimit

Identifies the drift of a weakly convergent correction using compact continuous tests and the inverse-radius weighted velocity limit.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/DriftWeakLimit.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.Internal.DriftWeakLimit`.

**Continuous compact vector fields.** Definition `IsBumpField`: This predicate requires a vector field to be continuous and compactly supported.

**Coordinate functions are continuous.** Proved result `coord_cont`: Each scalar coordinate function y↦yᵢ is continuous on ℝ³.

**The axial turn as a linear map.** Definition `turnL`: This defines the continuous axial turn sending (x₁,x₂,x₃) to (−x₂,x₁,0).

**The spatial turn is (−x₂,x₁,0).** Proved result `turnL_apply`: The continuous spatial turn sends (x₁,x₂,x₃) to (−x₂,x₁,0), agreeing with the axial generator.

**The axial turn is continuous.** Proved result `continuous_turn`: The axial generator J is a continuous linear map on ℝ³.

**The axial turn fixes zero.** Proved result `turn_zero`: The axial generator sends the zero vector to zero.

**Coordinates reconstruct each vector.** Proved result `vec_decomp`: Every x∈ℝ³ equals ∑ₖxₖeₖ.

**Coordinates reconstruct linear maps.** Proved result `clm_decomp`: For any linear map L on ℝ³, Lx=∑ₖxₖL(eₖ).

**Axial turns are skew adjoint.** Proved result `inner_turn`: For any vectors u and w, (Ju)·w=−u·Jw.

**Compact continuous fields belong to L².** Proved result `bump_memLp`: A continuous compactly supported vector field belongs to L²(ℝ³).

**Continuous weights retain compact fields.** Proved result `bump_smul`: Under the stated hypotheses, continuous weights preserve compact fields.

**Compact scalars give compact vectors.** Proved result `bump_const`: Under the stated hypotheses, compact scalar weights give compact vectors.

**Axial turns preserve compact fields.** Proved result `bump_turn`: Applying the axial generator to a continuous compactly supported vector field preserves continuity and compact support.

**Compact fields pair with local L¹ fields.** Proved result `pair_int`: If f is locally integrable and h is continuous with compact support, f·h is integrable on ℝ³.

**Second-order velocities are locally L¹.** Proved result `vel_li`: Under the stated hypotheses, second-order velocities are locally integrable.

**Gradient columns belong to L².** Proved result `col_memLp`: Every column of the weak gradient of an admissible second-order field belongs to L²(ℝ³).

**Gradient columns are locally integrable.** Proved result `col_li`: Every column of the weak gradient of an admissible second-order field is locally integrable.

**Drift pairings split by coordinate.** Proved result `drift_pair`: Under the stated hypotheses, drift pairings split into coordinate terms.

**Drift integrals split by coordinate.** Proved result `drift_int`: Under the stated hypotheses, drift integrals split into coordinate terms.

**Weighted limits give compact pairings.** Proved result `vel_tendsto`: Under the stated hypotheses, weighted weak limits give compact pairings.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak drift limits remain in L².** Proved result `driftWeakLimit_holds`: Under the stated assumptions, this establishes that under convergence of rotation rates and the stated simultaneous weak limits, the drift of the limiting second-order velocity is square integrable.

### Breakdown.FracCert.EmbedWeak

Embeds physical weak derivative data into the Fourier energy space, relating operator norms to coordinate energies and controlling the extended-valued norms.

This provides functional analysis or weak Fourier identities for the fractional certificate route; the source README distinguishes these fractional statements from the ordinary-dissipation results used by the paper.

Source: `lean/Breakdown/FracCert/EmbedWeak.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.EmbedWeak.Internal`.

**Basis vectors reconstruct linear maps.** Proved result `apply_eq_sum`: For a linear map L and vector w in ℝ³, Lw=∑ᵢwᵢL(eᵢ).

**Column norms bound operator norm.** Proved result `norm_le_sum`: The operator norm of a matrix L is at most the sum of the Euclidean norms of its three columns.

**Matrix energy bounds the operator norm².** Proved result `norm_sq_le`: Under the stated hypotheses, matrix energy bounds squared operator norm.

**Matrix energy gives L² operator norm.** Proved result `integrable_norm_sq`: Under the stated hypotheses, matrix energy gives integrable operator norm.

**The first finite term is below the sum.** Proved result `le_ofReal_add`: Under the stated hypotheses, a finite first term lies below the real sum.

**The second finite term is below the sum.** Proved result `le_ofReal_add'`: Under the stated hypotheses, a finite second term lies below the real sum.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak derivatives embed in energy space.** Proved result `embedWeak`: Under the stated assumptions, this establishes that a measurable divergence-free L⁶ velocity with measurable square-integrable weak gradient is represented by an energy-space element whose velocity and coordinate partial fields agree with those physical data almost everywhere.

### Breakdown.FracCert.FarFieldGradientFree

Uses the transverse projection in the heat-divergence symbol to prove that the rotated and scaled far-field integral annihilates gradient frequency tests.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/FarFieldGradientFree.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.FarFieldGradientFreeInternal`.

**All moments give a continuous profile.** Proved result `profileField_continuous`: A frequency-space profile with finite homogeneous Sobolev moments at every positive integer order has a continuous physical representative. Source: `Breakdown.FracCert.FarFieldGradientFree:21`.

**All moments give a bounded profile.** Proved result `profileField_bounded`: A frequency-space profile with all positive integer homogeneous Sobolev moments has a physical representative bounded everywhere by one finite constant C≥0. Source: `Breakdown.FracCert.FarFieldGradientFree:27`.

**Tensor squares preserve continuity.** Proved result `tensorSq_continuous`: For a continuous vector field V, the tensor square V⊗V is continuous. Source: `Breakdown.FracCert.FarFieldGradientFree:37`.

**Tensor squares have a squared bound.** Proved result `tensorSq_norm_le`: A pointwise bound |V|≤C with C≥0 gives the tensor bound |V⊗V|≤C². Source: `Breakdown.FracCert.FarFieldGradientFree:43`.

**The heat-divergence kernel is measurable.** Proved result `kernel_measurable`: Every component of the projected fractional heat-divergence kernel is measurable jointly in time and position.

**The heat-divergence kernel is integrable.** Proved result `kernel_integrable`: Assuming the projected-kernel decay estimate, each kernel component belongs to L¹(ℝ³) for α>0 and t>0.

**The total projected kernel mass.** Definition `kernelMass`: This defines the total time-one projected kernel mass by summing the L¹ norms of its twenty-seven scalar components.

**Kernel mass is nonnegative.** Proved result `kernelMass_nonneg`: The sum of the L¹ masses of all time-one projected kernel components is nonnegative. Source: `Breakdown.FracCert.FarFieldGradientFree:66`.

**Coordinate bounds control vector norms.** Proved result `norm_le_three`: Under the stated hypotheses, coordinate bounds control the vector norm.

**Kernel mass bounds heat divergence.** Proved result `heatDivConv_norm_le`: Assuming the kernel decay estimate and α,t>0, a tensor bounded by B has heat-divergence convolution bounded by 3BMαt^(−1/(2α)), where Mα is the sum of the componentwise time-one kernel masses. Source: `Breakdown.FracCert.FarFieldGradientFree:84`.

**Negative exponentials are below one.** Proved result `exp_neg_lt_one`: For τ>0, the exponential e^(−τ) is strictly below one. Source: `Breakdown.FracCert.FarFieldGradientFree:123`.

**Coordinate embeddings are measurable.** Proved result `single_measurable`: For each coordinate direction eᵢ, the map r↦reᵢ from ℝ to ℝ³ is measurable. Source: `Breakdown.FracCert.FarFieldGradientFree:127`.

**Variable rotations retain measurability.** Proved result `meas_rot`: Under the stated hypotheses, variable rotations preserve measurability.

**Heat convolutions vary measurably.** Proved result `meas_heat`: For a continuous tensor F, its heat-divergence convolution evaluated at measurable time and position maps is measurable on any measurable parameter space. Source: `Breakdown.FracCert.FarFieldGradientFree:148`.

**The far-field integrand is measurable.** Proved result `joint_measurable`: Under the stated hypotheses, the far-field integrand is jointly measurable.

**The far-field integrand has a time bound.** Proved result `integrand_norm_le`: Assuming kernel decay and α>0, the rotated and dilated heat-divergence integrand for a tensor bounded by B is at most 3BMα e^(−τ(1−1/(2α)))(1−e^(−τ))^(−1/(2α)) in norm for τ>0.

**Small heat times have a lower bound.** Proved result `one_sub_exp_ge`: Under the stated hypotheses, small heat times have a linear lower bound. Source: `Breakdown.FracCert.FarFieldGradientFree:201`.

**The time singularity is integrable.** Proved result `weight_integrable`: When α>1, the time weight e^(−τ(1−1/(2α)))(1−e^(−τ))^(−1/(2α)) is integrable on (0,∞). Source: `Breakdown.FracCert.FarFieldGradientFree:207`.

**Projected symbols are continuous off 0.** Proved result `symbol_continuousAt`: Under the stated hypotheses, the projected symbol is continuous off zero.

**Kernel pairings have a Fourier formula.** Proved result `kernel_pairing_step`: Assuming kernel decay, α,t,c>0 and a continuous compactly supported scalar symbol Q with Q(0)=0, pairing K(x−z) against the inverse transform of Q at R(cx) equals ∫Q(ξ)e^(2πi(cR⁻¹ξ)·z)k(−cR⁻¹ξ)dξ. Here K is one projected kernel component, k its multiplier and R an isometry; the frequency integrand is integrable.

**Transverse projections kill frequencies.** Proved result `real_contract`: For every frequency η and coordinate j, ∑ᵢ(δᵢⱼ−ηᵢηⱼ/|η|²)ηᵢ=0, including η=0 with the specified zero-denominator convention.

**The projected symbol kills frequencies.** Proved result `symbol_contract`: Contracting any projected heat-divergence symbol with its output frequency gives zero: ∑ᵢkᵢⱼₖ(η)ηᵢ=0.

**Inverse rotations expand in entries.** Proved result `symm_apply_eq_sum`: Under the stated hypotheses, inverse rotations expand by matrix entries.

**Symbol L¹ mass bounds inverse transforms.** Proved result `inverse_transform_norm_le`: For any scalar symbol Q, the absolute value of its inverse Fourier transform at y is at most ∫|Q(ξ)|dξ.

**Projected kernels annihilate gradients.** Proved result `kernel_core`: Under the stated hypotheses, projected kernels annihilate gradient tests.

**Heat convolutions annihilate gradients.** Proved result `conv_pair_zero`: Under the stated hypotheses, heat convolutions annihilate gradient tests.

**Far-field pairings pass through time.** Proved result `farFieldTimeSplit`: Under the stated assumptions, this establishes that for 1<α<5/4, pairing the far-field operator of a bounded continuous tensor with a continuous integrable test equals the negative time integral of the corresponding pairings of the rotated and scaled heat convolution.

**Rotated heat fields annihilate gradients.** Proved result `heatDivGradientFree`: Under the stated assumptions, this establishes that for α>1 and positive heat time and similarity scale, each rotated and scaled heat-divergence convolution of a bounded continuous tensor annihilates smooth compact frequency tests parallel to their frequencies.

**Source namespace:** `Breakdown.FracCert`.

**Far fields annihilate gradient tests.** Proved result `farFieldGradientFree`: Under the stated assumptions, this establishes that for 1<α<5/4, the far field of a profile tensor square with all moments annihilates real-symmetric smooth annular frequency tests parallel to their frequencies.

### Breakdown.FracCert.FarFieldGradientFreeParts

States the time-interchange and projected-gradient orthogonality contracts used to show the far-field term is solenoidal.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/FarFieldGradientFreeParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert`.

**Far-field pairings pass through time.** Proposition `FarFieldTimeSplitStatement`: This proposition requires that for 1<α<5/4, pairing the far-field operator of a bounded continuous tensor with a continuous integrable test equals the negative time integral of the corresponding pairings of the rotated and scaled heat convolution.

**Rotated heat fields annihilate gradients.** Proposition `HeatDivGradientFreeStatement`: This proposition requires that for α>1 and positive heat time and similarity scale, each rotated and scaled heat-divergence convolution of a bounded continuous tensor annihilates smooth compact frequency tests parallel to their frequencies.

### Breakdown.FracCert.FarFieldPairing

Matches the physical far-field integral to the nonlinear mild pairing by transposing the heat-divergence kernel and integrating the convection term by parts.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/FarFieldPairing.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.FarFieldPairingInternal`.

**All moments give a continuous profile.** Proved result `field_continuous`: Finite homogeneous Sobolev moments of every positive integer order make the profile's physical representative continuous.

**All moments give a bounded profile.** Proved result `field_bounded`: Finite homogeneous Sobolev moments of every positive integer order give a uniform finite bound on the profile's physical representative.

**Tensor squares preserve continuity.** Proved result `tensor_continuous`: If V is continuous on ℝ³, so is the tensor field V⊗V.

**Tensor squares have a squared bound.** Proved result `tensor_norm_le`: If C≥0 bounds |V| everywhere, then C² bounds |V⊗V| everywhere.

**Nice fields are continuous and in L¹.** Proved result `nice_props`: Under the stated hypotheses, nice fields are continuous and integrable.

**Heat continuity gives continuity.** Proved result `integrand_continuousOn`: Under the stated hypotheses, heat continuity gives integrand continuity.

**Similarity moves across pairings.** Proved result `change_vars`: Under the stated hypotheses, similarity moves across integral pairings.

**Source namespace:** `Breakdown.FracCert`.

**Heat pairings give far-field identities.** Proved result `farFieldPairing_of`: Under the stated assumptions, this establishes that for 1<α<5/4, the far field of a profile tensor square with all moments pairs against each nice test as the negative positive-time integral of its trilinear pairing with the heat-evolved similarity-adjoint test.

**Source namespace:** `Breakdown.FracCert.FarFieldPairingInternal`.

**Coordinate magnitudes are norm bounded.** Proved result `coord_abs_le`: Every coordinate of a vector w∈ℝ³ satisfies |wₖ|≤|w|.

**Product magnitudes obey product bounds.** Proved result `abs_mul_le'`: Bounds |a|≤A and |b|≤B imply |ab|≤AB.

**Bounded continuous factors preserve L¹.** Proved result `integrable_bdd`: Multiplying an integrable scalar function g by a bounded continuous scalar function f preserves integrability.

**Coordinates preserve continuity.** Proved result `coord_continuous`: Under the stated hypotheses, continuous fields have continuous coordinates.

**Coordinates inherit vector derivatives.** Proved result `coord_hasFDerivAt`: If a vector field f is differentiable at x, the derivative of its kth coordinate is h↦(Df(x)[h])ₖ.

**Derivatives equal coordinate entries.** Proved result `coord_fderiv`: Under the stated hypotheses, coordinate derivatives equal vector entries.

**Coordinates preserve integrability.** Proved result `coord_integrable`: Under the stated hypotheses, integrable fields have integrable coordinates.

**Derivative entries are integrable.** Proved result `dcoord_integrable`: Under the stated hypotheses, integrable derivatives have integrable entries.

**Convection integrates by coordinates.** Proved result `parts_jk`: Under the stated hypotheses, convection admits coordinate integration by parts.

**Source namespace:** `Breakdown.FracCert`.

**Trilinear terms integrate by parts.** Proved result `trilinearByParts`: Under the stated assumptions, this establishes that for an energy-space element with all moments, the trilinear pairing with a nice test equals minus the sum of the velocity tensor entries paired with the corresponding test derivatives.

**Transposition gives the heat pairing.** Proved result `heatDivPairing_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and 0< t<1, pairing heat divergence of a profile tensor square with a nice test equals its trilinear pairing with the heat-evolved test.

**Kernel transpose gives integral duality.** Proved result `heatDivTranspose_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and 0< t<1, pairing heat divergence of a bounded continuous tensor with a nice test equals the negative tensor pairing with the derivatives of the heat-evolved test.

**Heat duality gives the far-field pairing.** Proved result `farFieldPairing_of_transpose`: Under the stated assumptions, this establishes that for 1<α<5/4, the far field of a profile tensor square with all moments pairs against each nice test as the negative positive-time integral of its trilinear pairing with the heat-evolved similarity-adjoint test.

**Kernel duality gives far-field pairings.** Proved result `farFieldPairing_of_kernel`: Under the stated assumptions, this establishes that for 1<α<5/4, the far field of a profile tensor square with all moments pairs against each nice test as the negative positive-time integral of its trilinear pairing with the heat-evolved similarity-adjoint test.

**Source namespace:** `Breakdown.FracCert.FarFieldPairingInternal`.

**Fourier inversion respects coordinates.** Proved result `coord_inverseTransform`: Under the stated hypotheses, Fourier inversion commutes with coordinates.

**Real vector parts agree coordinatewise.** Proved result `realVec_coord`: Taking the real part of a complex vector acts coordinatewise: (Re w)ᵢ=Re(wᵢ).

**Source namespace:** `Breakdown.FracCert`.

**Kernel transposes are heat derivatives.** Proved result `kernelTranspose`: Under the stated assumptions, this establishes that for 1<α<5/4 and 0< t<1, summing kernel component pairings with a nice test gives the negative corresponding derivative of the fractional heat-evolved test.

**Heat regularity gives far-field pairings.** Proved result `farFieldPairing_of_regular`: Under the stated assumptions, this establishes that for 1<α<5/4, the far field of a profile tensor square with all moments pairs against each nice test as the negative positive-time integral of its trilinear pairing with the heat-evolved similarity-adjoint test.

### Breakdown.FracCert.FarFieldPairingParts

States the heat-kernel transpose and trilinear integration-by-parts identities needed to express far-field pairings as the nonlinear mild integral.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/FarFieldPairingParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert`.

**Heat divergence gives trilinear pairings.** Proposition `HeatDivPairingStatement`: This proposition requires that for 1<α<5/4 and 0< t<1, pairing heat divergence of a profile tensor square with a nice test equals its trilinear pairing with the heat-evolved test.

**Heat divergence transfers to tests.** Proposition `HeatDivTransposeStatement`: This proposition requires that for 1<α<5/4 and 0< t<1, pairing heat divergence of a bounded continuous tensor with a nice test equals the negative tensor pairing with the derivatives of the heat-evolved test.

**Trilinear terms transfer to test fields.** Proposition `TrilinearByPartsStatement`: This proposition requires that for an energy-space element with all moments, the trilinear pairing with a nice test equals minus the sum of the velocity tensor entries paired with the corresponding test derivatives.

**Kernel transposes are heat derivatives.** Proposition `KernelTransposeStatement`: This proposition requires that for 1<α<5/4 and 0< t<1, summing kernel component pairings with a nice test gives the negative corresponding derivative of the fractional heat-evolved test.

### Breakdown.FracCert.FarFieldWeighted

Proves weighted L² integrability of the profile far field using a positive kernel majorant, weighted Cauchy-Schwarz, affine changes of variables and the profile L⁶ bound.

This develops the smoothness, far-field representation or spatial decay of the fractional extension, supporting conversion of a weak fractional profile to a classical decaying solution; no numbered paper theorem correspondence is asserted.

Source: `lean/Breakdown/FracCert/FarFieldWeighted.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.FarFieldWeightedInternal`.

**The projected heat kernel has decay.** Proved result `kernelDecayHolds`: Under the stated assumptions, this establishes that for α>0, every positive-time projected heat-divergence kernel component is smooth and its nth derivative is bounded by C(t^(1/(2α))+‖x‖)^(−4−n).

**The projected heat kernel has scaling.** Proved result `kernelScalingHolds`: Under the stated assumptions, this establishes that for α>0 and t>0, the projected kernel is real, integrable and in L³⁄², obeys the t^(−2/α) spatial rescaling, and has L¹ and L³⁄² norms scaling respectively by t^(−1/(2α)) and t^(−1/α).

**A positive heat-kernel majorant.** Definition `kk`: This defines an extended nonnegative kernel majorant by summing the norms of all components of the rescaled time-one projected heat-divergence kernel.

**The transformed heat time is positive.** Proved result `t_pos`: For τ>0, the heat time 1−e^(−τ) is positive. Source: `Breakdown.FracCert.FarFieldWeighted:32`.

**The majorant sums kernel component norms.** Proved result `kk_eq`: For α,τ>0, the nonnegative kernel majorant at z equals the sum of the absolute values of all projected heat-divergence kernel components at time 1−e^(−τ).

**Positive-time kernels are continuous.** Proved result `kernel_cont`: For α>0 and t>0, each projected heat-divergence kernel component is continuous in space.

**The kernel majorant is measurable.** Proved result `kk_meas`: Under the stated hypotheses, the kernel majorant is jointly measurable.

**Each kernel majorant slice is measurable.** Proved result `kk_meas_z`: For α>0 and every τ, the kernel majorant is measurable in its spatial argument.

**Majorant mass follows heat scaling.** Proved result `kk_lintegral`: For α,τ>0, the spatial mass of the kernel majorant equals (1−e^(−τ))^(−1/(2α)) times the sum of the componentwise time-one kernel masses.

**Coordinate norms bound the vector norm.** Proved result `enorm_le_sum_comp`: For v∈ℝ³, |v|≤∑ᵢ|vᵢ|.

**The majorant bounds heat convolution.** Proved result `heat_bound`: For α,τ>0 and a continuous tensor F, the norm of its heat-divergence convolution at x is bounded by ∫K(τ,z)|F(x−z)|dz, where K is the summed kernel majorant; the bound allows an infinite right side.

**Inverse rotation negates the angle.** Proved result `rot_symm`: The inverse of axial rotation by θ is axial rotation by −θ.

**A double integral bounds the far field.** Proved result `pointwise`: Under the stated hypotheses, a positive double integral bounds the far field.

**The affine argument is continuous.** Proved result `arg_cont`: Under the stated hypotheses, the affine convolution argument is continuous.

**Affine changes give the volume factor.** Proved result `lintegral_affine`: For a measurable nonnegative g, nonzero c, an isometry R and any translation z, ∫g(cRy−z)dy=|c|⁻³∫g(x)dx, with infinite integrals allowed.

**Weighted Cauchy-Schwarz bounds integrals.** Proved result `cst_weighted`: For measurable nonnegative u,v,ψ satisfying uv=m², (∫mψ dν)²≤(∫u dν)(∫vψ² dν), with nonnegative integrals permitted to be infinite.

**Heat time has a rational lower bound.** Proved result `t_lower`: For τ>0, the transformed heat time obeys 1−e^(−τ)≥τ/(1+τ).

**Heat-time powers have bounds.** Proved result `t_pow_le`: Under the stated hypotheses, heat-time singularities have power bounds.

**The weighted kernel measure is finite.** Proved result `lam_finite`: For 1<α<5/4, the space-time integral of e^(−τ(1−1/α)) times the nonnegative projected-kernel majorant is finite over τ>0 and z∈ℝ³.

**The similarity amplitude factor.** Definition `aA`: This defines the similarity amplitude exp(−τ)^(1−1/(2α)).

**The similarity spatial scale.** Definition `cC`: This defines the similarity spatial scale exp(−τ)^(1/(2α)).

**The transformed tensor magnitude.** Definition `psi`: This defines the extended norm of the tensor evaluated at the rotated, scaled spatial point minus the convolution displacement.

**The amplitude-weighted kernel measure.** Definition `mm`: This defines the positive kernel density as the product of the similarity amplitude and the scalar kernel majorant.

**The inverse-scale kernel weight.** Definition `m1`: This defines the first Cauchy-Schwarz weight as the kernel majorant times the similarity amplitude divided by the spatial scale.

**The direct-scale kernel weight.** Definition `m2`: This defines the second Cauchy-Schwarz weight as the kernel majorant times the similarity amplitude and spatial scale.

**The amplitude factor is measurable.** Proved result `aA_meas`: The amplitude A(τ)=e^(−τ(1−1/(2α))) is measurable as a function of the space-time parameter (τ,z), for every α.

**The spatial scale is measurable.** Proved result `cC_meas`: The spatial scale C(τ)=e^(−τ/(2α)) is measurable as a function of (τ,z), for every α.

**The spatial scale is positive.** Proved result `cC_pos`: The spatial scale e^(−τ/(2α)) is strictly positive for every α and τ.

**The amplitude factor is nonnegative.** Proved result `aA_nonneg`: The amplitude e^(−τ(1−1/(2α))) is nonnegative for every α and τ.

**The kernel measure weight is measurable.** Proved result `mm_meas`: For α>0, the product of the similarity amplitude and the nonnegative kernel majorant is measurable in (τ,z).

**The inverse-scale weight is measurable.** Proved result `m1_meas`: For α>0, dividing the similarity amplitude by the spatial scale and multiplying by the kernel majorant gives a measurable space-time weight.

**The direct-scale weight is measurable.** Proved result `m2_meas`: For α>0, multiplying the similarity amplitude, spatial scale and kernel majorant gives a measurable space-time weight.

**The transformed tensor is measurable.** Proved result `psi_meas`: For α>0 and continuous F, the transformed tensor norm |F(e^(−τ/(2α))R₋ₐτy−z)| is jointly measurable in y,τ,z.

**The split weights recover the square.** Proved result `huv`: Writing A for the nonnegative amplitude, C>0 for the spatial scale and K for the kernel majorant, the split weights satisfy (AK/C)(ACK)=(AK)² pointwise.

**The cubic Jacobian cancels the scale.** Proved result `real_id`: For C>0 and real A, the Jacobian identity AC|C⁻³|^(2/3)=A/C holds.

**The kernel measure bounds the far field.** Proved result `pointwise'`: For α>0 and continuous F, the far-field output at y is bounded in norm by the nonnegative space-time integral of A(τ)K(τ,z)|F(C(τ)R₋ₐτy−z)|; infinite bounds are allowed.

**The inverse-radius weight lies in L⁶.** Proved result `weight_six`: The nonnegative integral ∫(1+|y|)⁻⁶dy is finite on ℝ³.

**L³ tensors give weighted L² far fields.** Proved result `hbase`: For 1<α<5/4, the far-field output of a continuous tensor F∈L³ satisfies ∫(1+|y|)⁻²|V(y)|²dy<∞.

**All moments give a continuous profile.** Proved result `profile_cont`: A frequency-space profile with every positive integer homogeneous Sobolev moment has a continuous physical representative.

**All moments give an L⁶ profile.** Proved result `profile_six`: A frequency-space profile with every positive integer homogeneous Sobolev moment has a physical representative in L⁶(ℝ³).

**Tensor squares preserve continuity.** Proved result `tensor_cont`: Continuity of V implies continuity of its tensor square V⊗V.

**Velocity squared bounds the tensor norm.** Proved result `tensor_bound`: Under the stated hypotheses, tensor norm is bounded by velocity squared.

**L⁶ velocities give L³ tensors.** Proved result `tensor_three`: If V∈L⁶(ℝ³), then ∫|V⊗V|³ is finite.

**A rescaled real heat-kernel component.** Definition `kf`: This defines a real component of the heat kernel using the explicit rescaling of its time-one Fourier inverse.

**The rescaled component is measurable.** Proved result `kf_meas`: Under the stated hypotheses, the rescaled kernel component is measurable.

**Rescaling recovers the heat kernel.** Proved result `kf_eq`: Under the stated hypotheses, the rescaled component equals the heat kernel.

**The componentwise heat convolution.** Definition `hform`: This defines the componentwise heat-divergence convolution using the rescaled real kernel formula.

**The components give heat divergence.** Proved result `hform_eq`: Under the stated hypotheses, the component formula equals heat divergence.

**The heat convolution is measurable.** Proved result `hform_meas`: Under the stated hypotheses, the heat convolution formula is measurable.

**The rotated similarity integrand.** Definition `gform`: This defines the joint spatial-time far-field integrand by composing the componentwise convolution with the similarity rotation, scale and amplitude.

**Similarity gives the integrand formula.** Proved result `g_eq`: Under the stated hypotheses, the similarity formula equals the integrand.

**The similarity integrand is measurable.** Proved result `gform_meas`: For α>0 and continuous F, the rotated similarity-time heat-divergence integrand is jointly measurable in the spatial point and time.

**The far-field operator is measurable.** Proved result `far_meas`: For α>0 and continuous F, integrating the similarity-time heat-divergence expression gives a measurable far-field vector field.

**Source namespace:** `Breakdown.FracCert`.

**The far field has weighted L² size.** Proved result `farFieldWeighted`: Under the stated assumptions, this establishes that for 1<α<5/4, the far-field operator applied to the tensor square of a profile with all moments belongs to L² after multiplication by (1+‖y‖)⁻¹.

### Breakdown.FracCert.FlowDeriv

Differentiates the rotation and dilation flow on test functions, which supplies the weak drift pairing identity.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FlowDeriv.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.Internal.FlowDeriv`.

**Frequency turns preserve scaling.** Proved result `freqTurn_smul`: For real r and a complex vector z, J(rz)=rJz.

**Frequency turns preserve differences.** Proved result `freqTurn_sub`: For complex vectors z and w, J(z−w)=Jz−Jw.

**Axial turns preserve differences.** Proved result `axialTurn_sub`: For real vectors z and w, J(z−w)=Jz−Jw. Source: `Breakdown.FracCert.FlowDeriv:25`.

**Frequency turns do not increase norms.** Proved result `norm_freqTurn_le`: For a complex vector z, the axial generator satisfies |Jz|≤|z|.

**Axial turns do not increase norms.** Proved result `norm_axialTurn_le`: For a real vector z, the axial generator satisfies |Jz|≤|z|. Source: `Breakdown.FracCert.FlowDeriv:36`.

**Frequency turns are continuous.** Proved result `continuous_freqTurn`: The axial generator on complex three-dimensional vectors is continuous.

**Axial turns are continuous.** Proved result `continuous_axialTurn`: The axial generator on real three-dimensional vectors is continuous.

**Complex rotations expand in a basis.** Proved result `rotC_eq_sum`: For an isometry R of ℝ³ and z∈ℂ³, its complex-linear extension satisfies Rz=∑ⱼzⱼReⱼ.

**Rotating vectors obey the chain rule.** Proved result `hasDerivAt_rotC`: If θ(t) and z(t) are differentiable, d(Rθ(t)z(t))/dt=θ′(t)J(Rθ(t)z(t))+Rθ(t)z′(t).

**Spatial derivatives follow the flow.** Proved result `fderiv_flowPush`: For smooth ψ, differentiating its transported frequency test in direction v applies the linear frequency flow to v before Dψ, then applies the same rotated amplitude to the output.

**Time derivatives give the adjoint.** Proved result `hasDerivAt_flowPush`: For smooth ψ, the time derivative of its transported frequency test equals the adjoint dilation-and-rotation drift applied to that transported test.

**The adjoint vanishes off support.** Proved result `flowAdjoint_of_notMem`: For any test φ, the adjoint frequency drift is zero at every point outside the closed support of φ.

**The flow adjoint is continuous.** Proved result `continuous_flowAdjoint`: For smooth φ, its adjoint frequency drift is continuous for every α and angular rate a.

**Values and derivatives bound the adjoint.** Proved result `norm_flowAdjoint_le`: If |φ(ξ)|≤A and |Dφ(ξ)[v]|≤B|v| with B≥0, the adjoint frequency drift has norm at most (|1−1/(2α)|+|a|)A+(|1/(2α)|+|a|)B|ξ|.

**The transported adjoint has a bound.** Proved result `norm_flowAdjoint_push_le`: If smooth ψ satisfies |ψ|≤C₀ and |Dψ|≤C₁, its transported adjoint at time s has norm at most (|1−1/(2α)|+|a|)e^(s(1−1/(2α)))C₀+(|1/(2α)|+|a|)eˢC₁|ξ|.

**Source namespace:** `Breakdown.SteadyCert`.

**The flow pairing is differentiable.** Proved result `flowDeriv`: Under the stated assumptions, this establishes that for 1<α<5/4 and a field whose first frequency weight is in L², pairing with the transported test is differentiable in time and its derivative pairs the field with the flow adjoint of that test.

### Breakdown.FracCert.FlowPairing

Builds the strongly continuous rotation and dilation flow on L² and derives its weak integral and pairing identities.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FlowPairing.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Rotation and dilation of frequencies.** Definition `flowLin`: This defines the frequency transformation ξ ↦ exp(−gt) R(at)ξ as a continuous linear equivalence.

**Rotation and scaling of field values.** Definition `flowValue`: This defines the value transformation z ↦ exp(ct) R(−at)z on complex vectors.

**Pullback along the frequency flow.** Definition `flowPull`: This defines the transported field by evaluating it along the frequency transformation and applying the value transformation.

**The flow operator on L².** Definition `flowOp`: This defines the bounded linear operator on L² induced by the frequency and value transformations.

**The L² flow is continuous.** Proposition `FlowContinuityStatement`: This proposition requires that for every choice of the three flow rates, the rotation and dilation action on each L² field is continuous in time.

**Weak drift integrates along the flow.** Proposition `FlowIntegralStatement`: This proposition requires that for 1<α<5/4, a weighted L² field with weak flow derivative D has transported increment equal almost everywhere to the time integral of the L² flow applied to D.

**Source namespace:** `Breakdown.SteadyCert.Internal.FlowPairing`.

**The frequency flow has a formula.** Proved result `flowLin_apply`: The frequency flow acts by ξ↦e^(−gt)Rₐtξ, combining radial dilation with axial rotation.

**The L² flow agrees almost everywhere.** Proved result `flowOp_ae`: The L² flow of f has, almost everywhere, the pointwise representative e^(ct)R₋ₐtf(e^(−gt)Rₐtξ).

**Field norms scale exponentially.** Proved result `norm_flowValue`: The rotated amplitude map z↦e^(ct)R₋ₐtz multiplies every vector norm by e^(ct).

**Raising the weight multiplies by exp.** Proved result `flowValue_succ`: Increasing the amplitude exponent from c to c+1 multiplies the transported vector value by eᵗ.

**The identity rotation fixes vectors.** Proved result `rotC_refl`: The complex extension of the identity isometry fixes every complex vector.

**The flow starts at the identity.** Proved result `flowOp_zero`: At time t=0, the frequency flow operator fixes every L² field.

**The frequency flow preserves null sets.** Proved result `qmp_flowLin`: The dilation-rotation map ξ↦e^(−gt)Rₐtξ is measurable and takes preimages of Lebesgue-null sets to null sets.

**Integrability survives the flow.** Proved result `integrable_flowLin`: If F∈L¹(ℝ³), composing F with ξ↦e^(−gt)Rₐtξ preserves integrability.

**Integrals acquire the Jacobian factor.** Proved result `integral_flowLin`: For the dilation-rotation flow, ∫F(e^(−gt)Rₐtξ)dξ=e^(3gt)∫F(ξ)dξ.

**Frequency powers scale along the flow.** Proved result `freqPow_flowLin`: Along the frequency flow, (2π|e^(−gt)Rₐtξ|)ˢ=e^(−gts)(2π|ξ|)ˢ for every real s.

**The fractional energy is integrable.** Proved result `integrable_weight`: For α≥1, if (2π|ξ|)h and (2π|ξ|)^(2α)h belong to L², then ∫(2π|ξ|)^(2α)|h|² is finite.

**Frequency norms scale exponentially.** Proved result `norm_flowLin`: The dilation-rotation flow satisfies |e^(−gt)Rₐtξ|=e^(−gt)|ξ|.

**L² norms square to integrals.** Proved result `norm_sq_L2`: For an L² complex vector field F, ‖F‖₂²=∫|F(ξ)|²dξ.

**Flow norms scale exponentially.** Proved result `norm_flowOp`: The flow f(ξ)↦e^(ct)R₋ₐtf(e^(−gt)Rₐtξ) multiplies its L² norm by e^((c+3g/2)t).

**Moving complex rotations are continuous.** Proved result `continuous_rotC`: If z(t) is continuous, so is its rotation R₋ₐtz(t) for a fixed angular rate a.

**Moving field values are continuous.** Proved result `continuous_flowValue`: If z(t) is continuous, then e^(ct)R₋ₐtz(t) is continuous for fixed a and c.

**Frequency trajectories are continuous.** Proved result `continuous_flowLin`: For fixed g,a and ξ, the frequency trajectory t↦e^(−gt)Rₐtξ is continuous.

**Compact fields have continuous orbits.** Proved result `tendsto_flowOp_of_compact`: If an L² field has a continuous compactly supported representative, its dilation-rotation orbit is continuous in the L² norm at every time.

**The quadratic frequency weight.** Proved result `freqPow_two_eq`: The second radial frequency power is (2π)²‖ξ‖².

**The second weight is the first squared.** Proved result `freqPow_two_mul`: The radial weights satisfy (2π|ξ|)²=(2π|ξ|)(2π|ξ|).

**The first frequency weight is continuous.** Proved result `continuous_freqPow_one`: The first frequency weight ξ↦2π|ξ| is continuous on ℝ³.

**The second frequency weight is smooth.** Proved result `contDiff_freqPow_two`: The second frequency weight ξ↦(2π|ξ|)² is smooth on ℝ³, including at zero.

**Weighted L² survives the flow.** Proved result `memLp_weight_pull`: If (2π|ξ|)h∈L², the same weighted L² property holds after applying any dilation-rotation flow with exponential amplitude.

**The quadratic weight is locally L¹.** Proved result `locallyIntegrable_weight_two`: If (2π|ξ|)f∈L², then (2π|ξ|)²f is locally integrable in frequency space.

**Source namespace:** `Breakdown.SteadyCert`.

**Flow identities give the energy pairing.** Proved result `flowPairing_of`: Under the stated assumptions, this establishes that for 1<α<5/4, an L² weak flow derivative D of a field h with its first and 2α frequency weights in L² satisfies the identity ∫⟨D,(2π‖ξ‖)^(2α)h⟩=(3/2−5/(4α))∫(2π‖ξ‖)^(2α)‖h‖².

**The L² flow is continuous.** Proved result `flowContinuity`: Under the stated assumptions, this establishes that for every choice of the three flow rates, the rotation and dilation action on each L² field is continuous in time.

**The integral gives the energy pairing.** Proved result `flowPairing_of_integral`: Under the stated assumptions, this establishes that for 1<α<5/4, an L² weak flow derivative D of a field h with its first and 2α frequency weights in L² satisfies the identity ∫⟨D,(2π‖ξ‖)^(2α)h⟩=(3/2−5/(4α))∫(2π‖ξ‖)^(2α)‖h‖².

**The flow identity holds on tests.** Proposition `FlowTestStatement`: This proposition requires that for 1<α<5/4, the transported increment of a weighted L² field with weak flow derivative D and the integrated flow of D have equal pairings against every frequency test.

**Test identities identify the integral.** Proved result `flowIntegral_of_test`: Under the stated assumptions, this establishes that for 1<α<5/4, a weighted L² field with weak flow derivative D has transported increment equal almost everywhere to the time integral of the L² flow applied to D.

**Test identities give the pairing.** Proved result `flowPairing_of_test`: Under the stated assumptions, this establishes that for 1<α<5/4, an L² weak flow derivative D of a field h with its first and 2α frequency weights in L² satisfies the identity ∫⟨D,(2π‖ξ‖)^(2α)h⟩=(3/2−5/(4α))∫(2π‖ξ‖)^(2α)‖h‖².

**Source namespace:** `Breakdown.SteadyCert.Internal.FlowPairing`.

**Rotation moves across inner products.** Proved result `real_inner_rotC`: For the complex extension of an isometry R, the real inner products satisfy ⟨Rw,z⟩=⟨w,R⁻¹z⟩.

**Reversing rates inverts the flow.** Proved result `flowLin_inv`: Reversing both the dilation rate and the angular rate inverts the frequency map: e^(gt)R₋ₐt(e^(−gt)Rₐtξ)=ξ.

**The flow moves across integral pairings.** Proved result `integral_inner_flowPull`: Moving the dilation-rotation flow across an integrated real inner product reverses its spatial rates g,a and changes its amplitude exponent c to c+3g.

**Inverse-weighted tests are continuous.** Proved result `continuous_invWeight`: If ψ is smooth, compactly supported and zero near ξ=0, then ψ(ξ)/(2π|ξ|) is continuous on all of ℝ³.

**Weighted fields pair integrably.** Proved result `integrable_inner_test`: If (2π|ξ|)f∈L² and ψ is a smooth compactly supported test away from ξ=0, then ⟨f,ψ⟩ is integrable.

**The flow preserves frequency tests.** Proved result `isFreqTest_flowPull`: Dilation, axial rotation and constant exponential amplitude preserve smooth compactly supported frequency tests whose support avoids zero.

**Source namespace:** `Breakdown.SteadyCert`.

**The adjoint transport of tests.** Definition `flowPush`: This defines test transport with dilation rate −1/(2α), rotation rate −a and amplitude rate 1−1/(2α), the rates adjoint to the profile flow.

**The flow pairing is differentiable.** Proposition `FlowDerivStatement`: This proposition requires that for 1<α<5/4 and a field whose first frequency weight is in L², pairing with the transported test is differentiable in time and its derivative pairs the field with the flow adjoint of that test.

**Derivatives give the test identity.** Proved result `flowTest_of_deriv`: Under the stated assumptions, this establishes that for 1<α<5/4, the transported increment of a weighted L² field with weak flow derivative D and the integrated flow of D have equal pairings against every frequency test.

**Derivatives give the energy pairing.** Proved result `flowPairing_of_deriv`: Under the stated assumptions, this establishes that for 1<α<5/4, an L² weak flow derivative D of a field h with its first and 2α frequency weights in L² satisfies the identity ∫⟨D,(2π‖ξ‖)^(2α)h⟩=(3/2−5/(4α))∫(2π‖ξ‖)^(2α)‖h‖².

### Breakdown.FracCert.FreeBounds

Obtains coercive L² estimates for the fractional free operator from Fourier energy and drift identities.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeBounds.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**L² norms square to integrals.** Proved result `lp_norm_sq`: For any real inner-product-space-valued L² function f, ‖f‖₂²=∫|f|².

**Complexification preserves norms.** Proved result `norm_complexifyVec_eq`: Viewing a real vector as a complex vector leaves its Euclidean norm unchanged.

**Complexification preserves L² energy.** Proved result `integral_norm_sq_complexify`: Viewing a real L² vector field as complex-valued leaves its squared-norm integral unchanged.

**The L² representative agrees a.e..** Proved result `toLpOrZero_coe`: For a square-integrable real vector field, conversion to L² followed by taking a representative agrees with the original field almost everywhere.

**Fourier transform preserves L² energy.** Proved result `integral_fieldSymbol_sq`: For a real vector field P∈L², its Fourier transform has the same squared-norm integral as P.

**The trace is bounded by matrix entries.** Proved result `secondTrace_sq_le`: For a vector-valued bilinear form H, |∑ᵢH(eᵢ,eᵢ)|²≤3∑ᵢ,ⱼ|H(eᵢ,eⱼ)|².

**The negative trace lies in L².** Proved result `memLp_negSecondTrace`: For an admissible second-order field v, the negative trace of its weak Hessian belongs to L².

**L² fields pair integrably.** Proved result `integrable_pair`: For X,Y∈L²(ℝ³;ℝ³), the pointwise pairing X·Y is integrable. Source: `Breakdown.FracCert.FreeBounds:73`.

**Integral pairings equal L² pairings.** Proved result `pair_eq_inner`: For square-integrable representatives X and Y, their spatial integral ∫X·Y is their Hilbert-space L² inner product. Source: `Breakdown.FracCert.FreeBounds:79`.

**The concrete L² norm is the Lp norm.** Proved result `l2Norm_eq_norm`: For X∈L², √(∫|X|²) agrees with its L² norm.

**Cauchy-Schwarz bounds the pairing.** Proved result `abs_pair_le`: For X,Y∈L², |∫X·Y|≤‖X‖₂‖Y‖₂. Source: `Breakdown.FracCert.FreeBounds:94`.

**Two frequency weights dominate one.** Proved result `pointwise_le`: For nonzero ξ, nonnegative β, and nonnegative s, the quantity s is at most s/(2π‖ξ‖)² plus (2π‖ξ‖)^(2β)s.

**Almost every frequency is nonzero.** Proved result `ae_ne_zero`: The singleton frequency {0} has Lebesgue measure zero, so ξ≠0 almost everywhere. Source: `Breakdown.FracCert.FreeBounds:118`.

**Gradient and power energies bound trace.** Proved result `trace_le`: Assuming the gradient and trace Fourier energy identities, integrability of the inverse-square-weighted trace symbol, an L² power whose symbol is (2π‖ξ‖)^(2α−2) times the negative-second-trace symbol, and α≥1, the trace's squared L² norm is at most gradient energy plus the power's squared L² norm.

**Squared norms split with a cross term.** Proved result `sq_split`: If X,Y∈L² and Z=X+Y almost everywhere, then ∫|Z|²=∫|X|²+2∫X·Y+∫|Y|².

**Pairing distributes over a sum.** Proved result `pair_split`: If X,Y,W∈L² and Z=X+Y almost everywhere, then ∫Z·W=∫X·W+∫Y·W.

**A coercive scalar estimate.** Proved result `final_alg`: If 0<κ≤1 and nonnegative f,g,n,p satisfy p≤f, n²≤g²+p², absolute bounds abs(A)≤fn and abs(B)≤pn, and κg²+B=A, then n+g≤(6/κ+1)f.

**Grouped estimates for the free equation.** Proved result `freeBounds_grouped_of`: Assuming the second-symbol energy, weak-power symbol, drift energy, and drift-power identities, every free solution with 1<α<5/4 and L² forcing and drift has both power and drift norms bounded by the forcing norm, satisfies the trace-pairing energy identity, and has the sum of gradient and trace norms bounded by a constant depending only on α times the forcing norm.

**The free bounds interface follows.** Proved result `freeBounds_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a free solution with L² forcing has separate power and drift norms bounded by the forcing norm, the stated trace-pairing energy identity and a uniform bound on the sum of square-root gradient and trace energies.

### Breakdown.FracCert.FreeExists

Extends solvability of the free equation from smooth Fourier data to arbitrary square-integrable data using density and completeness.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeExists.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.FreeExistsInternal`.

**Axial turns preserve sums.** Proved result `axialTurn_add`: The axial generator satisfies J(x+w)=Jx+Jw for all real vectors x,w. Source: `Breakdown.FracCert.FreeExists:15`.

**Axial turns preserve scaling.** Proved result `axialTurn_smul`: The axial generator satisfies J(cx)=cJx for every real c and x∈ℝ³. Source: `Breakdown.FracCert.FreeExists:18`.

**Axial turns preserve differences.** Proved result `axialTurn_sub`: The axial generator satisfies J(x−w)=Jx−Jw for all real vectors x,w. Source: `Breakdown.FracCert.FreeExists:21`.

**Axial turns are continuous.** Proved result `axialTurn_continuous`: The axial generator is a continuous map on ℝ³.

**Coordinates reconstruct each vector.** Proved result `sum_unit`: Every vector x equals the finite sum ∑ⱼxⱼeⱼ of its coordinate components. Source: `Breakdown.FracCert.FreeExists:28`.

**Basis convergence gives convergence.** Proved result `clm_tendsto`: If matrices Kₙ converge on each coordinate basis vector to K₀, then Kₙx→K₀x for every fixed vector x.

**The concrete L² norm is the Lp norm.** Proved result `l2Norm_eq`: For a square-integrable vector field f, the quantity √(∫|f|²) is its L² norm. Source: `Breakdown.FracCert.FreeExists:43`.

**Difference norms agree in L².** Proved result `l2Norm_sub`: For f,g∈L², √(∫|f−g|²) equals the distance between f and g in L².

**L² fields pair integrably.** Proved result `inner_integrable`: If f and g belong to L²(ℝ³;ℝ³), their pointwise inner product is integrable. Source: `Breakdown.FracCert.FreeExists:54`.

**Test fractional powers lie in L⁶⁄⁵.** Proved result `power_memLp`: For 1<α<3/2 and a smooth compactly supported vector test φ, (−Δ)^αφ belongs to L^(6/5)(ℝ³).

**Six and six-fifths are conjugate.** Proved result `conj_six`: The exponents 6 and 6/5 satisfy 1/6+1/(6/5)=1 and are Hölder conjugates.

**The norm of an L⁶ field lies in L⁶.** Proved result `six_memLp`: If w∈L⁶(ℝ³;ℝ³), its scalar norm y↦|w(y)| also belongs to L⁶.

**Fractional-power tests pair integrably.** Proved result `pair_integrable`: For 1<α<3/2, w∈L⁶ and a smooth compactly supported vector test φ, the pairing w·(−Δ)^αφ is integrable.

**Hölder bounds the test pairing.** Proved result `pair_bound`: For 1<α<3/2, w∈L⁶ and smooth compactly supported φ, |∫w·(−Δ)^αφ|≤‖w‖₆‖(−Δ)^αφ‖₆⁄₅.

**Second-order fields admit differences.** Proved result `sub_field`: Assuming closure of the second-order field class under linear combinations, the difference of two admissible fields with the same symmetry order has weak gradient G−K and weak Hessian H−L and remains admissible.

**Weak powers admit differences.** Proved result `sub_power`: For 1<α<3/2, if v,u∈L⁶ have L² weak fractional powers P,Q, then v−u has weak fractional power P−Q.

**Drift fields preserve differences.** Proved result `drift_sub`: The dilation-and-rotation drift is linear in the velocity and its gradient: Dα,a(v−u,G−K)=Dα,a(v,G)−Dα,a(u,K). Source: `Breakdown.FracCert.FreeExists:138`.

**Square-root bounds control energy.** Proved result `sq_bound`: If A,B≥0 and √A+√B≤c<√ε with ε>0, then A+B<ε.

**Vanishing powers imply vanishing.** Proved result `tendsto_of_pow`: For a nonnegative sequence fₙ and a positive integer k, fₙᵏ→0 implies fₙ→0.

**Free solutions survive L² limits.** Proved result `closure_core`: Assuming the free a priori estimates and completeness and linearity of the second-order field class, let 1<α<5/4 and F∈L² be approximated by Fₙ with ∫|F−Fₙ|²<1/(n+1). If every Fₙ has an admissible free solution with L² drift and weak fractional power, then F has such a solution, satisfying Dα,a v+(−Δ)^αv=F almost everywhere.

**Source namespace:** `Breakdown.SteadyCert`.

**The free equation is solvable.** Proved result `freeExists_of`: Under the stated assumptions, this establishes that for 1<α<5/4, every solenoidal L² forcing in the prescribed symmetry class has a second-order free solution with weak fractional power and L² drift satisfying drift plus power equals the forcing almost everywhere.

### Breakdown.FracCert.FreeNice

Realizes a Fourier profile symbol as a twice differentiable solenoidal field with finite energy and a weak fractional power.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeNice.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Profile symbols are measurable.** Proved result `profile_aesm`: A profile symbol that is smooth away from ξ=0, compactly supported and obeys the prescribed near-zero power bounds is measurable. Source: `Breakdown.FracCert.FreeNice:16`.

**Low moments of the symbol are integrable.** Proved result `profile_integrable_pow`: For α>1, a profile symbol with derivative bounds |Dʲw(ξ)|≤Cⱼ|ξ|^(2α−4−j) and bounded support has integrable moments ∫|ξ|ⁿ|w(ξ)|dξ for n=0,1,2.

**The realized profile is C².** Proved result `contDiff_profileField`: For α>1, the real inverse transform of an admissible profile symbol is twice continuously differentiable on ℝ³.

**The realized profile is solenoidal.** Proved result `divergence_profileField`: For α>1, the physical field realized from an admissible solenoidal profile symbol has zero divergence at every point.

**Profile symbols give smooth fields.** Proved result `profileSymbolSmooth`: Under the stated assumptions, this establishes that for 1<α<5/4, an admissible profile symbol realizes a C² vector field with vanishing classical divergence.

**Classical derivatives are weak ones.** Proved result `weak_of_contDiff`: For a C¹ Banach-valued function g and smooth compactly supported scalar φ, ∫∂ⱼφ·g=−∫φ∂ⱼg for every coordinate j.

**Second derivatives agree componentwise.** Proved result `second_apply`: For a C² vector field v, differentiating the ith derivative in direction eⱼ gives D(Dv)(y)[eⱼ]eᵢ.

**A power bound gives integrability.** Proved result `integrable_of_rpow_bound`: A measurable function g supported in a ball and bounded off zero by C|ξ|^β is integrable on ℝ³ whenever β>−3.

**The Fourier derivative factor is bounded.** Proved result `norm_mult_le`: For ξ,h∈ℝ³, |2πi(ξ·h)|≤2π|h||ξ|.

**Differentiation raises the power bound.** Proved result `mult_bound`: If |g(ξ)|≤C|ξ|^β for ξ≠0, then |2πi(ξ·h)g(ξ)|≤2π|h|C|ξ|^(β+1).

**Squaring doubles the power bound.** Proved result `sq_bound`: If |g(ξ)|≤C|ξ|^β away from zero, then |g(ξ)|²≤C²|ξ|^(2β) there. Source: `Breakdown.FracCert.FreeNice:170`.

**Fourier multiplication is measurable.** Proved result `mult_aesm`: Multiplying a measurable complex vector symbol by the Fourier differentiation factor 2πi(ξ·h) preserves measurability.

**Derivatives act on Fourier symbols.** Proved result `fderiv_niceField_apply`: If g and |ξ||g| are integrable, the directional derivative of its real inverse transform in direction h is the real inverse transform of 2πi(ξ·h)g(ξ).

**Compact symbols have finite L² energy.** Proved result `profile_facts`: If a measurable symbol g is supported in a ball and satisfies |g(ξ)|≤C|ξ|^β with β>−3/2 away from zero, then g belongs to L¹∩L² and its real inverse transform belongs to L².

**The first symbol moment is integrable.** Proved result `moment_integrable`: A measurable symbol supported in a ball and bounded by C|ξ|^β off zero has finite first absolute moment ∫|ξ||g(ξ)|dξ when β>−4.

**Realized derivatives have finite energy.** Proved result `energy_profileField`: For 1<α<5/4, the physical field realized from an admissible profile symbol has square-integrable gradient and Hessian.

**Profile symbols give finite energy.** Proved result `profileSymbolEnergy`: Under the stated assumptions, this establishes that for 1<α<5/4, the physical field realized by an admissible profile symbol has finite gradient energy and finite full Hessian energy.

**Inverse transforms satisfy a pairing.** Proved result `pair_scalar`: For integrable scalar symbols a and b, ∫(ℱ⁻¹a)(x)b(x)dx=∫a(ξ)(ℱ⁻¹b)(ξ)dξ.

**Inverse transforms of L¹ are continuous.** Proved result `continuous_inverseTransform_of`: The inverse Fourier transform of an L¹ scalar symbol is continuous.

**L¹ norms bound inverse transforms.** Proved result `norm_inverseTransform_le_of`: For any scalar symbol a, |ℱ⁻¹a(x)|≤∫|a(ξ)|dξ at each point x.

**Vector pairings split by coordinate.** Proved result `pair_vector`: For integrable complex vector h and real vector f, ∫Re(ℱ⁻¹h)·f equals the sum over coordinates of Re∫hᵢ(ξ)(ℱ⁻¹fᵢ)(ξ)dξ.

**Frequency weights realize weak powers.** Proved result `power_profileField`: For 1<α<5/4 and an admissible profile symbol w, the inverse field of (2π‖ξ‖)^(2α)w is the weak fractional power of the inverse field of w.

**Profile symbols give weak powers.** Proved result `profileSymbolPower`: Under the stated assumptions, this establishes that for 1<α<5/4, multiplying an admissible profile symbol by (2π‖ξ‖)^(2α) realizes the weak fractional power of its physical field.

**Symbol properties give realization.** Proved result `profileSymbolRealize_of`: Under the stated assumptions, this establishes that for 1<α<5/4, an admissible profile symbol with the prescribed physical symmetry realizes a second-order field whose weak fractional power is obtained by multiplying its symbol by (2π‖ξ‖)^(2α).

**Nice data give free solutions.** Proved result `freeExistsNice_of`: Under the stated assumptions, this establishes that for 1<α<5/4, every nice solenoidal forcing in the prescribed symmetry class has a second-order free solution with weak fractional power and L² drift satisfying the free equation almost everywhere.

### Breakdown.FracCert.FreeSymbolExists

Closes the Fourier construction of a free fractional solution from its smoothness, decay, equation and symmetry properties.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExists.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Four symbol properties give existence.** Proved result `freeSymbolExists_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and a nice forcing in the symmetry class, an admissible profile symbol exists in that class and solves the free frequency equation away from zero.

**Small-frequency bounds give existence.** Proved result `freeSymbolExists_of_small`: Under the stated assumptions, this establishes that for 1<α<5/4 and a nice forcing in the symmetry class, an admissible profile symbol exists in that class and solves the free frequency equation away from zero.

**Core bounds give symbol existence.** Proved result `freeSymbolExists_of_core`: Under the stated assumptions, this establishes that for 1<α<5/4 and a nice forcing in the symmetry class, an admissible profile symbol exists in that class and solves the free frequency equation away from zero.

**A free solution symbol exists.** Proved result `freeSymbolExists`: Under the stated assumptions, this establishes that for 1<α<5/4 and a nice forcing in the symmetry class, an admissible profile symbol exists in that class and solves the free frequency equation away from zero.

### Breakdown.FracCert.FreeSymbolExistsBasic

Checks support, conjugation symmetry and solenoidality of the explicit free Fourier solution.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsBasic.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolExistsInternal`.

**Axial rotation has three coordinates.** Proved result `rot_coord`: Axial rotation sends (y₁,y₂,y₃) to (cosθ y₁−sinθ y₂, sinθ y₁+cosθ y₂, y₃).

**Axial rotations preserve norms.** Proved result `rot_norm`: For every θ and y∈ℝ³, axial rotation preserves length: |Rθy|=|y|.

**Axial rotations preserve negation.** Proved result `rot_neg`: For every θ and y∈ℝ³, Rθ(−y)=−Rθy.

**Complex rotations have three coordinates.** Proved result `rotC_coord`: The complex axial rotation sends (z₁,z₂,z₃) to (cosθ z₁−sinθ z₂, sinθ z₁+cosθ z₂, z₃).

**Conjugation acts on each coordinate.** Proved result `conj_coord`: Complex conjugation of a vector acts on each coordinate separately.

**Rotation commutes with conjugation.** Proved result `rotC_conj`: For every angle θ and complex vector z, Rθ overline{z}=overline{Rθz}.

**Rotation fixes the zero vector.** Proved result `rotC_zero`: Every complex axial rotation sends the zero vector to zero.

**Complex conjugation as an isometry.** Definition `conjIsometry`: This equips coordinatewise complex conjugation with its real linear isometry structure.

**The free symbol vanishes far away.** Proved result `support_zero`: For α>0 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, the constructed free solution symbol vanishes outside some ball.

**The free symbol has real symmetry.** Proved result `conjSymmetric`: For smooth solenoidal conjugate-symmetric input supported away from zero with compact support, the constructed free symbol satisfies w(−ξ)=overline{w(ξ)}.

**Rotation transfers to the frequency.** Proved result `pair_rotC`: For ξ∈ℝ³ and z∈ℂ³, ∑ᵢξᵢ(Rθz)ᵢ=∑ᵢ(R₋θξ)ᵢzᵢ.

**The free symbol is solenoidal.** Proved result `divergence`: For smooth solenoidal conjugate-symmetric input supported in a compact annulus, the free solution symbol satisfies ∑ᵢξᵢwᵢ(ξ)=0 at every ξ.

### Breakdown.FracCert.FreeSymbolExistsBound

Promotes near-zero bounds for the free Fourier solution to global derivative bounds using compact support and smoothness away from zero.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsBound.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolBoundInternal`.

**All free derivatives vanish far away.** Proved result `far_zero`: For α>0 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, one radius R>0 contains the support of every derivative of the free solution symbol.

**Free derivatives are continuous off zero.** Proved result `deriv_continuousOn`: For α>0 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, every derivative of the constructed free symbol is continuous away from ξ=0.

**Source namespace:** `Breakdown.SteadyCert`.

**Local decay gives global decay.** Proved result `freeSolutionBound_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and nice input data, each jth derivative of the free Fourier solution is bounded by C‖ξ‖^(2α−4−j) at every nonzero frequency.

### Breakdown.FracCert.FreeSymbolExistsClass

Transports the prescribed rotational and reflection symmetries through the explicit free Fourier inverse.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsClass.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolClassInternal`.

**Fourier transforms respect linear maps.** Proved result `transform_clm`: Fourier transformation commutes with a fixed invertible complex-linear map L: ℱ(Lf)=L(ℱf).

**Inverse transforms respect linear maps.** Proved result `inverseTransform_clm`: Inverse Fourier transformation commutes with a fixed invertible complex-linear map L: ℱ⁻¹(Lf)=L(ℱ⁻¹f).

**Compatible spatial and complex actions.** Structure `Compatible`: This proposition bundles commutation of the spatial and complex actions with axial rotations and compatibility with taking real parts and complexification.

**Field symmetry implies symbol symmetry.** Proved result `symbol_equiv`: For an isometry T whose complex extension commutes with axial rotations, a physical field's pointwise T-equivariance implies T-equivariance of its smooth solenoidal conjugate-symmetric symbol supported in a compact annulus.

**Free solutions preserve symmetry.** Proved result `solution_equiv`: If an isometry T and its complex extension commute with axial rotations and the input symbol is T-equivariant, the constructed free solution symbol is T-equivariant for every α and a.

**Symbol symmetry implies field symmetry.** Proved result `field_equiv`: If a symbol is equivariant under an isometry T whose complex extension commutes with axial rotations, its real inverse transform satisfies V(Ty)=TV(y).

**Axial rotation as a linear map.** Definition `rotLin`: This equips axial rotation through θ with its real linear map structure.

**Axial rotation as an isometry.** Definition `rotIso`: This equips axial rotation through θ with its norm-preserving linear equivalence structure.

**Reflection as a linear map.** Definition `mirrorLin`: This equips reflection of the third spatial coordinate with its real linear map structure.

**Reflection preserves norms.** Proved result `mirror_norm`: Reflection across the horizontal plane preserves Euclidean length: |(y₁,y₂,−y₃)|=|y|. Source: `Breakdown.FracCert.FreeSymbolExistsClass:81`.

**Reflection as an isometry.** Definition `mirrorIso`: This equips reflection of the third spatial coordinate with its norm-preserving linear equivalence structure.

**Complex rotation as an equivalence.** Definition `rotCLE`: This equips rotation of the first two complex coordinates through θ with its continuous complex linear equivalence structure and inverse rotation through −θ.

**Reflection of complex vectors.** Definition `mirrorC`: This defines complex reflection by retaining the first two coordinates and negating the third.

**Complex reflection as an equivalence.** Definition `mirrorCLE`: This equips complex reflection with its continuous complex linear equivalence structure and uses reflection itself as its inverse.

**The discrete turn is compatible.** Proved result `turn_compatible`: The discrete axial rotation through 2π/m and its complex extension commute with all axial rotations and agree under real inclusion and real-part projection.

**Reflection is compatible.** Proved result `mirror_compatible`: Horizontal-plane reflection and its complex extension commute with axial rotations and agree under real inclusion and real-part projection.

**Free solutions retain class symmetry.** Proved result `solution_class`: Under the stated hypotheses, free solutions stay in the symmetry class.

**Source namespace:** `Breakdown.SteadyCert`.

**The free solution preserves its class.** Proved result `freeSolutionClass`: Under the stated assumptions, this establishes that for 1<α<5/4, the explicit free Fourier solution preserves the prescribed discrete rotation and reflection class of the physical forcing.

### Breakdown.FracCert.FreeSymbolExistsCore

Proves the near-origin power bounds for the undamped core of the free Fourier solution by homogeneity along the rotation and dilation flow.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsCore.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolCoreInternal`.

**Flow norms scale exponentially.** Proved result `flow_norm`: The frequency characteristic ξ(t)=e^(−t/(2α))Rₐtζ has norm e^(−t/(2α))|ζ|.

**The kernel vanishes before time zero.** Proved result `kernel_nonpos`: For α>0, if the input symbol vanishes on |ξ|< r, then its characteristic kernel is zero for |ζ|< r and characteristic times σ≤0.

**The core obeys a scaling identity.** Proved result `core_homog`: For α>1 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, the characteristic integral h satisfies h(e^(−t/(2α))Rₐtζ)=e^(−(1−2/α)t)Rₐth(ζ) for t≥0 and all sufficiently small nonzero ζ.

**Complex rotations have a uniform bound.** Proved result `rotC_bound`: The complex rotation has the uniform estimate |Rθz|≤(1+‖J‖+2‖Pₐₓᵢₛ‖)|z|, where J is the axial generator and Pₐₓᵢₛ the projection onto the rotation axis.

**Core derivatives have power bounds.** Proved result `core_bound`: Under the stated assumptions, this establishes that for 1<α<5/4 and nice input data, the jth derivative of the undamped Fourier core is bounded by C‖ξ‖^(2α−4−j) near zero frequency.

**Source namespace:** `Breakdown.SteadyCert`.

**The core bound interface holds.** Proved result `freeCoreBound`: Under the stated assumptions, this establishes that for 1<α<5/4 and nice input data, the jth derivative of the undamped Fourier core is bounded by C‖ξ‖^(2α−4−j) near zero frequency.

### Breakdown.FracCert.FreeSymbolExistsEquation

Differentiates the explicit free Fourier integral along characteristics to obtain the fractional profile equation away from zero frequency.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsEquation.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolEquationInternal`.

**The integrated undamped Fourier core.** Definition `hbase`: This defines the undamped Fourier core as the integral of the characteristic kernel over positive times.

**The infinitesimal spatial turn.** Definition `turnCL`: This defines the continuous real linear map sending (x₁,x₂,x₃) to (−x₂,x₁,0).

**Projection onto the spatial axis.** Definition `axisCL`: This defines projection onto the third spatial coordinate as a continuous linear map.

**The infinitesimal complex turn.** Definition `turnCLC`: This defines the continuous real linear map sending a complex vector (z₁,z₂,z₃) to (−z₂,z₁,0).

**Projection onto the complex axis.** Definition `axisCLC`: This defines projection onto the third complex coordinate as a continuous real linear map.

**The spatial turn is (−x₂,x₁,0).** Proved result `turnCL_apply`: The continuous spatial turn map sends (x₁,x₂,x₃) to (−x₂,x₁,0), agreeing with the axial generator.

**The axis map selects coordinate three.** Proved result `axisCL_apply`: The real axis projection sends y to y₃e₃.

**The complex turn is (−z₂,z₁,0).** Proved result `turnCLC_apply`: The continuous complex turn map sends (z₁,z₂,z₃) to (−z₂,z₁,0), agreeing with the complex axial generator.

**complex axis selects coordinate three.** Proved result `axisCLC_apply`: The complex axis projection sends z to z₃e₃.

**Zero-angle rotation is the identity.** Proved result `rot_zero`: Axial rotation through angle zero fixes every real vector.

**Zero-angle complex rotation is identity.** Proved result `rotC_zero'`: Axial rotation through angle zero fixes every complex vector.

**Rotation splits into three terms.** Proved result `rot_decomp`: For a real vector y, Rθy=cosθ y+sinθ Jy+(1−cosθ)Pₐₓᵢₛy.

**Complex rotation splits into three terms.** Proved result `rotC_decomp`: For a complex vector z, Rθz=cosθ z+sinθ Jz+(1−cosθ)Pₐₓᵢₛz.

**Cosine has zero initial derivative.** Proved result `cos_deriv`: Under the stated hypotheses, scaled cosine has zero derivative at zero.

**The initial sine derivative is a.** Proved result `sin_deriv`: The function t ↦ sin(at) has derivative a at t=0.

**Complex rotations obey the product rule.** Proved result `rotC_deriv`: If A is differentiable at zero, the derivative there of RₐtA(t) is A′(0)+aJA(0).

**Axial rotations have the turn derivative.** Proved result `rot_deriv`: For a fixed real vector ξ, the derivative at t=0 of Rₐtξ is aJξ.

**The characteristic frequency flow.** Definition `flowPt`: This defines the characteristic frequency trajectory exp(−t/(2α)) R(at)ξ.

**The flow fixes its initial frequency.** Proved result `flow_zero`: At time zero, the characteristic frequency trajectory equals its initial frequency.

**The flow derivative is drift plus turn.** Proved result `flow_deriv`: The characteristic e^(−t/(2α))Rₐtξ has derivative −ξ/(2α)+aJξ at t=0.

**Rotation preserves scalar multiples.** Proved result `rot_smul'`: Axial rotation commutes with real scalar multiplication: Rθ(cy)=cRθy.

**Rotation angles add under composition.** Proved result `rot_rot`: Composing real axial rotations adds their angles: RθRφy=Rθ₊φy.

**Complex rotation angles add.** Proved result `rotC_rotC`: Composing complex axial rotations adds their angles: RθRφz=Rθ₊φz.

**Flow shifts translate kernel time.** Proved result `kernel_shift`: Transporting the frequency point along the characteristic shifts kernel time from τ to τ−t and multiplies the kernel by e^(−(1−2/α)t)Rₐt.

**The characteristic kernel is continuous.** Proved result `kernel_cont`: For smooth solenoidal conjugate-symmetric input supported in a compact annulus, the characteristic kernel is continuous in its time variable at every frequency point.

**The core integral has a finite cutoff.** Proved result `core_eq_interval`: For α>0 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, there is R>0 such that the core integral at ξ equals its integral over [0,T] whenever 0<ε<|ξ| and T≥2αR/ε.

**The core is smooth away from zero.** Proved result `core_contDiffAt`: For α>0 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, the core characteristic integral is smooth at every nonzero frequency.

**core satisfies its transport identity.** Proved result `core_deriv`: For α>1 and admissible compact-annulus input s, the core h satisfies Dh(ξ)[−ξ/(2α)+aJξ]=K(ξ,0)+aJh(ξ)−(1−2/α)h(ξ) for ξ≠0, where K is its characteristic kernel.

**Drift differentiates the frequency power.** Proved result `pow_deriv`: For α>0 and ξ≠0, the derivative of (2π|ξ|)^(2α) along −ξ/(2α)+aJξ equals −(2π|ξ|)^(2α).

**The kernel at zero is damped data.** Proved result `kernel_zero`: At characteristic time zero, the kernel is e^(−(2π|ξ|)^(2α))s(ξ).

**Complex turns preserve scaling.** Proved result `turnC_smul`: The complex axial generator commutes with real scalar multiplication: J(cz)=cJz.

**The free symbol solves its equation.** Proved result `equation`: For α>1 and smooth solenoidal conjugate-symmetric datum s supported in a compact annulus, the constructed w solves (1−2/α)w−Dw[ξ]/(2α)+a(Dw[Jξ]−Jw)+(2π|ξ|)^(2α)w=s at every ξ≠0.

**Source namespace:** `Breakdown.SteadyCert`.

**The free equation interface holds.** Proved result `freeSolutionEquation`: Under the stated assumptions, this establishes that for 1<α<5/4 and a nice input symbol, applying the profile operator to the explicit free Fourier solution recovers the input at every nonzero frequency.

### Breakdown.FracCert.FreeSymbolExistsExp

Bounds derivatives of radial frequency powers and their exponential multiplier near zero.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsExp.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolExpInternal`.

**Frequency derivatives are continuous.** Proved result `pow_deriv_cont`: For every real p and derivative order i, the ith derivative of ξ↦(2π|ξ|)ᵖ is continuous away from ξ=0.

**Frequency derivatives have power bounds.** Proved result `pow_deriv_bound`: For every real p and nonnegative integer i, there is K such that |Dⁱ(2π|ξ|)ᵖ|≤K|ξ|^(p−i) for ξ≠0.

**Power bounds for exponential derivatives.** Proved result `exp_bound`: Under the stated assumptions, this establishes that for 1<α<5/4, each jth derivative of exp((2π‖ξ‖)^(2α)) is bounded by C‖ξ‖^(−j) for nonzero frequencies of norm at most one.

**Source namespace:** `Breakdown.SteadyCert`.

**The exponential bound interface holds.** Proved result `freeExpBound`: Under the stated assumptions, this establishes that for 1<α<5/4, each jth derivative of exp((2π‖ξ‖)^(2α)) is bounded by C‖ξ‖^(−j) for nonzero frequencies of norm at most one.

### Breakdown.FracCert.FreeSymbolExistsParts

Defines the explicit free Fourier solution and the smoothness, decay, equation and symmetry contracts used to certify it.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Complex axial rotation.** Definition `axialRotationC`: This defines axial rotation of a complex vector by the usual sine and cosine matrix on its first two coordinates, leaving the third unchanged.

**The free-solution damping weight.** Definition `freeWeight`: This defines the characteristic damping weight exp(−(1−2/α)τ) exp(−(exp τ−1)(2π‖ξ‖)^(2α)).

**The free Fourier solution.** Definition `freeSolution`: This defines the free Fourier solution as the positive-time integral of damped, rotated input data evaluated along the expanding frequency characteristics.

**The free solution is smooth off zero.** Proposition `FreeSolutionSmoothStatement`: This proposition requires that for 1<α<5/4 and a nice input symbol, the explicit free Fourier solution is infinitely differentiable away from zero frequency.

**Free derivatives satisfy power bounds.** Proposition `FreeSolutionBoundStatement`: This proposition requires that for 1<α<5/4 and nice input data, each jth derivative of the free Fourier solution is bounded by C‖ξ‖^(2α−4−j) at every nonzero frequency.

**Free derivatives have local power bounds.** Proposition `FreeSolutionSmallBoundStatement`: This proposition requires that for 1<α<5/4 and nice input data, each jth derivative of the free Fourier solution has a bound C‖ξ‖^(2α−4−j) in some punctured neighborhood of zero.

**The free solution solves its equation.** Proposition `FreeSolutionEquationStatement`: This proposition requires that for 1<α<5/4 and a nice input symbol, applying the profile operator to the explicit free Fourier solution recovers the input at every nonzero frequency.

**The free solution preserves symmetry.** Proposition `FreeSolutionClassStatement`: This proposition requires that for 1<α<5/4, the explicit free Fourier solution preserves the prescribed discrete rotation and reflection class of the physical forcing.

### Breakdown.FracCert.FreeSymbolExistsSmall

Separates the near-origin estimate for the free Fourier solution into an undamped core estimate and an exponential-factor estimate.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsSmall.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Core derivatives satisfy power bounds.** Proposition `FreeCoreBoundStatement`: This proposition requires that for 1<α<5/4 and nice input data, the jth derivative of the undamped Fourier core is bounded by C‖ξ‖^(2α−4−j) near zero frequency.

**Exponential derivatives satisfy bounds.** Proposition `FreeExpBoundStatement`: This proposition requires that for 1<α<5/4, each jth derivative of exp((2π‖ξ‖)^(2α)) is bounded by C‖ξ‖^(−j) for nonzero frequencies of norm at most one.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolSmallInternal`.

**Core and exponential bounds combine.** Proved result `small_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and nice input data, each jth derivative of the free Fourier solution has a bound C‖ξ‖^(2α−4−j) in some punctured neighborhood of zero.

**Source namespace:** `Breakdown.SteadyCert`.

**The local free bound follows.** Proved result `freeSolutionSmallBound_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and nice input data, each jth derivative of the free Fourier solution has a bound C‖ξ‖^(2α−4−j) in some punctured neighborhood of zero.

### Breakdown.FracCert.FreeSymbolExistsSmooth

Uses compact support of the Fourier data to make the characteristic integral locally finite and smooth away from zero frequency.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeSymbolExistsSmooth.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeSymbolSmoothInternal`.

**Real inclusion into complex is smooth.** Proved result `ofReal_smooth`: The inclusion of the real line into the complex plane is smooth as a map of real vector spaces.

**Smooth rotations compose smoothly.** Proved result `rot_comp`: If an angle f and a real vector g depend smoothly on a normed-space parameter x, then x↦R_{f(x)}g(x) is smooth.

**Complex rotations compose smoothly.** Proved result `rotC_comp`: If an angle f and a complex vector g depend smoothly on x, their axial rotation x↦R_{f(x)}g(x) is smooth.

**Frequency powers are smooth off zero.** Proved result `pow_smoothAt`: For every real p, the frequency power (2π|ξ|)ᵖ is smooth at every ξ≠0.

**The exponentially damped symbol.** Definition `damped`: This defines the damped input symbol by multiplying it by exp(−(2π‖ξ‖)^(2α)).

**The damped nice symbol is smooth.** Proved result `damped_smooth`: For smooth solenoidal conjugate-symmetric s supported in a compact annulus, the damped symbol e^(−(2π|ξ|)^(2α))s(ξ) is smooth everywhere for any α.

**The characteristic integral kernel.** Definition `kernel`: This defines the characteristic kernel by rotating the damped input along expanding, counterrotating frequencies and multiplying by exp(−(1−2/α)τ).

**The kernel is jointly smooth.** Proved result `kernel_smooth`: For smooth solenoidal conjugate-symmetric input supported in a compact annulus, the characteristic kernel is jointly smooth in frequency and time for every α and a.

**Complex rotations preserve scaling.** Proved result `rotC_smul`: Complex axial rotation commutes with real scalar multiplication: Rθ(cz)=cRθz.

**Axial rotations preserve norms.** Proved result `rot_norm'`: Axial rotation preserves the Euclidean norm of every real vector.

**Frequency powers respect dilation.** Proved result `pow_scale`: For α>0, (2π|e^(τ/(2α))Rθξ|)^(2α)=e^τ(2π|ξ|)^(2α).

**The integrand splits off its exponential.** Proved result `integrand_eq`: For α>0, the free-solution integrand equals e^((2π|ξ|)^(2α)) times the damped characteristic kernel at (ξ,τ).

**The free solution splits off damping.** Proved result `solution_eq`: For α>0, the constructed free symbol is e^((2π|ξ|)^(2α)) times the integral of its damped characteristic kernel over τ>0.

**The kernel has a finite time cutoff.** Proved result `kernel_far`: For α>0 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, some R>0 makes the characteristic kernel zero whenever 0<ε<|ξ| and τ>2αR/ε.

**The free solution is smooth off zero.** Proved result `solution_smooth`: For α>0 and smooth solenoidal conjugate-symmetric input supported in a compact annulus, the free solution symbol is smooth on ℝ³∖{0}.

**Source namespace:** `Breakdown.SteadyCert`.

**The free smoothness interface holds.** Proved result `freeSolutionSmooth`: Under the stated assumptions, this establishes that for 1<α<5/4 and a nice input symbol, the explicit free Fourier solution is infinitely differentiable away from zero frequency.

### Breakdown.FracCert.FreeUnique

Uses the energy identities to prove uniqueness of free solutions, including the fact that an L⁶ field with zero weak gradient vanishes.

This supplies the Fourier and free-operator analysis behind the fractional analogue of the linear estimates used in the certificate strategy; fractional statements are not used by the paper according to the source README.

Source: `lean/Breakdown/FracCert/FreeUnique.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeUnique.Internal`.

**Zero basis values give the zero map.** Proved result `clm_zero_of_unit`: A linear map from ℝ³ into a real normed space is zero if it vanishes on all three coordinate basis vectors. Source: `Breakdown.FracCert.FreeUnique:15`.

**Zero weak gradients kill convolutions.** Proved result `conv_deriv_zero`: If v has weak gradient G=0 almost everywhere, then ∫∂ⱼf(z−t)v(t)dt=0 for every smooth compactly supported scalar f, point z and coordinate j.

**Zero gradients give constant mollifiers.** Proved result `conv_const`: Under the stated hypotheses, a mollified zero-gradient field is constant.

**An L⁶ field with zero gradient vanishes.** Proved result `velocity_zero`: If v∈L⁶(ℝ³) has weak gradient zero almost everywhere, then v=0 almost everywhere.

**Zero symbol energy kills derivatives.** Proved result `second_zero_of_energy`: Assuming the Fourier energy identities for second derivatives, an admissible field whose negative-Laplacian symbol is zero almost everywhere has both weak gradient and weak Hessian zero almost everywhere.

**Source namespace:** `Breakdown.SteadyCert`.

**The free solution is unique.** Proved result `freeUnique_of`: Under the stated assumptions, this establishes that for 1<α<5/4, a second-order field with weak fractional power, L² drift and zero free residual has velocity, both derivative fields and fractional power all zero almost everywhere.

### Breakdown.FracCert.GradientAdd

Proves that weak gradient fields are closed under addition, handling the measurability required by their test identities.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/GradientAdd.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.GradientAddInternal`.

**Absolute values are bounded by squares.** Proved result `abs_le_one_add_sq`: For every real a, |a|≤1+a².

**A local square bound implies local L¹.** Proved result `locInt_of_bound`: If f is measurable, g is locally square-integrable and |f|≤|g| pointwise, then f is locally integrable.

**Compact tests pair integrably.** Proved result `pair_integrable`: The product of a locally integrable scalar function and a continuous compactly supported scalar test is integrable on ℝ³.

**Gradient components are locally L¹.** Proved result `comp_locInt`: Every coordinate of a measurable, locally square-integrable vector field is locally integrable.

**Test derivatives are continuous.** Proved result `deriv_continuous`: For a smooth compactly supported scalar test φ and fixed direction v, y↦Dφ(y)[v] is continuous.

**Test derivatives have compact support.** Proved result `deriv_support`: For a smooth compactly supported scalar test φ and fixed direction v, its directional derivative has compact support.

**Test pairings force measurability.** Proved result `aesm_of_pairings`: If (∂ⱼφ)q is measurable for every smooth compactly supported φ in one fixed coordinate direction j, then q is measurable.

**The nonmeasurable case has zero pairings.** Proved result `pairing_zero`: If the potential in the weak-gradient identities is not almost-everywhere strongly measurable while the vector field has the stated local square integrability, each compact scalar-test pairing with a field coordinate is zero.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak gradient fields admit sums.** Proved result `gradientAdd`: Under the stated assumptions, this establishes that the sum of two weak gradient fields is a weak gradient field.

### Breakdown.FracCert.GradientClosed

Identifies the closed L² subspace of gradient fields through orthogonality to solenoidal fields.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/GradientClosed.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.GradientClosedInternal`.

**Gradient fields respect almost equality.** Proved result `gradient_congr`: If Q is a locally square-integrable weak gradient and Q′∈L² equals Q almost everywhere, then Q′ is also a weak gradient of a locally square-integrable potential.

**Difference norms equal squared integrals.** Proved result `norm_sub_sq`: If F and G represent L² fields f and g almost everywhere, then ‖f−g‖₂²=∫|F−G|².

**Orthogonality implies gradient closure.** Proved result `closed_of_orthogonal`: Under the stated assumptions, this establishes that strong L² limits of square-integrable weak gradient fields are weak gradient fields.

**Source namespace:** `Breakdown.SteadyCert`.

**Gradient closure follows from duality.** Proved result `gradientClosed_of_orthogonal`: Under the stated assumptions, this establishes that strong L² limits of square-integrable weak gradient fields are weak gradient fields.

**The L² gradient fields form a closed set.** Proved result `gradientClosed`: Under the stated assumptions, this establishes that strong L² limits of square-integrable weak gradient fields are weak gradient fields.

### Breakdown.FracCert.GradientOrthogonal

Shows that gradient fields are orthogonal to square-integrable solenoidal fields using curl identities and translated pairings.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/GradientOrthogonal.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.GradientOrthogonalInternal`.

**Reversed scalar multiplication.** Abbreviation `mulFlip`: This abbreviates real scalar multiplication with its two arguments exchanged, represented as a continuous bilinear map.

**Flipped multiplication is r times a.** Proved result `mulFlip_apply`: Evaluating the flipped scalar multiplication map at a and r gives the real product r·a.

**Test derivatives remain tests.** Proved result `test_dir`: A directional derivative of a smooth compactly supported scalar test is again smooth and compactly supported.

**Smooth mixed derivatives commute.** Proved result `second_dir`: For a smooth compactly supported scalar test φ and fixed directions u,v, ∂ᵥ∂ᵤφ=∂ᵤ∂ᵥφ at every point.

**Gradient fields have symmetric curl data.** Proved result `curl_symm`: A locally square-integrable weak gradient Q satisfies ∫∂ₖφ Qⱼ=∫∂ⱼφ Qₖ for every smooth compactly supported φ, expressing zero distributional curl.

**Zero basis values give the zero map.** Proved result `clm_zero_of_unit`: A scalar linear functional on ℝ³ is zero if its value on every coordinate basis vector is zero. Source: `Breakdown.FracCert.GradientOrthogonal:49`.

**Zero weak derivatives kill smoothing.** Proved result `conv_hasFDerivAt_zero`: Under the stated hypotheses, vanishing weak derivatives kill smoothing.

**Continuous decay gives a global bound.** Proved result `bounded_of`: A continuous scalar function tending to zero outside compact sets is bounded in absolute value on ℝ³.

**The smoothed constant must vanish.** Proved result `conv_zero`: If a continuous scalar C tends to zero at infinity and all its distributional first derivatives vanish, then (C*ψ)(0)=0 for every smooth compactly supported ψ.

**The zero-derivative pairing vanishes.** Proved result `zero_of_parts`: If C is continuous, tends to zero at infinity and has all distributional first derivatives zero, then C(0)=0.

**Source namespace:** `Breakdown.SteadyCert`.

**Gradient and solenoidal orthogonality.** Proved result `gradientOrthogonal`: Under the stated assumptions, this establishes that every square-integrable weak gradient field has zero integral pairing with every solenoidal L² field.

### Breakdown.FracCert.GradientOrthogonalParts

Develops translated L² pairings, their decay and differentiated convolution identities for the gradient-orthogonality proof.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/GradientOrthogonalParts.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.GradientOrthogonalInternal`.

**The translated field pairing.** Definition `pairShift`: This defines the translated pairing ∫⟨ζ(x),Q(x+y)⟩ dx.

**The generic integral L² size.** Definition `sq2'`: This defines the square root of the integral of the squared norm of a general normed-space-valued field.

**The vector integral L² size.** Definition `sq2`: This defines the square root of the integral of the squared norm of a spatial vector field.

**The integral L² size is nonnegative.** Proved result `sq2_nonneg`: The quantity √(∫|f|²) is nonnegative for every vector field f.

**Translation preserves L².** Proved result `memLp_shift`: If b∈L²(ℝ³), every translate x↦b(x+y) belongs to L².

**Translation preserves the L² size.** Proved result `sq2_shift`: Translating a vector field leaves √(∫|b|²) unchanged.

**L² fields pair integrably.** Proved result `integrable_pair`: If a,b∈L²(ℝ³), their scalar product a·b is integrable. Source: `Breakdown.FracCert.GradientOrthogonalParts:35`.

**Cauchy-Schwarz bounds the pairing.** Proved result `abs_pair_le`: For a,b∈L², |∫a·b|≤√(∫|a|²)√(∫|b|²). Source: `Breakdown.FracCert.GradientOrthogonalParts:42`.

**Compact continuous fields approximate L².** Proved result `approx`: For f∈L² and ε>0, there is a continuous compactly supported g∈L² with ‖f−g‖₂≤ε.

**Pairing errors obey a two-term bound.** Proved result `pair_sub`: For ζ,Q,g,h∈L², their translated pairings satisfy |∫ζ(x)·Q(x+y)dx−∫g(x)·h(x+y)dx|≤‖ζ−g‖₂‖Q‖₂+‖g‖₂‖Q−h‖₂, uniformly in y.

**Compact pairings approximate uniformly.** Proved result `uniform_approx`: For ζ,Q∈L² and ε>0, continuous compactly supported g,h can be chosen so that their translated pairing differs from that of ζ,Q by at most ε for every translation y.

**Shifted pairings are convolutions.** Proved result `pairShift_conv`: The translated pairing y↦∫g(x)·h(x+y)dx is the convolution of x↦g(−x) with h using the vector inner product.

**Compact pairings decay continuously.** Proved result `approx_cont`: Under the stated hypotheses, compact pairings are continuous and decay.

**Translated L² pairings are continuous.** Proved result `continuous_pairShift`: For ζ,Q∈L², the function y↦∫ζ(x)·Q(x+y)dx is continuous.

**Translated L² pairings decay at infinity.** Proved result `tendsto_pairShift`: For ζ,Q∈L², their translated pairing ∫ζ(x)·Q(x+y)dx tends to zero as |y|→∞.

**Shifted weighted pairings are integrable.** Proved result `integrable_pair_shift`: If ζ∈L², F∈L² and κ is continuous with compact support, then x↦|ζ(x)| |∫κ(y)F(x+y)dy| is integrable.

**Derivative norms control gradient norms.** Proved result `grad_norm_le`: For a scalar function g, the coordinate gradient satisfies |∇g(x)|≤3‖Dg(x)‖.

**Scalar gradients obey the product rule.** Proved result `grad_mul`: At a point where a and b are differentiable, ∇(ab)=a∇b+b∇a.

**Smooth scalar gradients are continuous.** Proved result `continuous_grad`: The gradient of a smooth scalar function is continuous on ℝ³.

**Solenoidal fields annihilate gradients.** Proved result `cut_pair`: If ζ∈L² is solenoidal, f is smooth, and |ζ||f| and each |ζ||∂ⱼf| are integrable, then ∫ζ·∇f=0.

**Fubini exchanges the shifted pairing.** Proved result `exchange_pair`: For ζ,Q∈L² and continuous compactly supported κ, ∫κ(y)∫ζ(x)·Q(x+y)dxdy=∫ζ(x)·∫κ(y)Q(x+y)dydx.

**Reversed scalar multiplication.** Abbreviation `scalFlip`: This abbreviates real multiplication with its two arguments exchanged as a continuous bilinear map.

**Flipped multiplication is r times a.** Proved result `scalFlip_apply`: Evaluating the flipped scalar multiplication map at a and r gives the real product r·a.

**Shifted integrals are convolutions.** Proved result `shift_conv`: The shifted integral x↦∫h(y)F(x+y)dy equals the convolution of F with the reflected kernel h(−·).

**Test convolution differentiates smoothly.** Proved result `deriv_shift`: For F∈L² and smooth compactly supported φ, x↦∫φ(y)F(x+y)dy is smooth and its jth derivative is −∫∂ⱼφ(y)F(x+y)dy.

**Test derivatives retain compact support.** Proved result `test_dir'`: Under the stated hypotheses, test derivatives are continuous and compact.

**Curl symmetry survives translation.** Proved result `curl_shift`: If Q has zero distributional curl, its translates satisfy ∫∂ₖφ(y)Qⱼ(x+y)dy=∫∂ⱼφ(y)Qₖ(x+y)dy for every smooth compactly supported φ and every x.

**Pairing derivatives vanish weakly.** Proved result `integral_deriv_pairShift`: If ζ∈L² is solenoidal and Q∈L² has zero distributional curl, then all distributional derivatives of their translated pairing vanish: ∫∂ₖφ(y)∫ζ(x)·Q(x+y)dxdy=0.

### Breakdown.FracCert.HeatDivRegular

Differentiates the projected heat-divergence operator under an integrable kernel to propagate smoothness and derivative bounds.

This develops regularity or spatial decay for the fractional extension, supporting passage from a weak fractional profile to a classical decaying field; it is not an identification with a numbered ordinary-dissipation theorem in the paper.

Source: `lean/Breakdown/FracCert/HeatDivRegular.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracInternal.HeatDivRegular`.

**derivative bound gives Lipschitz control.** Proved result `deriv_increment`: Under the stated hypotheses, one more derivative gives a Lipschitz bound.

**Top and zeroth derivatives give bounds.** Proved result `step_bound`: Under the stated hypotheses, values and top derivatives control the rest.

**Derivative bounds interpolate.** Proved result `interp`: For a Cʲ map g with |g|≤B and |Dʲg|≤A globally, each derivative of order n≤j is bounded by (2ʲ+j)ʲ(A+B).

**Dominated integrals preserve derivatives.** Proved result `param_contDiff`: If a Banach-valued integrand is Cʲ in a spatial parameter, its derivatives through j are measurable in the integration variable and all have one integrable majorant, then its integral is Cʲ and every derivative through j passes under the integral.

**Convolution preserves derivatives.** Proved result `conv_contDiff`: Under the stated hypotheses, integrable convolutions preserve derivatives.

**Kernel mass controls convolution norms.** Proved result `conv_norm_le`: For an integrable scalar kernel κ and a vector-valued G bounded by M, |∫κ(w)G(x−sw)dw|≤M∫|κ| for every scale s and point x.

**Scaled convolutions are continuous.** Proved result `conv_continuous`: For an integrable kernel κ and bounded continuous Banach-valued G, the scaled convolution (s,x)↦∫κ(w)G(x−sw)dw is jointly continuous.

**Kernel rescaling gives its Jacobian.** Proved result `scale_integral`: For s>0, the change of variables z=x−sw gives ∫s⁻⁴κ((x−z)/s)q(z)dz=s⁻¹∫κ(w)q(x−sw)dw.

**Kernel values rescale from time one.** Proved result `kernel_re`: For α>0 and t>0, the real kernel at (t,y) equals t^(−2/α) times its time-one value at t^(−1/(2α))y, assuming the kernel-decay interface.

**Coordinates reconstruct each vector.** Proved result `basis_expand`: Every real vector v is reconstructed from the coordinate sum ∑ₐvₐeₐ.

**Joint scaling preserves continuity.** Proved result `cont_scaled`: For an integrable kernel κ and bounded continuous G, (t,x)↦∫κ(w)G(x−tᵍw)dw is continuous for t>0, for every real exponent g.

**Source namespace:** `Breakdown.FracCert`.

**Kernel decay gives heat regularity.** Proved result `heatDivRegular_of`: Under the stated assumptions, this establishes that for 1<α<5/4 and 0≤β<3, a Cʲ tensor with bounded jth derivative and a β-weighted value bound has Cʲ heat-divergence convolutions, jointly continuous derivatives through order j and bounds Ct^(−1/(2α))(A+B) for 0< t≤1.

**Heat-divergence regularity holds.** Proved result `heatDivRegular`: Under the stated assumptions, this establishes that for 1<α<5/4 and 0≤β<3, a Cʲ tensor with bounded jth derivative and a β-weighted value bound has Cʲ heat-divergence convolutions, jointly continuous derivatives through order j and bounds Ct^(−1/(2α))(A+B) for 0< t≤1.

### Breakdown.FracCert.HeldExists

Solves the nonlinear held equation by contraction inside the certificate radius, using the bordered inverse and the a priori estimate.

This belongs to the fractional certificate route: held solutions, multiplier cancellation and nontrivial profiles give an analogue of the a posteriori strategy in paper §7; its fractional conclusions are outside the paper's stated ordinary-dissipation argument.

Source: `lean/Breakdown/FracCert/HeldExists.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak fractional powers admit differences.** Proposition `WeakPowerSubStatement`: This proposition requires that for 1<α<5/4, subtracting two L⁶ fields with weak fractional powers subtracts their weak fractional powers.

**defect gives an admissible right side.** Proposition `DefectRightSideStatement`: This proposition requires that a valid fractional certificate makes its defect square integrable and makes minus that defect minus the correction convection an admissible symmetry-class forcing.

**Source namespace:** `Breakdown.FracInternal.HeldExists`.

**The components of a held state.** Structure `HeldState`: This structure stores a correction velocity, its candidate first and second derivatives, a candidate fractional power and a finite vector of multiplier corrections.

**The zero held state.** Definition `zero`: This defines the held state whose velocity, derivatives, fractional power and multiplier corrections are all zero.

**Distance between two held states.** Definition `dsz`: This defines the distance of two held states by applying the certificate size to the differences of their first derivatives, second derivatives and multipliers.

**The size of a held state.** Definition `sz`: This defines the size of a held state by applying the certificate size to its two derivative fields and its multiplier vector.

**Axial turns preserve differences.** Proved result `axialTurn_sub`: For real vectors a and b, J(a−b)=Ja−Jb. Source: `Breakdown.FracCert.HeldExists:46`.

**Gradient fields admit negatives.** Proved result `isGradientField_neg`: Under the stated hypotheses, negatives of gradient fields are gradients.

**The zero field is a gradient.** Proved result `isGradientField_zero`: The zero vector field is the weak gradient of the zero potential and satisfies the local square-integrability requirements.

**The zero field is second order.** Proved result `secondOrder_zero`: The zero velocity, gradient and Hessian satisfy the second-order field conditions for every symmetry order m.

**The zero held state has zero size.** Proved result `size_zero`: A held state with zero velocity, derivatives and actuator coefficients has certificate size zero.

**Negation preserves certificate size.** Proved result `size_neg`: Changing the signs of G, H and all actuator coefficients κ leaves the certificate size √(E(G,H)+μ²|κ|²) unchanged.

**Distance from zero equals size.** Proved result `dsz_zero_right`: The certificate distance from a held state to the zero state equals the size of that held state.

**Held-state distance is symmetric.** Proved result `dsz_comm`: The certificate distance computed from the difference of two held states is symmetric in those states.

**Held-state distance is nonnegative.** Proved result `dsz_nonneg`: The certificate distance between any two held states is nonnegative.

**Certificate energy is nonnegative.** Proved result `energy_nonneg`: For a valid certificate, E(G,H)=∫|tr H|²+∫w|G|² is nonnegative for any gradient and Hessian fields. Source: `Breakdown.FracCert.HeldExists:97`.

**Squared size controls energy.** Proved result `energy_le`: For a valid certificate, E(G,H)≤S², where S=√(E(G,H)+μ²|κ|²) is the size including the actuator coefficients.

**Size controls the square-root energy.** Proved result `sqrt_energy_le`: For a valid certificate, √E(G,H)≤√(E(G,H)+μ²|κ|²).

**The concrete L² norm is the Lp norm.** Proved result `l2Norm_eq`: For a square-integrable field F, √(∫|F|²) agrees with its usual L² norm. Source: `Breakdown.FracCert.HeldExists:118`.

**The concrete L² norm is nonnegative.** Proved result `l2Norm_nonneg`: For every vector field F, √(∫|F|²) is nonnegative. Source: `Breakdown.FracCert.HeldExists:125`.

**L² differences obey a triangle bound.** Proved result `l2Norm_sub_le`: Under the stated hypotheses, L² difference norms obey a triangle bound.

**One norm is bounded by another and error.** Proved result `l2Norm_le_add_sub`: For F,F′∈L², ‖F‖₂≤‖F′‖₂+‖F−F′‖₂.

**Bounds for convection differences.** Proved result `product_bound`: Under the stated hypotheses, nonlinear differences have a product bound.

**The quadratic term is energy controlled.** Proved result `product_self`: For a valid certificate and an admissible field u, the nonlinear term satisfies ‖(u·∇)u‖₂≤Cₚᵣₒd E(u), where Cₚᵣₒd is the certificate's product constant.

**L² Cauchy sequences converge.** Proved result `l2_limit`: Every sequence of L² vector fields that is Cauchy in the L² norm has an L² limit F₀ with ∫|Fₙ−F₀|²→0.

**L² limits agree almost everywhere.** Proved result `l2_unique`: If an L² sequence converges to F₀ in squared-integral distance and to F₁ in L² norm, with both limits in L², then F₀=F₁ almost everywhere.

**The scalar radius bound is monotone.** Proved result `g_mono`: For D>0, the function g(A,y)=A/2+√(A²/4+y²/D) is increasing in each variable on A,y≥0.

**The scalar radius bound is subadditive.** Proved result `g_add`: For D>0, g(A,y)=A/2+√(A²/4+y²/D) satisfies g(A₁+A₂,y₁+y₂)≤g(A₁,y₁)+g(A₂,y₂) for all real inputs.

**The scalar bound scales positively.** Proved result `g_smul`: For x≥0, g(xA,xy)=xg(A,y), where g(A,y)=A/2+√(A²/4+y²/D).

**The inverse bound is nonnegative.** Proved result `bc_nonneg`: If the coercivity parameter is nonnegative and 0≤θ<1, the inverse-estimate expression with zero pin input is nonnegative for every pair of residual inputs x,y.

**The inverse bound splits additively.** Proved result `bc_split`: With nonnegative scale and coercivity parameters and 0≤θ<1, bounds 0≤X≤a+x and 0≤Y≤b+xR imply B(X,Y,0)≤B(a,b,0)+xB(1,R,0) for a,b,x,R≥0, where B is the certificate inverse-estimate expression.

**Almost equality preserves L² norms.** Proved result `l2Norm_congr_ae`: Vector fields equal almost everywhere have equal quantities √(∫|F|²).

**L² fields pair integrably.** Proved result `inner_integrable`: For X,e∈L²(ℝ³), the pointwise inner product X·e is integrable. Source: `Breakdown.FracCert.HeldExists:348`.

**L² inner products equal integrals.** Proved result `inner_toLp`: For f,g∈L², their Hilbert-space inner product is ∫f(y)·g(y)dy.

**Residual pairings obey a triangle bound.** Proved result `pair_triangle`: With X,e∈L², the integral pairing obeys |⟨−Z−X,e⟩|≤|⟨Z,e⟩|+|⟨X,e⟩| for any Z, using the convention that a nonintegrable pairing is assigned value zero.

**Row sizes obey a triangle bound.** Proved result `rowSize_le`: If row weights τₐ are nonnegative and |⟨F,eₐ⟩|≤|⟨Z,eₐ⟩|+|⟨X,eₐ⟩| for every row, the weighted Euclidean norm of F's row pairings is at most the sum of those for Z and X.

**The row maximum bounds all rows.** Proved result `rows_le`: For a valid certificate and X∈L², the weighted row size is bounded by √T‖X‖₂, where T is the certificate's row bound.

**A priori bounds control the held size.** Proved result `apriori_rhs`: Assuming closure of pressure gradients under addition and the a priori estimate, a valid certificate with 1<α<5/4 bounds a zero-pin linear state by S≤B(a,b,0)+Cᵣ‖X‖₂ when its full linear residual is −Y−X modulo a pressure gradient. Here p lies in the parameter box, X,Y∈L², and a,b bound the projected L² and row sizes of Y.

**The zero input has zero inverse bound.** Proved result `boundFn_zero`: The certificate inverse-estimate function satisfies B(0,0,0)=0.

**The projected zero norm vanishes.** Proved result `projectedNorm_zero`: The infimum of the L² sizes of pressure-gradient corrections to the zero field is at most zero, by choosing the zero correction.

**Rows of the zero field vanish.** Proved result `rowsModGrad_zero`: The infimum of row sizes of pressure-gradient corrections to the zero field is at most zero.

**Linear states admit differences.** Proved result `lin_sub`: Assuming linearity of the second-order field class and subtraction for weak fractional powers, two linear states at the same parameter p have a difference that is again a linear state when 1<α<5/4.

**The full linear field admits differences.** Proved result `fullField_sub`: At fixed α and p, the full linearized field of the difference of two velocities, derivative fields, fractional powers and actuator coefficient vectors equals the difference of their full linearized fields pointwise.

**Matrix-entry pairings are integrable.** Proved result `entryInner_integrable`: For measurable matrix fields G and χ with integrable squared Frobenius norms, the matrix pairing G:χ is integrable.

**Pins preserve differences.** Proved result `pins_sub`: For a valid certificate and two admissible fields, each pin satisfies ℓᵢ(G−G′)=ℓᵢ(G)−ℓᵢ(G′).

**The held radius gives a contraction.** Proved result `radius_facts`: A valid certificate gives r≥0, ρ+CᵣLr²≤r and 2CᵣLr<1 for its held radius r, residual size ρ, inverse row constant Cᵣ≥0 and nonlinear constant L.

**Source namespace:** `Breakdown.SteadyCert`.

**A held nonlinear solution exists.** Proved result `heldExists`: Under the stated assumptions, this establishes that for a valid fractional certificate and every parameter in its box, a held nonlinear solution exists with correction size at most the certified held radius.

### Breakdown.FracCert.HeldLimit

Passes bounded held solutions to a limit, retaining symmetry and identifying gradient residuals through solenoidal test pairings.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldLimit.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldLimitInternal`.

**L² fields pair integrably.** Proved result `inner_integrable`: The scalar product of two L² vector fields is integrable on ℝ³. Source: `Breakdown.FracCert.HeldLimit:16`.

**Negatives of gradients are gradients.** Proved result `gradient_neg`: The negative of a locally square-integrable weak gradient is the weak gradient of the negative potential. Source: `Breakdown.FracCert.HeldLimit:22`.

**Orthogonality characterizes gradients.** Proved result `recover`: Under the stated hypotheses, solenoidal orthogonality gives a gradient.

**Held residuals kill solenoidal tests.** Proved result `residual_orthogonal`: Under the stated hypotheses, held residuals annihilate solenoidal fields.

**Multipliers split from the residual.** Proved result `residual_split`: The held residual with actuator coefficients κ equals its zero-coefficient residual plus ∑ᵢκᵢbᵢ, pointwise.

**Residual pairings split by multiplier.** Proved result `residual_pair`: If the zero-coefficient held residual, the actuator fields and ζ all belong to L², pairing the residual with ζ separates into the zero-coefficient pairing plus ∑ᵢκᵢ∫bᵢ·ζ.

**Certificate energy is nonnegative.** Proved result `energy_nonneg`: For a valid certificate, the energy ∫|tr H|²+∫w|G|² is nonnegative for all G and H. Source: `Breakdown.FracCert.HeldLimit:102`.

**Size splits into energy and multipliers.** Proved result `size_sq`: Under the stated hypotheses, squared size splits energy and multipliers.

**Size bounds each multiplier coordinate.** Proved result `coord_bound`: For a valid certificate, a state-size bound S≤R implies μ|κᵢ|≤R for each actuator coefficient, where μ>0 is its multiplier scale.

**The held residual expands into its terms.** Proved result `residual_terms`: The held residual expands as the drift of v and Wₚ, their weak fractional powers, the convection (∇Wₚ+G)(Wₚ+v), and the forcing ∑ᵢ(λᵢ(p)+κᵢ)bᵢ.

**The discrete turn as a linear map.** Definition `turnLin`: This equips rotation through the discrete symmetry angle 2π/m with its real linear map structure.

**Reflection as a linear map.** Definition `mirrorLin`: This equips reflection of the third coordinate with its real linear map structure.

**axial turn commutes with discrete turns.** Proved result `axial_turn`: The axial generator commutes with the discrete rotation through 2π/m: JR₂π⁄ₘz=R₂π⁄ₘJz.

**The axial turn commutes with reflection.** Proved result `axial_mirror`: The axial generator commutes with reflection across the horizontal plane.

**Basis pairings determine vectors.** Proved result `vec_ext`: Two vectors in ℝ³ are equal if their inner products with each coordinate basis vector agree.

**Weak powers preserve orthogonal symmetry.** Proved result `power_equivariant`: If v is equivariant almost everywhere under an isometry R and P is its L² weak fractional power, then P(Ry)=RP(y) almost everywhere as well.

**The discrete turn as an isometry.** Definition `turnIsom`: This equips the discrete axial turn with its norm-preserving linear equivalence structure.

**Reflection as an isometry.** Definition `mirrorIsom`: This equips reflection of the third coordinate with its norm-preserving linear equivalence structure.

**The isometry rotates through 2π/m.** Proved result `turnIsom_apply`: The discrete-turn isometry acts as the axial rotation through 2π/m used in the symmetry class.

**The mirror isometry reflects vectors.** Proved result `mirrorIsom_apply`: The reflection isometry used here acts by (y₁,y₂,y₃)↦(y₁,y₂,−y₃).

**Coordinates reconstruct each vector.** Proved result `sum_unit`: Every real vector w equals ∑ⱼwⱼeⱼ. Source: `Breakdown.FracCert.HeldLimit:258`.

**Linear maps expand in a basis.** Proved result `clm_sum`: For any bounded linear map L from ℝ³ into a real normed space, Lw=∑ⱼwⱼL(eⱼ).

**Test derivatives are continuous.** Proved result `dir_continuous`: For a smooth compactly supported scalar test φ, its derivative in any fixed direction w is continuous.

**Test derivatives have compact support.** Proved result `dir_support`: For a smooth compactly supported scalar test φ, its derivative in any fixed direction w has compact support.

**Weak gradients work in every direction.** Proved result `weak_dir`: If v and the columns of its weak gradient G are locally integrable, then ∫Dφ(y)[w]v(y)dy=−∫φ(y)G(y)wdy for every smooth compactly supported φ and every constant direction w.

**Weak gradients preserve spatial symmetry.** Proved result `gradient_equivariant`: If v is locally integrable, G is its weak gradient with L² columns and v(Ry)=Rv(y) almost everywhere for an isometry R, then G(Ry)Rw=RG(y)w for every w at almost every y.

**The residual preserves spatial symmetry.** Proved result `residual_at`: If a linear spatial symmetry commutes with the axial generator and the velocity, profile, fractional powers, gradients and actuators transform equivariantly at y, then the held residual transforms equivariantly at y too.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak powers remain in their class.** Proved result `weakPowerClass_holds`: Under the stated assumptions, this establishes that for 1<α<5/4, a measurable L⁶ field in the discrete rotation and reflection class has its weak fractional power in the same class.

**Weak gradients retain class symmetry.** Proved result `gradientClass_holds`: Under the stated assumptions, this establishes that a measurable L⁶ field in the symmetry class with a measurable square-integrable weak gradient has that gradient equivariant almost everywhere under the discrete turn and reflection.

**The held residual retains its class.** Proved result `heldResidualClass_of`: Under the stated assumptions, this establishes that for a valid fractional certificate, the held residual of every admissible linear correction state preserves the prescribed symmetry class.

**The held residual lies in L².** Proved result `heldResidualSquare_of`: Under the stated assumptions, this establishes that for a valid fractional certificate and a linear correction state in the parameter box, every held residual belongs to L² and to the prescribed symmetry class.

**Held solutions have weak limits.** Proved result `heldWeakLimit_of`: Under the stated assumptions, this establishes that bounded held solutions at convergent parameters have a subsequence with a limiting linear state, no larger size, convergent multipliers and pins, and convergent residual pairings against every solenoidal L² field.

**The held solution relation is closed.** Proved result `heldLimit_of`: Under the stated assumptions, this establishes that for a valid fractional certificate, held solutions within the certified radius at convergent parameters have a subsequence with convergent multipliers and a held-solution limit within the same radius.

### Breakdown.FracCert.HeldLimitParts

Names the residual and the weak compactness, symmetry and lower-bound contracts needed to close the held-solution relation.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldLimitParts.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.FracCertData`.

**The full nonlinear held residual.** Definition `heldResidual`: This defines the held residual as the full bordered linear field plus the correction convection Gv and the profile defect.

**Source namespace:** `Breakdown.SteadyCert`.

**Held residuals are L² class fields.** Proposition `HeldResidualSquareStatement`: This proposition requires that for a valid fractional certificate and a linear correction state in the parameter box, every held residual belongs to L² and to the prescribed symmetry class.

**Bounded held solutions have weak limits.** Proposition `HeldWeakLimitStatement`: This proposition requires that bounded held solutions at convergent parameters have a subsequence with a limiting linear state, no larger size, convergent multipliers and pins, and convergent residual pairings against every solenoidal L² field.

**Weak powers preserve the symmetry class.** Proposition `WeakPowerClassStatement`: This proposition requires that for 1<α<5/4, a measurable L⁶ field in the discrete rotation and reflection class has its weak fractional power in the same class.

**Weak gradients preserve class symmetry.** Proposition `GradientClassStatement`: This proposition requires that a measurable L⁶ field in the symmetry class with a measurable square-integrable weak gradient has that gradient equivariant almost everywhere under the discrete turn and reflection.

**Held residuals preserve class symmetry.** Proposition `HeldResidualClassStatement`: This proposition requires that for a valid fractional certificate, the held residual of every admissible linear correction state preserves the prescribed symmetry class.

**Weak held limits retain energy bounds.** Proposition `HeldStateLimitStatement`: This proposition requires that bounded held solutions at convergent parameters have a linear-state subsequential limit with lower semicontinuous energy, weakly convergent gradients and convergent zero-multiplier residual pairings against solenoidal L² fields.

### Breakdown.FracCert.HeldMultiplierContinuous

Combines bounded existence, uniqueness and closedness to make the held multipliers continuous in the certificate parameter.

This belongs to the fractional certificate route: held solutions, multiplier cancellation and nontrivial profiles give an analogue of the a posteriori strategy in paper §7; its fractional conclusions are outside the paper's stated ordinary-dissipation argument.

Source: `lean/Breakdown/FracCert/HeldMultiplierContinuous.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldMultiplierContinuousInternal`.

**State size controls square-root energy.** Proved result `sqrt_energy_le_size`: For any certificate data, √E(G,H)≤√(E(G,H)+μ²|κ|²), so the state size bounds the square-root energy.

**Certificate size is nonnegative.** Proved result `size_nonneg`: The state size √(E(G,H)+μ²|κ|²) is nonnegative for every G,H and κ.

**The held radius has a linear bound.** Proved result `held_radius_le`: If the held radius r is nonnegative, its defining quadratic formula gives r≤2ρ, where ρ is the residual-size bound.

**The held ball satisfies uniqueness.** Proved result `unique_condition`: For a valid certificate, any two states of size at most the held radius satisfy (√E+√E′)CᵣL<1, the smallness condition used in the uniqueness estimate.

**Source namespace:** `Breakdown.SteadyCert`.

**The held multipliers vary continuously.** Proved result `heldMultiplierContinuous`: Under the stated assumptions, this establishes that a valid fractional certificate admits a continuous corrected multiplier map on its parameter box, with each value realized by a held solution within the certified radius.

### Breakdown.FracCert.HeldNonzero

Uses the certificate energy gap to exclude cancellation of the approximate profile by the correction.

This belongs to the fractional certificate route: held solutions, multiplier cancellation and nontrivial profiles give an analogue of the a posteriori strategy in paper §7; its fractional conclusions are outside the paper's stated ordinary-dissipation argument.

Source: `lean/Breakdown/FracCert/HeldNonzero.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldNonzeroInternal`.

**Integration by parts for smooth fields.** Proved result `partsIdentity`: Under the stated hypotheses, smooth fields satisfy integration by parts.

**Matrix-entry energy is nonnegative.** Proved result `entrySq_nonneg`: The squared Frobenius norm ∑ᵢ|Geᵢ|² of a matrix G is nonnegative. Source: `Breakdown.FracCert.HeldNonzero:34`.

**Cancellation fixes the gradient energy.** Proved result `gradient_ae_eq`: Under the stated hypotheses, cancellation identifies gradient energies.

**Source namespace:** `Breakdown.SteadyCert`.

**The corrected profile is nonzero.** Proved result `heldNonzero`: Under the stated assumptions, this establishes that for a valid fractional certificate, a held correction within the certified radius cannot cancel the approximate profile almost everywhere.

### Breakdown.FracCert.HeldResidualLimit

Identifies the weak limit of the nonlinear held residual, using a locally strong subsequence and separate drift and product limits.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldResidualLimit.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldResidualLimitInternal`.

**Almost every spatial point is nonzero.** Proved result `ae_ne_zero`: The point y=0 has Lebesgue measure zero in ℝ³, so y≠0 almost everywhere. Source: `Breakdown.FracCert.HeldResidualLimit:27`.

**The inverse-radius field lies in L².** Proved result `inv_memLp`: For an admissible second-order field v, the inverse-radius weighted field v(y)/|y| belongs to L²(ℝ³).

**Removing the radius recovers L².** Proved result `weight_memLp`: If y↦|y|w(y) is an admissible second-order field, then w∈L²(ℝ³).

**The held residual splits into four parts.** Proved result `residual_parts`: The held residual is the sum of drift plus fractional power, the approximate-profile defect, the three convection terms (∇Wₚ)v+GWₚ+Gv, and the actuator correction ∑ᵢκᵢbᵢ.

**The residual expands into profile terms.** Proved result `residual_expand`: Expanding the defect combines the held residual into the drift and fractional power of Wₚ+v, the convection (∇Wₚ+G)(Wₚ+v), and the actuator coefficients λ(p)+κ. Source: `Breakdown.FracCert.HeldResidualLimit:58`.

**The held residual lies in L².** Proved result `residual_memLp`: For 1<α<5/4 and a valid certificate, every linear state at p in the parameter box has an L² held residual for every actuator coefficient vector κ. Source: `Breakdown.FracCert.HeldResidualLimit:72`.

**The convection cross terms lie in L².** Proved result `cross_memLp`: For 1<α<5/4, a valid certificate, p in its box and an admissible field v, the sum (∇Wₚ)v+GWₚ+Gv belongs to L².

**The profile defect lies in L².** Proved result `defect_memLp`: For 1<α<5/4, a valid certificate and p in its box admitting a linear state, the approximate-profile defect at p belongs to L².

**Residual pairings split into four parts.** Proved result `pair_parts`: For a valid certificate with 1<α<5/4, a linear state at p in its box and ζ∈L², the residual pairing splits into the drift-plus-power, profile-defect, convection and actuator pairings.

**Held residuals kill solenoidal tests.** Proved result `held_orthogonal`: Under the stated hypotheses, held residuals annihilate solenoidal fields. Source: `Breakdown.FracCert.HeldResidualLimit:132`.

**Integration respects a four-term sum.** Proved result `combine4`: For integrable scalar f₁,f₂,f₃,f₄, integration of c₁f₁+c₂f₂+a(f₃−f₄) equals c₁∫f₁+c₂∫f₂+a(∫f₃−∫f₄).

**Drift test pairings pass to the limit.** Proved result `drift_test_limit`: If aₙ→a₀, measurable matrix fields Gₙ converge weakly in L² to G₀ with uniformly bounded energy, and measurable uₙ converge strongly to u₀ in L² on every ball, then their drift pairings against each smooth compactly supported vector test converge to the limiting drift pairing. All velocities are assumed locally square-integrable, and the limiting pairing is integrable.

**Matrix-vector products are locally L¹.** Proved result `apply_locInt`: A measurable matrix field with finite squared Frobenius integral, applied to a continuous vector field, is integrable on every compact set.

**The drift field is locally integrable.** Proved result `drift_locInt`: If v∈L⁶ and G is a measurable matrix field with finite squared Frobenius integral, their dilation-and-rotation drift is locally integrable for every α and a.

**Weak limits identify the drift field.** Proved result `drift_identify`: Suppose admissible second-order fields uₙ and v₀ of the same symmetry order satisfy uₙ→v₀ in L² on every ball, ∇uₙ⇀∇v₀ in L² with uniformly bounded energy, and aₙ→a₀. If D₀∈L² and the drift pairings ∫Dα,aₙuₙ·g converge to ∫D₀·g for every g∈L², then D₀=Dα,a₀v₀ almost everywhere, with nonintegrable pairings assigned value zero.

**Source namespace:** `Breakdown.SteadyCert.LocalStrongInternal`.

**Ball integrals equal cutoff integrals.** Proved result `ind_sq`: For any ball Bᵣ, ∫ over Bᵣ |f−g|² equals the whole-space integral of |1_Bᵣf−1_Bᵣg|².

**Ball restrictions of the field lie in L².** Proved result `ind_memLp`: Truncating an admissible second-order velocity to any ball gives a global L² field.

**Radius-weighted cutoffs lie in L².** Proved result `ind_weight_memLp`: If w∈L², then the field |y|w(y) truncated to any ball belongs to L².

**Weighted weak limits give local tests.** Proved result `ball_weak`: If uₙ/|y| converges against every L² test to w₀, then uₙ converges against each L² test supported inside Bᵣ to |y|w₀, for every r.

**Ball energy is lower semicontinuous.** Proved result `lsc_ball`: If uₙ converges weakly to a₀ against L² tests supported in Bᵣ and uₙ,a₀,b are square-integrable there, then infinitely many bounds ∫ over Bᵣ |uₙ−b|²<ε imply ∫ over Bᵣ |a₀−b|²≤ε.

**Second-order fields are locally L².** Proved result `loc_memLp`: An admissible second-order velocity belongs to L² on every ball in ℝ³.

**Radius-weighted L² fields are locally L².** Proved result `loc_weight_memLp`: Multiplying an L² field by |y| preserves square integrability on each bounded ball.

**Local difference squares are integrable.** Proved result `sq_int`: If f and g are square-integrable on Bᵣ, the scalar function |f−g|² is integrable on Bᵣ.

**Matrix differences have finite energy.** Proved result `entry_int`: Under the stated hypotheses, matrix difference energies are integrable.

**Finite local nets give small errors.** Proved result `frequent_small`: For admissible uₙ with uₙ/|y| weakly converging to w₀∈L², finite ε-nets for the velocities and gradients on Bᵣ imply that ∫ over Bᵣ |uₙ−|y|w₀|²<4ε occurs for infinitely many n, for every ε>0.

**Source namespace:** `Breakdown.SteadyCert`.

**A locally strong subsequence exists.** Proved result `localStrongSubseq`: Under the stated assumptions, this establishes that uniformly energy-bounded second-order fields whose inverse-radius velocities converge weakly in L² have a subsequence converging strongly on every ball to the radius times that weak limit.

**Local strong limits close the residual.** Proved result `heldResidualLimit_of`: Under the stated assumptions, this establishes that under the boundedness and weak-convergence hypotheses for held solutions, the residual of the limiting linear state with the limiting multiplier annihilates every solenoidal L² field.

**The held residual limit interface holds.** Proved result `heldResidualLimit_holds`: Under the stated assumptions, this establishes that under the boundedness and weak-convergence hypotheses for held solutions, the residual of the limiting linear state with the limiting multiplier annihilates every solenoidal L² field.

### Breakdown.FracCert.HeldResidualLimitParts

States the compactness step that upgrades a weighted weak limit and bounded derivative energy to strong L² convergence on every ball.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldResidualLimitParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**A locally strong subsequence exists.** Proposition `LocalStrongSubseqStatement`: This proposition requires that uniformly energy-bounded second-order fields whose inverse-radius velocities converge weakly in L² have a subsequence converging strongly on every ball to the radius times that weak limit.

### Breakdown.FracCert.HeldStateLimitAApply

Controls matrix-vector pairings and passes them to the limit when matrix fields converge weakly and vectors converge locally strongly.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitAApply.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.ApplyPairingInternal`.

**Cauchy-Schwarz bounds integral pairings.** Proved result `abs_pair_le`: For f,g∈L², |∫f·g|≤(∫|f|²)¹ᐟ²(∫|g|²)¹ᐟ². Source: `Breakdown.FracCert.HeldStateLimitAApply:16`.

**The first basis vector has unit norm.** Proved result `unit_norm`: The first coordinate basis vector in ℝ³ has Euclidean norm one.

**Matrix-vector evaluation is measurable.** Proved result `apply_meas`: If a matrix field A and a vector field b are measurable, then y↦A(y)b(y) is measurable.

**Matrix entries control operator action.** Proved result `apply_norm_le`: For every matrix A and vector x, |Ax|≤(∑ᵢ|Aeᵢ|²)¹ᐟ²|x|.

**Local L² norms bound test pairings.** Proved result `small_bound`: If A has finite squared Frobenius integral, b is measurable and square-integrable on Bᵣ, and continuous ψ is supported there with |ψ|≤M, then (Ab)·ψ is integrable and |∫(Ab)·ψ|≤‖A‖₂M‖b‖_{L²(Bᵣ)}.

**Basis inner products give coordinates.** Proved result `unit_inner`: For x∈ℝ³, its inner product with eᵢ equals its ith coordinate.

**A difference square has a two-term bound.** Proved result `sub_sq_le`: For vectors x,z∈ℝ³, |x−z|²≤2|x|²+2|z|².

**Rank-one test matrices are measurable.** Proved result `frame_meas`: If a₀ is measurable and ψ is continuous, the rank-one matrix field h↦(a₀(y)·h)ψ(y) is measurable.

**Rank-one action is ⟨x,w⟩v.** Proved result `frame_apply`: The rank-one operator built from x and v sends w to ⟨x,w⟩v.

**Matrix pairings represent vector action.** Proved result `frame_entry`: For a matrix B and vectors x,v, its Frobenius pairing with the rank-one matrix h↦(x·h)v equals (Bx)·v.

**Rank-one matrix energy is bounded.** Proved result `frame_sq`: The rank-one matrix h↦(x·h)v has squared Frobenius norm at most 3|x|²|v|².

**Weak-strong products converge on tests.** Proved result `apply_pairing_limit`: Under the stated hypotheses, weak and strong factors give pairing limits.

### Breakdown.FracCert.HeldStateLimitACross

Combines uniform L² control of convection cross terms with convergence against compact test fields.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitACross.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**The convection cross terms stay bounded.** Proposition `CrossUniformBoundStatement`: This proposition requires that a valid fractional certificate and a common energy bound give a uniform L² bound on the profile-correction cross convection together with the correction self-convection.

**Cross terms converge against tests.** Proposition `CrossTestLimitStatement`: This proposition requires that under parameter convergence, bounded derivative energy, weak gradient convergence and local strong L² velocity convergence, the three convection terms converge in pairing against every compact test field.

**Test limits extend to L² pairings.** Proved result `crossPairingLimit_of`: Under the stated assumptions, this establishes that under parameter convergence, bounded derivative energy, weak gradient convergence and local strong velocity convergence, the convection cross terms and correction convection converge against every solenoidal L² field.

**Inverse-square bounds from profile decay.** Proved result `decay_sq_le`: Under the stated hypotheses, profile decay has an inverse-square bound.

**Three-term squares have a sum bound.** Proved result `sum3_sq_le`: For a,b,c∈ℝ³, |a+b+c|²≤3(|a|²+|b|²+|c|²).

**The uniform cross-term bound holds.** Proved result `crossUniformBound`: Under the stated assumptions, this establishes that a valid fractional certificate and a common energy bound give a uniform L² bound on the profile-correction cross convection together with the correction self-convection.

### Breakdown.FracCert.HeldStateLimitADefect

Separates parameter continuity of the defect into free-profile, nonlinear-profile and multiplier contributions.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitADefect.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Free-profile pairings pass to the limit.** Proposition `ProfileFreePairingLimitStatement`: This proposition requires that under convergence within the certificate parameter box, the approximate profile drift plus fractional power converges in pairing against every solenoidal L² field.

**The free-profile part stays L² bounded.** Proposition `ProfileFreeBoundStatement`: This proposition requires that the free part of a valid certificate profile has uniformly bounded squared L² norm throughout the parameter box.

**Free-profile test pairings converge.** Proposition `ProfileFreeTestLimitStatement`: This proposition requires that under convergence within the certificate parameter box, the approximate profile drift plus fractional power converges in pairing against every compact test field.

**Test limits give free-profile pairings.** Proved result `profileFreePairingLimit_of`: Under the stated assumptions, this establishes that under convergence within the certificate parameter box, the approximate profile drift plus fractional power converges in pairing against every solenoidal L² field.

**Source namespace:** `Breakdown.SteadyCert.DefectPairingInternal`.

**Profile decay controls matrix action.** Proved result `decay_le`: If y≠0 and ‖A‖≤C(1+|y|)⁻², then |Ax|²≤C²|x|²/|y|² for every x.

**Profile products converge weakly.** Proved result `product_limit`: For a valid certificate with 1<α<5/4, if pₙ→q within its parameter box, the self-convection fields (Wₚₙ·∇)Wₚₙ converge against every L² test to (Wq·∇)Wq.

**Each profile multiplier is continuous.** Proved result `multiplier_limit`: For a valid certificate, each prescribed profile multiplier λᵢ(pₙ) converges to λᵢ(q) whenever pₙ→q within the parameter box.

**Source namespace:** `Breakdown.SteadyCert`.

**Defect pairings pass to the limit.** Proved result `defectPairingLimit_of`: Under the stated assumptions, this establishes that the defect of a valid fractional certificate varies continuously in pairing against every solenoidal L² field as the parameter converges within its box.

### Breakdown.FracCert.HeldStateLimitAFree

Obtains uniform L² bounds on the free part of held and approximate profiles from solenoidal drift and power estimates.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitAFree.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.FreeBoundInternal`.

**The concrete L² norm is the Lp norm.** Proved result `l2Norm_eq`: For f∈L², √(∫|f|²) is its L² norm. Source: `Breakdown.FracCert.HeldStateLimitAFree:15`.

**L² norms obey the triangle inequality.** Proved result `l2_add_le`: For f,g∈L², ‖f+g‖₂≤‖f‖₂+‖g‖₂.

**Scaling multiplies L² norms by magnitude.** Proved result `l2_smul`: Multiplying a vector field by a real scalar c multiplies √(∫|f|²) by |c|.

**Finite L² sums have a norm bound.** Proved result `l2_sum_le`: For finitely many L² fields bᵢ and coefficients cᵢ, ‖∑ᵢcᵢbᵢ‖₂≤∑ᵢ|cᵢ|‖bᵢ‖₂, also when the sum is restricted to any subset of indices.

**The zero field is a gradient.** Proved result `gradient_zero`: The zero vector field is the weak gradient of the zero scalar potential.

**Source namespace:** `Breakdown.SteadyCert`.

**The held free part stays L² bounded.** Proved result `heldFreeBound_of`: Under the stated assumptions, this establishes that a common bound on held-state size gives a uniform squared L² bound on the sum of the correction drift and its fractional power.

**The parameter box is compact.** Proved result `box_compact`: Every finite-dimensional parameter box defined by |pᵢ|≤rᵢ is compact, including the empty case.

**The profile free part stays L² bounded.** Proved result `profileFreeBound_of`: Under the stated assumptions, this establishes that the free part of a valid certificate profile has uniformly bounded squared L² norm throughout the parameter box.

### Breakdown.FracCert.HeldStateLimitAParts

States a route to held-state compactness through free-part bounds, linear weak limits, nonlinear cross pairings and defect pairings.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitAParts.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**The held free part stays L² bounded.** Proposition `HeldFreeBoundStatement`: This proposition requires that a common bound on held-state size gives a uniform squared L² bound on the sum of the correction drift and its fractional power.

**Bounded linear states have weak limits.** Proposition `LinearStateWeakLimitStatement`: This proposition requires that energy-bounded linear states with uniformly L²-bounded drift and fractional power at convergent parameters admit a subsequence with lower semicontinuous energy, weak gradient convergence, local strong velocity convergence and weak convergence of the free part.

**Cross pairings pass to the limit.** Proposition `CrossPairingLimitStatement`: This proposition requires that under parameter convergence, bounded derivative energy, weak gradient convergence and local strong velocity convergence, the convection cross terms and correction convection converge against every solenoidal L² field.

**Defect pairings pass to the limit.** Proposition `DefectPairingLimitStatement`: This proposition requires that the defect of a valid fractional certificate varies continuously in pairing against every solenoidal L² field as the parameter converges within its box.

### Breakdown.FracCert.HeldStateLimitAProfile

Proves convergence of free-profile test pairings using continuity of the approximate profile and its weak fractional power.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitAProfile.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Profile-power test pairings converge.** Proposition `ProfilePowerTestLimitStatement`: This proposition requires that the approximate profile fractional power varies continuously in pairing against every compact test field as the certificate parameter converges within its box.

**Source namespace:** `Breakdown.SteadyCert.ProfileTestInternal`.

**Test fields are bounded and supported.** Proved result `test_bound`: Every smooth compactly supported vector test has a uniform bound M≥0 and vanishes outside some ball.

**Local matrix pairings are integrable.** Proved result `pair_int`: Under the stated hypotheses, local matrix-vector pairings are integrable.

**A constant matrix cut off to a ball.** Definition `cutoff`: This defines a field equal to the fixed vector L on the open ball of radius r and zero outside that ball.

**The matrix cutoff is measurable.** Proved result `cutoff_meas`: The matrix field equal to a fixed matrix L on Bᵣ and zero outside Bᵣ is measurable.

**The matrix cutoff has finite energy.** Proved result `cutoff_sq`: A constant matrix L truncated to Bᵣ has integrable squared Frobenius norm.

**The cutoff preserves supported pairings.** Proved result `cutoff_pair`: If ψ vanishes outside Bᵣ, replacing L by its truncation to Bᵣ leaves the pointwise pairing (Lx)·ψ(y) unchanged for all x,y.

**Local strong limits preserve pairings.** Proved result `fixed_pair_limit`: Under the stated hypotheses, local strong limits preserve test pairings.

**Fixed-matrix pairings are integrable.** Proved result `pair_int_fixed`: For any fixed matrix L, a measurable vector field b that is square-integrable on every ball has an integrable pairing (Lb)·ψ with every smooth compactly supported vector test ψ.

**Convergent profile gradients are bounded.** Proved result `grad_sq_bound`: Under the stated hypotheses, convergent profile gradients stay bounded.

**Integrals split into profile terms.** Proved result `combine`: Under the stated hypotheses, integration distributes over profile terms.

**Source namespace:** `Breakdown.SteadyCert`.

**Profile-power limits give free limits.** Proved result `profileFreeTestLimit_of`: Under the stated assumptions, this establishes that under convergence within the certificate parameter box, the approximate profile drift plus fractional power converges in pairing against every compact test field.

**Profile-power test limits hold.** Proved result `profilePowerTestLimit`: Under the stated assumptions, this establishes that the approximate profile fractional power varies continuously in pairing against every compact test field as the certificate parameter converges within its box.

### Breakdown.FracCert.HeldStateLimitATest

Turns certificate parameter continuity into local L² convergence of the profile and weak convergence of its gradients.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitATest.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Profile fields converge locally in L².** Proposition `ProfileLocalLimitStatement`: This proposition requires that the approximate profiles of a valid fractional certificate converge strongly in L² on every ball when their parameters converge within the box.

**Source namespace:** `Breakdown.SteadyCert.CrossTestInternal`.

**Differences of matrix columns lie in L².** Proved result `col_sub_memLp`: If measurable matrix fields A and B have finite squared Frobenius integrals, each column of A−B belongs to L².

**Matrix differences have finite energy.** Proved result `entrySq_sub_integrable`: Under the stated hypotheses, matrix difference energies are integrable.

**Strong matrix convergence implies weak.** Proved result `strong_weak`: Strong convergence of measurable matrix fields Aₙ to A₀ in squared Frobenius integral implies ∫Aₙ:E→∫A₀:E for every square-integrable matrix test E.

**Second-order fields have local energy.** Proved result `local_sq`: An admissible second-order velocity has finite squared-norm integral on every ball.

**Continuous fields have local energy.** Proved result `cont_sq`: A continuous vector field has finite squared-norm integral on every ball.

**Profile gradients converge in energy.** Proved result `grad_tendsto`: For a valid certificate and pₙ→q within its parameter box, ∫|∇Wₚₙ−∇Wq|²→0.

**Profile Hessians have finite L² energy.** Proved result `second_two_of`: For a valid certificate and p in its parameter box, the sum of the squared norms of all stored second-derivative entries of Wₚ is integrable.

**The profile is a second-order field.** Proved result `profile_second_order`: For a valid certificate with 1<α<5/4 and p in its box, Wₚ with its supplied gradient and Hessian satisfies the L⁶, L² derivative, solenoidality and symmetry requirements of the second-order field class.

**Source namespace:** `Breakdown.SteadyCert`.

**Profile fields converge locally in L².** Proved result `profileLocalLimit`: Under the stated assumptions, this establishes that the approximate profiles of a valid fractional certificate converge strongly in L² on every ball when their parameters converge within the box.

**Profile limits control cross-term tests.** Proved result `crossTestLimit_of`: Under the stated assumptions, this establishes that under parameter convergence, bounded derivative energy, weak gradient convergence and local strong L² velocity convergence, the three convection terms converge in pairing against every compact test field.

### Breakdown.FracCert.HeldStateLimitAWeak

Extends convergence against a dense class of test functions to all L² test fields using uniform bounds.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitAWeak.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert.WeakPairingInternal`.

**Dense tests determine weak limits.** Proved result `tendsto_inner_of_dense`: Under the stated hypotheses, dense tests determine bounded weak limits.

**Integral pairings equal L² pairings.** Proved result `pair_eq_inner`: For square-integrable vector fields f and g, ∫f·g equals their L² inner product. Source: `Breakdown.FracCert.HeldStateLimitAWeak:47`.

**L² norms square to integrals.** Proved result `norm_toLp_sq`: For f∈L², the square of its L² norm equals ∫|f|².

**Test-field limits extend to L² tests.** Proved result `tendsto_pair_of_tests`: If fₙ is uniformly bounded in L², f₀∈L² and ∫fₙ·ψ→∫f₀·ψ for every smooth compactly supported vector test ψ, the same convergence holds for every ζ∈L².

### Breakdown.FracCert.HeldStateLimitB

Constructs the held-state limit by bounding each residual component and retaining the zero solenoidal pairing.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitB.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**L² fields pair integrably.** Proved result `pair_integrable`: The pointwise scalar product of two L² vector fields is integrable. Source: `Breakdown.FracCert.HeldStateLimitB:19`.

**The residual expands into profile terms.** Proved result `residual_expand`: The held residual is the drift of v and Wₚ plus their fractional powers, the convection (∇Wₚ+G)(Wₚ+v), and the actuator forcing with coefficients λ(p)+κ. Source: `Breakdown.FracCert.HeldStateLimitB:25`.

**The held residual lies in L².** Proved result `residual_memLp`: For 1<α<5/4, a valid certificate and p in its parameter box, every admissible linear state has an L² held residual for all actuator coefficients κ. Source: `Breakdown.FracCert.HeldStateLimitB:39`.

**Multipliers split from the residual.** Proved result `residual_sum`: Changing the held coefficients from zero to κ adds exactly ∑ᵢκᵢbᵢ to the residual at every point.

**Residual pairings split by multiplier.** Proved result `residual_pairing`: If the zero-coefficient residual, ζ and all actuators belong to L², the residual pairing equals its zero-coefficient pairing plus ∑ᵢκᵢ∫bᵢ·ζ.

**Held residuals kill solenoidal tests.** Proved result `held_orthogonal`: Under the stated hypotheses, held residuals annihilate solenoidal fields. Source: `Breakdown.FracCert.HeldStateLimitB:76`.

**Certificate energy is nonnegative.** Proved result `energy_nonneg'`: For a valid certificate, E(G,H)=∫|tr H|²+∫w|G|² is nonnegative.

**Size bounds each multiplier coordinate.** Proved result `multiplier_coord_bound`: For a valid certificate, the state-size bound S≤R implies μ|κᵢ|≤R for every coefficient i.

**Uniform bounds give held-state limits.** Proved result `heldStateLimit_of_bounds`: Under the stated assumptions, this establishes that bounded held solutions at convergent parameters have a linear-state subsequential limit with lower semicontinuous energy, weakly convergent gradients and convergent zero-multiplier residual pairings against solenoidal L² fields.

**Second traces lie in L².** Proved result `trace_memLp'`: For an admissible second-order field, the trace of its weak Hessian lies in L².

**Weak identification gives bounded limits.** Proved result `heldBoundedLimit_of`: Under the stated assumptions, this establishes that bounded held solutions with convergent parameters and multipliers have a linear-state subsequential limit with lower semicontinuous energy, weak gradient convergence and a residual annihilating all solenoidal L² fields.

### Breakdown.FracCert.HeldStateLimitBBound

Derives uniform bounds for the fractional power and drift of a bounded held solution.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitBBound.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldBoundInternal`.

**The free bounds interface is proved.** Proved result `freeBoundsProved`: Under the stated assumptions, this establishes that for 1<α<5/4, a free solution with L² forcing has separate power and drift norms bounded by the forcing norm, the stated trace-pairing energy identity and a uniform bound on the sum of square-root gradient and trace energies.

**L² norms obey the triangle inequality.** Proved result `norm_add_le'`: For f,g∈L², their sum satisfies ‖f+g‖₂≤‖f‖₂+‖g‖₂.

**Scaling multiplies L² norms by magnitude.** Proved result `norm_smul'`: For a real c, √(∫|cf|²)=|c|√(∫|f|²).

**The zero field has zero L² norm.** Proved result `norm_zero'`: The zero vector field has √(∫|0|²)=0.

**Finite L² sums have a norm bound.** Proved result `norm_sum_le'`: A finite sum of L² fields belongs to L² and its norm is at most the sum of their norms.

**L² fields pair integrably.** Proved result `pair_integrable'`: If f,g∈L², then f·g belongs to L¹.

**Negatives of gradients are gradients.** Proved result `gradient_neg'`: If Q is a locally square-integrable weak gradient, −Q is a weak gradient with potential −q. Source: `Breakdown.FracCert.HeldStateLimitBBound:75`.

**The held residual lies in L².** Proved result `residual_memLp'`: For a valid certificate with 1<α<5/4, p in the parameter box and an admissible linear state, the held residual is square-integrable for every actuator coefficient vector.

**Source namespace:** `Breakdown.SteadyCert`.

**Held drift and power have uniform bounds.** Proved result `heldUniformBound_of`: Under the stated assumptions, this establishes that a uniform bound on held-state size gives separate uniform L² bounds on the correction fractional power and rotating drift.

### Breakdown.FracCert.HeldStateLimitBExports

Closes the held-state compactness interface after supplying the solenoidal free-operator estimate.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitBExports.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert`.

**Solenoidal estimates give held limits.** Proved result `heldStateLimit_b`: Under the stated assumptions, this establishes that bounded held solutions at convergent parameters have a linear-state subsequential limit with lower semicontinuous energy, weakly convergent gradients and convergent zero-multiplier residual pairings against solenoidal L² fields.

**The held-state limit interface is proved.** Proved result `heldStateLimitProved`: Under the stated assumptions, this establishes that bounded held solutions at convergent parameters have a linear-state subsequential limit with lower semicontinuous energy, weakly convergent gradients and convergent zero-multiplier residual pairings against solenoidal L² fields.

### Breakdown.FracCert.HeldStateLimitBExtract

Reassembles weak coordinate limits into derivative tensors and identifies the limiting linear state and residual.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitBExtract.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.WeakFieldLimit`.

**A Hessian rebuilt from its entries.** Definition `entryOp`: This reconstructs a second-order operator from its indexed vector entries using the spatial coordinate functionals.

**Rebuilt Hessians recover their entries.** Proved result `entryOp_apply`: Reconstructing a vector-valued bilinear form from entries hᵢⱼ gives H(y)[eᵢ,eⱼ]=hᵢⱼ(y).

**The rebuilt Hessian is measurable.** Proved result `entryOp_meas`: If all nine vector-valued entries hᵢⱼ are measurable, the bilinear-form field reconstructed from them is measurable.

**A Hessian rebuilt from operator columns.** Definition `opOp`: This reconstructs an operator-valued linear map from its three columns using the spatial coordinate functionals.

**Rebuilt Hessians recover their columns.** Proved result `opOp_apply`: Reconstructing a bilinear form from its three operator-valued columns cᵢ gives H(y)[eᵢ]=cᵢ(y).

**The rebuilt operator field is measurable.** Proved result `opOp_meas`: If the three operator-valued column fields cᵢ are measurable, the reconstructed bilinear-form field is measurable.

**Source namespace:** `Breakdown.SteadyCert`.

**Closed weak limits identify held states.** Proved result `heldLimitIdentify_of`: Under the stated assumptions, this establishes that bounded held solutions with convergent parameters and multipliers have a linear-state subsequential limit whose gradient columns and second trace converge weakly and whose residual annihilates all solenoidal L² fields.

**Four weak closures give residual closure.** Proved result `heldLimitClosure_of`: Under the stated assumptions, this establishes that the specified simultaneous weak limits of the weighted velocity, derivative entries, power and drift of bounded held solutions form a limiting linear state whose residual annihilates all solenoidal L² fields.

### Breakdown.FracCert.HeldStateLimitBParts

States the separate weak closure contracts for held states, second derivatives, fractional powers, drift and residuals.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitBParts.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert`.

**Held drift and power have uniform bounds.** Proposition `HeldUniformBoundStatement`: This proposition requires that a uniform bound on held-state size gives separate uniform L² bounds on the correction fractional power and rotating drift.

**Bounded held states have residual limits.** Proposition `HeldBoundedLimitStatement`: This proposition requires that bounded held solutions with convergent parameters and multipliers have a linear-state subsequential limit with lower semicontinuous energy, weak gradient convergence and a residual annihilating all solenoidal L² fields.

**Coordinate limits identify held states.** Proposition `HeldLimitIdentifyStatement`: This proposition requires that bounded held solutions with convergent parameters and multipliers have a linear-state subsequential limit whose gradient columns and second trace converge weakly and whose residual annihilates all solenoidal L² fields.

**Weak component limits close held states.** Proposition `HeldLimitClosureStatement`: This proposition requires that the specified simultaneous weak limits of the weighted velocity, derivative entries, power and drift of bounded held solutions form a limiting linear state whose residual annihilates all solenoidal L² fields.

**Second-order fields admit weak limits.** Proposition `SecondOrderWeakLimitStatement`: This proposition requires that under the stated uniform derivative bounds and weak L² convergence of weighted velocities and derivative entries, multiplying the limiting weighted velocity by radius gives a second-order field with the limiting derivatives.

**Weak fractional powers admit weak limits.** Proposition `WeakPowerLimitStatement`: This proposition requires that for 1<α<5/4, weak L² convergence of the inverse-radius velocity and of its weak fractional power preserves the weak-power relation after multiplication of the limiting velocity by radius.

**Weak drift limits stay in L².** Proposition `DriftWeakLimitStatement`: This proposition requires that under convergence of rotation rates and the stated simultaneous weak limits, the drift of the limiting second-order velocity is square integrable.

**The limiting residual annihilates tests.** Proposition `HeldResidualLimitStatement`: This proposition requires that under the boundedness and weak-convergence hypotheses for held solutions, the residual of the limiting linear state with the limiting multiplier annihilates every solenoidal L² field.

### Breakdown.FracCert.HeldStateLimitBWeak

Extracts simultaneous L² weak subsequences and proves lower semicontinuity of the weighted certificate energies.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldStateLimitBWeak.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.WeakFieldLimit`.

**Integral pairings equal L² pairings.** Proved result `pair_eq`: For f,g∈L², the integral ∫f·g is their Hilbert-space L² inner product.

**L² fields pair integrably.** Proved result `pair_integrable`: The scalar product f·g is integrable whenever f and g are square-integrable vector fields. Source: `Breakdown.FracCert.HeldStateLimitBWeak:24`.

**L² weak subsequences exist.** Proved result `exists_weak_subseq`: Under the stated hypotheses, bounded L² sequences have weak subsequences.

**Weighted energy is lower semicontinuous.** Proved result `weighted_lsc`: If fₙ converges weakly in L² to f₀ and w is a bounded nonnegative measurable weight, then for every ε>0, ∫w|f₀|²≤∫w|fₙ|²+ε for all sufficiently large n.

**A matrix rebuilt from its columns.** Definition `colOp`: This reconstructs a spatial linear map from its three vector columns using the spatial coordinate functionals.

**Rebuilt matrices recover their columns.** Proved result `colOp_apply`: Reconstructing a matrix from column fields cⱼ gives G(y)eⱼ=cⱼ(y).

**The rebuilt matrix is measurable.** Proved result `colOp_meas`: A matrix field assembled from three measurable vector-valued columns is measurable.

**Matrix fields have weak subsequences.** Proved result `exists_weak_operator_subseq`: Every sequence of measurable matrix fields with uniformly bounded squared Frobenius integrals has a strictly indexed subsequence whose three columns converge weakly in L² to those of one measurable matrix field.

**Column limits give matrix pairing limits.** Proved result `entryInner_tendsto`: Weak L² convergence of all three matrix columns implies convergence of the integrated Frobenius pairing against every square-integrable matrix test.

**Matrix energy is lower semicontinuous.** Proved result `weighted_entry_lsc`: If every column of Gₙ converges weakly in L² to that of G₀ and w is bounded, nonnegative and measurable, then ∫w|G₀|²≤∫w|Gₙ|²+ε eventually for every ε>0.

**Finite families share a weak subsequence.** Proved result `exists_weak_subseq_family`: A finite family of uniformly L²-bounded sequences admits one strictly indexed subsequence along which every member converges weakly in L² to a corresponding L² limit.

### Breakdown.FracCert.HeldUnique

Subtracts two held solutions and uses the a priori and product estimates to prove uniqueness in the small-energy region.

This belongs to the fractional certificate route: held solutions, multiplier cancellation and nontrivial profiles give an analogue of the a posteriori strategy in paper §7; its fractional conclusions are outside the paper's stated ordinary-dissipation argument.

Source: `lean/Breakdown/FracCert/HeldUnique.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldUniqueInternal`.

**Axial turns preserve differences.** Proved result `axialTurn_sub`: For vectors a,b∈ℝ³, J(a−b)=Ja−Jb. Source: `Breakdown.FracCert.HeldUnique:16`.

**Drift fields preserve differences.** Proved result `drift_sub`: For fixed α and a, the drift of the difference (u−u′,G−G′) is the difference of the two drifts. Source: `Breakdown.FracCert.HeldUnique:20`.

**The second trace preserves differences.** Proved result `secondTrace_sub`: The vector-valued trace is linear: tr(A−B)=tr A−tr B for bilinear forms A,B.

**The full linear field admits differences.** Proved result `full_sub`: At fixed α and p, subtracting two full linear states, including their actuator coefficients, subtracts their full linearized fields pointwise.

**Quadratic differences factor.** Proved result `quad_split`: Under the stated hypotheses, quadratic differences split symmetrically.

**Matrix pairings preserve differences.** Proved result `entryInner_sub`: For matrices A,B,C, (A−B):C=A:C−B:C.

**Matrix-entry pairings are integrable.** Proved result `entryInner_int`: For measurable matrix fields G and χ with finite squared Frobenius integrals, G:χ is integrable.

**The concrete L² norm is the Lp norm.** Proved result `l2Norm_eq`: For F∈L², √(∫|F|²) is its Hilbert-space norm. Source: `Breakdown.FracCert.HeldUnique:65`.

**Integral pairings equal L² pairings.** Proved result `l2Pair_eq`: For F,E∈L², ∫F·E is their L² inner product.

**The concrete L² norm is nonnegative.** Proved result `l2Norm_nonneg`: The quantity √(∫|F|²) is nonnegative for every vector field F. Source: `Breakdown.FracCert.HeldUnique:79`.

**The row maximum bounds all rows.** Proved result `rows_bound`: For a valid certificate and f∈L², the weighted row size of f is at most √T‖f‖₂, where T is the certificate row bound.

**The inverse bound is nonnegative.** Proved result `bound_nonneg`: With nonnegative scale, coercivity and residual inputs and 0≤θ<1, the certificate inverse-estimate expression B(x,y,0) is nonnegative.

**inverse bound respects a common scale.** Proved result `bound_scale`: With nonnegative scale and coercivity parameters and 0≤θ<1, bounds 0≤x≤N and 0≤y≤Ns imply B(x,y,0)≤NB(1,s,0) for the inverse-estimate expression.

**Test fields have finite L² energy.** Proved result `test_sq_int`: Every smooth compactly supported vector test φ has finite integral ∫|φ|².

**L² fields pair integrably with tests.** Proved result `l2_test_int`: For P∈L² and a smooth compactly supported vector test φ, P·φ is integrable.

**Fractional-power tests pair integrably.** Proved result `six_power_int`: For 1<α<3/2, v∈L⁶ and smooth compactly supported φ, the pairing v·(−Δ)^αφ is integrable.

**Source namespace:** `Breakdown.SteadyCert`.

**Weak fractional powers admit differences.** Proved result `weakPowerDifference`: Under the stated assumptions, this establishes that for 1<α<5/4, subtracting two second-order fields and their weak fractional powers preserves the weak fractional-power relation.

**Source namespace:** `Breakdown.SteadyCert.GradientDifferenceInternal`.

**Compact cutoffs give integrability.** Proved result `cut_int`: Multiplying a measurable scalar f that is square-integrable on every compact set by a continuous compactly supported cutoff c gives an integrable function cf.

**Each basis vector has unit norm.** Proved result `unit_norm`: Each coordinate basis vector eⱼ in ℝ³ has length one.

**Gradient components have local energy.** Proved result `comp_sq_int`: If Q is measurable and locally square-integrable, each coordinate Qⱼ has integrable square on every compact set.

**Test derivatives are continuous.** Proved result `test_deriv_cont`: For a smooth compactly supported scalar test φ, every coordinate derivative ∂ⱼφ is continuous.

**Test derivatives have compact support.** Proved result `test_deriv_supp`: For a smooth compactly supported scalar test φ, every coordinate derivative ∂ⱼφ has compact support.

**Gradient potentials can be measurable.** Proved result `potential_regular`: Every locally square-integrable weak gradient Q has a measurable locally square-integrable scalar potential q satisfying ∫∂ⱼφ q=−∫φQⱼ for all smooth compactly supported φ.

**Source namespace:** `Breakdown.SteadyCert`.

**Gradient fields admit differences.** Proved result `gradientDifference`: Under the stated assumptions, this establishes that the difference of two weak gradient fields is a weak gradient field.

**Small held solutions are unique.** Proved result `heldUnique`: Under the stated assumptions, this establishes that two held solutions at the same parameter have equal velocities almost everywhere and equal multipliers when the sum of their square-root energies times the row and nonlinear product constants is less than one.

### Breakdown.FracCert.HeldUniqueParts

States the product and subtraction properties needed when comparing two held solutions.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldUniqueParts.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert`.

**Symmetric convection products lie in L².** Proposition `ProductSquareStatement`: This proposition requires that the symmetric convection product of two second-order fields in the same symmetry class belongs to L².

**Gradient fields admit differences.** Proposition `GradientDifferenceStatement`: This proposition requires that the difference of two weak gradient fields is a weak gradient field.

**Weak fractional powers admit differences.** Proposition `WeakPowerDifferenceStatement`: This proposition requires that for 1<α<5/4, subtracting two second-order fields and their weak fractional powers preserves the weak fractional-power relation.

### Breakdown.FracCert.HeldWeakProfile

Turns a held solution with cancelled multipliers into a nonzero weak fractional profile by combining the approximate profile and its correction.

This belongs to the fractional certificate route: held solutions, multiplier cancellation and nontrivial profiles give an analogue of the a posteriori strategy in paper §7; its fractional conclusions are outside the paper's stated ordinary-dissipation argument.

Source: `lean/Breakdown/FracCert/HeldWeakProfile.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldWeakProfileInternal`.

**The held equation expands as a profile.** Proved result `residual_eq`: The held equation with pressure gradient Q expands into the drift and fractional power of Wₚ+u, the convection (∇Wₚ+G)(Wₚ+u), the actuator term with total coefficients λ(p)+κ, and Q.

**L² fields pair integrably.** Proved result `integrable_inner_of`: For square-integrable vector fields f and g, their pointwise inner product is integrable.

**Source namespace:** `Breakdown.SteadyCert`.

**Cancelled held solutions give profiles.** Proved result `heldWeakProfile_of`: Under the stated assumptions, this establishes that for a valid fractional certificate, a held solution within the certified radius whose corrected multiplier is zero yields a nontrivial weak rotating fractional profile.

**Weak-power tests give the profile bridge.** Proved result `heldWeakProfile_of_power`: Under the stated assumptions, this establishes that for a valid fractional certificate, a held solution within the certified radius whose corrected multiplier is zero yields a nontrivial weak rotating fractional profile.

**The held-to-profile bridge follows.** Proved result `heldWeakProfile`: Under the stated assumptions, this establishes that for a valid fractional certificate, a held solution within the certified radius whose corrected multiplier is zero yields a nontrivial weak rotating fractional profile.

### Breakdown.FracCert.HeldWeakProfileParts

Provides the weak integration identities and square-integrability properties used to turn held solutions into weak profiles.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/HeldWeakProfileParts.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.SteadyCert`.

**Profile data admit the weak embedding.** Proposition `ProfileEmbedDataStatement`: This proposition requires that a valid certificate profile is measurable and in L⁶, has a measurable square-integrable weak gradient and has vanishing divergence almost everywhere.

**Corrected convection products lie in L².** Proposition `HeldQuadraticL2Statement`: This proposition requires that for a valid fractional certificate, the full convection of the approximate profile plus any admissible second-order correction belongs to L².

**Nice fields are solenoidal L² fields.** Proposition `NiceSolenoidalStatement`: This proposition requires that every nice physical test field is a square-integrable solenoidal field.

**Drift transfers to nice test fields.** Proposition `DriftNicePairingStatement`: This proposition requires that for α>0, an L⁶ field with square-integrable weak gradient transfers its rotating drift to the drift adjoint in pairings with nice test fields, with the adjoint pairing integrable.

**Weak powers transfer to nice tests.** Proposition `WeakPowerNiceStatement`: This proposition requires that for 1<α<5/4, the weak fractional-power identity extends from compact tests to nice test fields and the resulting velocity-power pairing is integrable.

**Source namespace:** `Breakdown.SteadyCert.HeldWeakProfilePartsInternal`.

**Integration by parts for smooth fields.** Proved result `test_ibp`: Under the stated hypotheses, smooth fields satisfy integration by parts.

**Gradient pairings expand by coordinate.** Proved result `inner_gradient`: For a vector a and scalar ψ, a·∇ψ(y)=∑ᵢaᵢ∂ᵢψ(y).

**Derivatives commute with coordinates.** Proved result `coord_fderiv`: Under the stated hypotheses, differentiation commutes with coordinates.

**Weak gradients admit decaying tests.** Proved result `weak_component`: Under the stated hypotheses, weak gradients pair against decaying tests.

**Matrix entries control squared action.** Proved result `norm_apply_sq_le`: For a matrix A and vector w, |Aw|²≤3|w|²∑ᵢ|Aeᵢ|².

**A mixed product is bounded by cubes.** Proved result `weight_split`: For t,x≥0, t²x≤t³+x³.

**Decay gives integrability.** Proved result `decay_mul_integrable`: Under the stated hypotheses, decay turns power bounds into integrability.

**Weak vector identities extend to decay.** Proved result `weak_vector`: If v∈L⁶ has measurable square-integrable weak gradient G, the identity ∫v·∂ⱼΦ=−∫Geⱼ·Φ extends to smooth vector fields Φ for which both |Φ| and |DΦ| are bounded by B(1+|y|)⁻⁴.

**Decaying fields pair integrably.** Proved result `inner_decay_integrable`: If continuous X satisfies |X(y)|≤B(1+|y|)⁻⁴ and measurable f has ∫|f|ⁿ<∞ for an integer n≥1, then f·X is integrable.

**Integration by parts with linear weights.** Proved result `weighted_pair`: Under the stated hypotheses, linear weights admit integration by parts.

**Integrability survives addition.** Proved result `int_add`: For scalar functions f,g∈L¹(ℝ³), the pointwise sum f+g is integrable.

**Integrability survives scalar factors.** Proved result `int_cmul`: If a scalar function f is integrable, so is cf for every real constant c.

**Integrability survives subtraction.** Proved result `int_sub`: For scalar f,g∈L¹(ℝ³), the difference f−g is integrable.

**Finite sums remain integrable.** Proved result `int_fsum`: The sum of three integrable scalar functions on ℝ³ is integrable.

**Axial turns preserve sums.** Proved result `axialTurn_add`: For real vectors x,z, the axial generator satisfies J(x+z)=Jx+Jz. Source: `Breakdown.FracCert.HeldWeakProfileParts:421`.

**Axial turns preserve scaling.** Proved result `axialTurn_smul`: For a real scalar c and vector x, the axial generator satisfies J(cx)=cJx. Source: `Breakdown.FracCert.HeldWeakProfileParts:425`.

**The axial turn as a continuous map.** Definition `turnCLM`: This equips the infinitesimal axial turn with its continuous linear map structure.

**The spatial turn is (−x₂,x₁,0).** Proved result `turnCLM_apply`: The bundled continuous turn map sends (x₁,x₂,x₃) to (−x₂,x₁,0), agreeing with the axial generator.

**Axial turns do not increase norms.** Proved result `norm_axialTurn_le'`: For every z∈ℝ³, the axial generator satisfies |Jz|≤|z|.

**Axial turns are skew-adjoint.** Proved result `inner_axialTurn`: For x,z∈ℝ³, (Jx)·z=−x·Jz.

**A turn has zero diagonal entries.** Proved result `axialTurn_unit_self`: For each coordinate basis vector eⱼ, the jth coordinate of Jeⱼ is zero.

**Linear maps expand in a basis.** Proved result `expand_apply`: For every linear map L on ℝ³, Lw=∑ⱼwⱼL(eⱼ).

**Source namespace:** `Breakdown.SteadyCert`.

**Nice fields are solenoidal L² fields.** Proved result `niceSolenoidal`: Under the stated assumptions, this establishes that every nice physical test field is a square-integrable solenoidal field.

**Profile data admit the weak embedding.** Proved result `profileEmbedData`: Under the stated assumptions, this establishes that a valid certificate profile is measurable and in L⁶, has a measurable square-integrable weak gradient and has vanishing divergence almost everywhere.

**The corrected quadratic term lies in L².** Proved result `heldQuadraticL2_of`: Under the stated assumptions, this establishes that for a valid fractional certificate, the full convection of the approximate profile plus any admissible second-order correction belongs to L².

**Drift transfers to nice test fields.** Proved result `driftNicePairing`: Under the stated assumptions, this establishes that for α>0, an L⁶ field with square-integrable weak gradient transfers its rotating drift to the drift adjoint in pairings with nice test fields, with the adjoint pairing integrable.

**Weak powers transfer to nice tests.** Proved result `weakPowerNice`: Under the stated assumptions, this establishes that for 1<α<5/4, the weak fractional-power identity extends from compact tests to nice test fields and the resulting velocity-power pairing is integrable.

### Breakdown.FracCert.HeldZero

Uses the continuous multiplier map and the certificate enclosure to choose a parameter that cancels all held forces.

This belongs to the fractional certificate route: held solutions, multiplier cancellation and nontrivial profiles give an analogue of the a posteriori strategy in paper §7; its fractional conclusions are outside the paper's stated ordinary-dissipation argument.

Source: `lean/Breakdown/FracCert/HeldZero.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.SteadyCert.HeldZeroInternal`.

**Near-isometric matrices are invertible.** Proved result `det_isUnit_of_near`: If a real square matrix U satisfies ||Uz|²−|z|²|≤δ|z|² for every z and δ<1, then det U≠0 and U is invertible.

**Source namespace:** `Breakdown.SteadyCert`.

**A parameter cancels all held multipliers.** Proved result `heldZero`: Under the stated assumptions, this establishes that a valid fractional certificate admits a parameter in its box and a held solution within its certified radius whose corrected multiplier vector vanishes.

### Breakdown.FracCert.InverseSquare

Proves the inverse-square Hardy estimate by regularized integration by parts, cutoff approximation and mollification of weak gradients.

This is functional-analytic support for the fractional certificate route, including compactness, weak limits, symmetry or gradient decompositions as appropriate to the module; no exact correspondence with a numbered paper result is asserted.

Source: `lean/Breakdown/FracCert/InverseSquare.lean`. Imported by the ordinary and fractional cell endpoint modules.

**Source namespace:** `Breakdown.FracInternal`.

**The regularized weight has a derivative.** Proved result `weight_fderiv_apply`: For δ>0, ∂ⱼ(yⱼ/(|y|²+δ))=(|y|²+δ)⁻¹−2yⱼ²(|y|²+δ)⁻².

**The squared norm has its derivative.** Proved result `normSq_fderiv_apply`: Under the stated hypotheses, squared norms have the expected derivative.

**Positive regularization gives smoothness.** Proved result `contDiff_weight`: For δ>0, each scalar weight y↦yⱼ/(|y|²+δ) is smooth everywhere on ℝ³.

**Coordinate squares sum to norm squared.** Proved result `sum_sq_coord`: The coordinate identity ∑ⱼyⱼ²=|y|² holds for every y∈ℝ³.

**Compact continuous products are L¹.** Proved result `integrable_mul_of_support`: Under the stated hypotheses, compact continuous products are integrable.

**Young bounds weighted derivatives.** Proved result `neg_partial_le`: Under the stated hypotheses, young bounds the weighted derivative term.

**Weight divergence controls radial weight.** Proved result `weight_sum_ge`: Under the stated hypotheses, weight divergence controls inverse radius.

**The squared weight has a radial bound.** Proved result `sq_weight_le`: For δ>0, |y|²/(|y|²+δ)²≤1/(|y|²+δ) for every y.

**The regularized Hardy bound holds.** Proved result `regularizedInverseSquare_le`: For smooth compactly supported u and δ>0, the regularized Hardy estimate is ∫|u(y)|²/(|y|²+δ)dy≤4∫|∇u|²dy.

**Cutoff derivatives lie in an annulus.** Proved result `fderiv_radialCutoff_ne`: For R>0, a nonzero derivative of the radial cutoff χᵣ can occur only in the closed annulus R≤|y|≤2R.

**Sixth powers control squared values.** Proved result `sq_le_six_add`: For real a and M>0, a²≤a⁶/M²+M.

**The cutoff energy tail tends to zero.** Proved result `cutoffTail`: For a continuous L⁶ field w, the cutoff error ∫|∇χᵣ(y)|²|w(y)|²dy tends to zero as R→∞.

**Weighted squares obey a two-term bound.** Proved result `sq_add_le_weighted`: For θ>0 and real x,y, (x+y)²≤(1+θ)x²+(1+θ⁻¹)y².

**Cutoff derivatives have an energy bound.** Proved result `entrySq_cutoff_le`: Under the stated hypotheses, cutoff derivatives satisfy an energy bound.

**Large cutoffs preserve derivative energy.** Proved result `cutoffEnergy`: If smooth w belongs to L⁶ and has finite gradient energy, then for every η>0, all sufficiently large radial cutoffs satisfy ∫|∇(χᵣw)|²≤∫|∇w|²+η.

**Jensen bounds mollified norm powers.** Proved result `normPow_convolution_le`: For a normalized nonnegative smooth bump ρ and integer k≥1, integrability of |f|ᵏ gives |ρ*f(y)|ᵏ≤(ρ*|f|ᵏ)(y) at every y.

**Mollification preserves weak derivatives.** Proved result `mollify_fderiv_apply`: If v∈L⁶ has weak gradient G, convolution with a normalized smooth bump satisfies ∂ⱼ(ρ*v)=ρ*(Geⱼ) pointwise. Source: `Breakdown.FracCert.InverseSquare:467`.

**Smooth approximation controls energy.** Proved result `smoothApprox`: Under the stated hypotheses, smooth fields approximate without energy gain.

**Radial cutoffs are test functions.** Proved result `testScalar_cutoff`: For every nonnegative integer n, the radial cutoff of radius n+1 is a smooth compactly supported scalar test.

**A test detects nonmeasurability.** Proved result `exists_test_not_measurable`: If a vector field g has no measurable representative up to a null set, some smooth compactly supported scalar cutoff φ leaves φg nonmeasurable up to a null set.

**Nonmeasurable columns force zero tests.** Proved result `partial_zero_of_not_measurable`: If locally integrable v satisfies the weak-gradient pairing with G and a column Geⱼ has no measurable representative, then ∫∂ⱼφ v=0 for every smooth compactly supported φ. This assertion uses the convention that a nonintegrable vector integral has value zero.

**A measurable weak gradient can be chosen.** Proved result `measurableGradient_exists`: A weak-gradient field with integrable squared entries admits a measurable weak-gradient representative whose entrywise energy is no larger, under the stated velocity hypotheses.

**Compact smooth energy approximation.** Proved result `smoothCompactApprox`: Under the stated hypotheses, compact smooth fields approximate the energy.

**Source namespace:** `Breakdown.SteadyCert`.

**Matrix-entry energy is nonnegative.** Proved result `entrySq_nonneg'`: For every matrix A, its squared Frobenius norm ∑ᵢ|Aeᵢ|² is nonnegative. Source: `Breakdown.FracCert.InverseSquare:682`.

**Approximation gives the Hardy bound.** Proved result `inverseSquare_of_approx`: If smooth compactly supported uₙ converge almost everywhere to measurable v and ∫|∇uₙ|²≤∫|G|²+1/(n+1), then |v|²/|y|² is integrable and ∫|v|²/|y|²≤4∫|G|².

**The inverse-square bound holds.** Proved result `inverseSquareBound`: Under the stated assumptions, this establishes that a measurable L⁶ velocity with square-integrable weak gradient has integrable ‖v(y)‖²/‖y‖² and its integral is at most four times the gradient energy.

### Breakdown.FracCert.KernelDecay

Builds derivative decay estimates for the projected fractional heat-divergence kernel by annular Fourier localization and dyadic summation.

This develops regularity or spatial decay for the fractional extension, supporting passage from a weak fractional profile to a classical decaying field; it is not an identification with a numbered ordinary-dissipation theorem in the paper.

Source: `lean/Breakdown/FracCert/KernelDecay.lean`. Imported by the fractional cell endpoint module.

**Source namespace:** `Breakdown.FracCert.KernelDecayInternal`.

**Exponential decay dominates polynomials.** Proved result `poly_exp_bound`: For any nonnegative integer M and c₀>0, (1+s)ᴹe^(−c₀s) is bounded by one finite nonnegative constant for all s≥0.

**Compact sets bound derivatives uniformly.** Proved result `uniform_bound_on`: If f is smooth on an open set U and K is a compact subset of U, its derivatives through any prescribed finite order have one uniform bound on K.

**Exponential derivatives have exact norms.** Proved result `norm_iteratedFDeriv_exp_mul`: The norm of the ith derivative of u↦e^(−su) is exactly |s|ⁱe^(−su), for every real s,u and nonnegative integer i.

**Localized heat symbols are bounded.** Proved result `piece_symbol_bound`: For α>0 and a smooth dyadic annular cutoff θ, the localized projected heat-divergence symbols θ(ξ)kₛ(ξ) are smooth, with every fixed finite collection of derivative orders bounded uniformly over s>0 and all ξ.

**The heat symbol obeys its scaling law.** Proved result `symbol_smul`: For α,t>0, the projected heat-divergence multiplier satisfies kₜ(t^(−1/(2α))η)=t^(−1/(2α))k₁(η), componentwise.

**The heat kernel obeys its scaling law.** Proved result `kernel_smul`: For α,t>0, the projected heat-divergence kernel satisfies Kₜ(x)=t^(−2/α)K₁(t^(−1/(2α))x), componentwise.

**Scaling combines the decay factors.** Proved result `scale_factor`: For t>0, r≥0 and integer n≥0, t^(−(4+n)/(2α))(1+t^(−1/(2α))r)^(−4−n)=(t^(1/(2α))+r)^(−4−n).

**Unit-time decay gives all-time decay.** Proved result `decay_of_unit`: For α>0, smoothness and bounds |DⁿK₁(x)|≤Cₙ(1+|x|)^(−4−n) imply smoothness for every t>0 and |DⁿKₜ(x)|≤Cₙ(t^(1/(2α))+|x|)^(−4−n).

**The symbol rescales its heat time.** Proved result `symbol_smul_gen`: For c>0, the projected multiplier obeys kₜ(cη)=c k_{tc^(2α)}(η), for every real α and t.

**Inverse transforms obey dilation.** Proved result `invTransform_smul_gen`: For c>0, inverse Fourier transformation obeys ℱ⁻¹f(x)=c³ℱ⁻¹(f(c·))(cx).

**Dilation controls derivative norms.** Proved result `norm_iteratedFDeriv_scale_le`: For smooth scalar k, c>0 and real a, the nth derivative of x↦ak(cx) has norm at most |a|cⁿ|Dⁿk(cx)|.

**The localized heat-divergence symbol.** Definition `pieceSymbol`: This defines one localized projected-divergence symbol by multiplying its Fourier multiplier by the radial cutoff.

**Dyadic kernel pieces rescale.** Proved result `piece_kernel_eq`: The time-one kernel piece localized by θ(2^(−ℓ)ξ) equals 2^(4ℓ) times the inverse transform of the unit-annulus symbol at heat time 2^(2αℓ), evaluated at 2^ℓx.

**Radial heat weights are integrable.** Proved result `radial_integrable`: For α,t>0 and every nonnegative integer m, the radial heat weight |ξ|ᵐe^(−t(2π|ξ|)^(2α)) is integrable on ℝ³.

**The heat symbol has a radial norm bound.** Proved result `symbol_norm_le`: Every projected heat-divergence multiplier component satisfies |kₜ(ξ)|≤4π|ξ|e^(−t(2π|ξ|)^(2α)).

**The heat symbol is measurable.** Proved result `symbol_measurable`: For every α,t and component indices, the projected heat-divergence multiplier is measurable in ξ.

**All heat-symbol moments are integrable.** Proved result `symbol_moment`: For α,t>0, every nonnegative integer moment ∫|ξ|ⁿ|kₜ(ξ)|dξ of each projected multiplier component is finite.

**The heat-divergence kernel is smooth.** Proved result `kernel_contDiff`: For α,t>0, every component of the projected heat-divergence kernel is smooth of all orders.

**Partial cutoff sums are at most one.** Proved result `cutoff_partial_le`: For a nonnegative dyadic annular partition of unity θ, every finite subsum ∑ℓ∈S θ(2^(−ℓ)v) is at most one, including at v=0.

**Cutoffs reconstruct the integral.** Proved result `hasSum_integral_cutoff`: Under the stated hypotheses, cutoff integrals reconstruct the integral.

**Fourier differentiation respects weights.** Proved result `powSMulRight_smul`: Under the stated hypotheses, Fourier derivative factors respect weights.

**The heat symbol is zero at the origin.** Proved result `symbol_zero`: Every component of the projected heat-divergence multiplier is zero at ξ=0 for all α and t.

**Kernel derivatives sum by dyadic pieces.** Proved result `kernel_hasSum`: For α>0 and a smooth dyadic annular partition of unity, the sum over all integer scales of the nth derivatives of the localized inverse transforms equals DⁿK₁(x) for every n and x.

**unit-time kernel has derivative decay.** Proved result `unit_bound`: For α>0, a smooth dyadic annular cutoff and uniformly bounded derivatives of the localized heat symbols, the localized Fourier-kernel estimate and dyadic summation bound imply |DⁿK₁(x)|≤Cₙ(1+|x|)^(−4−n) for every n and x.

**Source namespace:** `Breakdown.FracCert`.

**The kernel decay interface follows.** Proved result `kernelDecay_of`: Under the stated assumptions, this establishes that for α>0, every positive-time projected heat-divergence kernel component is smooth and its nth derivative is bounded by C(t^(1/(2α))+‖x‖)^(−4−n).
<!-- /passage:front -->

