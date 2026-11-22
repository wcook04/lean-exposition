
<!-- passage:front -->
# Library guide 12: Breakdown/CertCell

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) **12** [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) [28](../navier-stokes-library-28/paper.md) [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.CertCell.ShapeJunction` to `Breakdown.CertCell.VelocitySixthIntegral` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.

### Breakdown.CertCell.ShapeJunction

This file converts established shape facts and scalar-value symmetries into the admissibility and reflection clauses consumed by cell instances. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Admissible shapes from layer data.** Proved result. The layer's shape and scalar-value assumptions imply the shape admissibility requirements at every certified parameter. (`shapeAdmissible_of_layer`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJunction.lean#L15)).

**Shape reflection from value symmetry.** Proved result. Reflection symmetry of the supplied scalar values gives the shape reflection requirements at every certified parameter. (`shapeFlip_of_values`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeJunction.lean#L28)).

### Breakdown.CertCell.ShapeKeyConj

This file proves that changing a harmonic key to its negative conjugates the corresponding complex field, including the spline amplitudes and radial phase. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Differentiation commutes with conjugacy.** Proved result. For a complex-valued function of a real variable, (conj f)′(x) = conj(f′(x)); the identity also holds when both derivatives are assigned zero at nondifferentiable points. (`conjKey_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L16)).

**Radial scaling commutes with conjugacy.** Proved result. Applying the compactified radial differential operator t(1−t)∂ₜ to conj f gives the complex conjugate of that operator applied to f. (`conjKey_radialScale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L22)).

**Height derivatives respect conjugacy.** Proved result. Height differentiation respects conjugacy. (`conjKey_heightDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L27)).

**Conjugacy reverses the radial phase.** Proved result. Complex conjugation sends the radial operator t(1−t)∂ₜ + ijβ(t) to t(1−t)∂ₜ − ijβ(t), where β is the real radial phase slope. (`conjKey_shiftedScale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L31)).

**Polynomial weights are real.** Proved result. For nonnegative integers a and b and real t, the weight tᵃ(1−t)ᵇ is unchanged by complex conjugation. (`conjKey_weightPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L40)).

**Negating labels reverses time frequency.** Proved result. Negating both integer entries of a mode label changes its temporal frequency k to −k. (`conjKey_labelTime`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L44)).

**Angular frequency changes sign.** Proved result. Negating labels reverses angular frequency. (`conjKey_labelAzimuth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L49)).

**Negating keys conjugates their phase.** Proved result. Negating a mode's frequency and phase indices changes its oscillatory phase factor into its complex conjugate at every time and point. (`conjKey_keyPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L54)).

**Conjugated splines conjugate values.** Proved result. Conjugating every polynomial coefficient of a spline conjugates its evaluated value at every pair of real coordinates. (`conjKey_evalHalf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L64)).

**Negating keys conjugates components.** Proved result. If the nonzero angular amplitudes are conjugated with equal low-order and high-order exponents, negating the mode indices conjugates all three reduced components. For a zero angular label, the same conclusion follows by conjugating the stream and swirl amplitudes and the axis coefficient, with equal high-order exponents. (`conjKey_reducedComps`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L68)).

**Key fields obey complex conjugation.** Proved result. For admissible time-dependent shape data, the field associated with the negated mode and phase indices is the componentwise complex conjugate of the original field, at every time and point. (`keyConjugate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyConj.lean#L145)).

### Breakdown.CertCell.ShapeKeyDivergence

This file makes the divergence cancellation in the two component formulas explicit and reduces divergence-free key fields to the spherical-frame formula and regularity contracts. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Type-one divergence terms cancel.** Proved result. For admissible shape parameters and a nonzero angular mode, the reduced components satisfy Dⱼuᵣ + 2uᵣ − ∂ₓ((1−x²)uθ) + inuφ = 0, with Dⱼ the radial operator including phase and n the angular frequency. (`typeOne_reduced_cancel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L18)).

**Mixed partial derivatives agree.** Proved result. If Φ(t,x) is C² near a point, ∂ₓ∂ₜΦ = ∂ₜ∂ₓΦ there, and the x-slice is differentiable at that point. (`mixed_partials`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L34)).

**Stream derivatives cancel.** Proved result. For a C² stream function Φ and any coefficient c(t), applying t(1−t)∂ₜ+c(t)+2 to −∂ₓΦ cancels the x-derivative of −(t(1−t)∂ₜΦ+c(t)Φ+2Φ). (`partial_cancel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L75)).

**Type-two divergence terms cancel.** Proved result. For a zero angular mode whose weighted stream function t(1−t)ᴺ(1−x²)Ψ is C² at (t,x), its reduced components satisfy the spherical divergence cancellation Dⱼuᵣ + 2uᵣ − ∂ₓ((1−x²)uθ) = 0. (`typeTwo_reduced_cancel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L91)).

**Zero divergence extends from a dense set.** Proved result. For a C¹ complex vector field, divergence vanishing wherever the second coordinate is nonzero implies divergence vanishing everywhere. (`divergence_of_dense`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L122)).

**Complex embedding preserves regularity.** Proved result. Embedding a real scalar function in the complex numbers preserves its specified order of continuous differentiability. (`ofReal_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L141)).

**C² gives differentiable derivatives.** Proved result. C² gives differentiable first derivatives. (`c2_deriv_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L144)).

**Polynomial weights are C².** Proved result. For any nonnegative integers a and b, the polynomial weight tᵃ(1−t)ᵇ has two continuous derivatives on R. (`weightPoly_c2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L148)).

**The polar factor is C².** Proved result. The factor x ↦ 1−x², viewed as a complex-valued function of a real variable, is C² on R. (`polarFactor_c2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L151)).

**The axis factor is C².** Proved result. The factor x ↦ (1−x²)², viewed as a complex-valued function of a real variable, is C² on R. (`axisFactor_c2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L154)).

**Phase slope is differentiable below 1.** Proved result. For admissible radial phase data, the compactified radial phase slope is differentiable at every t < 1. (`phaseSlope_differentiableAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L157)).

**Joined splines are differentiable.** Proved result. Assuming the joined-spline regularity result, matching first derivatives across all joins in both coordinates makes the evaluated spline differentiable on R². (`spline_differentiable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L175)).

**The radial spline derivative.** Proved result. For a spline joined to at least first order in both variables, its radial derivative is the evaluation of the radial derivative spline. (`spline_hasDerivAt_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L179)).

**The height spline derivative.** Proved result. For a spline joined to at least first order in both variables, its height derivative is the evaluation of the height derivative spline. (`spline_hasDerivAt_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L190)).

**Lift differentiability to the first axis.** Proved result. A function differentiable at t remains differentiable at every pair (t,x) when lifted to depend only on the first coordinate. (`fst_differentiableAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L202)).

**Lift along the second coordinate.** Proved result. A function differentiable at x remains differentiable at every pair (t,x) when lifted to depend only on the second coordinate. (`snd_differentiableAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L206)).

**Differentiable partials of C² functions.** Proved result. C² partial derivatives are differentiable. (`partials_differentiableAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L210)).

**The stream value is C² below 1.** Proved result. Assuming joined-spline regularity, an admissible origin profile plus a stream spline joined through order two in both coordinates gives a C² stream amplitude at every t < 1. (`streamValue_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L235)).

**The weighted stream is C² below one.** Proved result. Below the chart edge, a valid C² stream spline gives a C² product with the radial weight and polar factor. (`typeTwo_product_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L249)).

**Type-two components are differentiable.** Proved result. Assuming joined-spline regularity and admissible shape parameters, a zero angular mode has differentiable reduced components for t < 1 when its stream spline is joined through order two and its swirl spline through order one in both coordinates. (`typeTwo_components_differentiableAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L256)).

**Type-one components are differentiable.** Proved result. Assuming joined-spline regularity and admissible shape parameters, a nonzero angular mode has differentiable reduced components for t < 1 when its radial spline is joined through orders (2,1) and its polar spline through orders (1,2). (`typeOne_components_differentiableAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L291)).

**Divergence in spherical coordinates.** Proposition definition. This proposition requires the spherical-frame divergence to be the phase divided by radius times the radial scaling term, twice the radial amplitude, the negative weighted height derivative, and the angular-frequency term where the second spatial coordinate is nonzero. (`FramedDivergenceFormula`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L359)).

**The key fields are divergence free.** Proved result. The spherical divergence identity, joined-spline regularity and regularity of the two mode constructions together imply that every field from admissible shape data has zero divergence at every point. (`keyDivergenceFree_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyDivergence.lean#L372)).

### Breakdown.CertCell.ShapeKeyFlip

This file follows reflection through coordinates, phases, spline parity and reduced components until it gives the vector-field reflection law. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Reflection changes two coordinate signs.** Proved result. The spatial symmetry acts by (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃), fixing the first Cartesian component and negating the other two. (`flipPoint_coords`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L16)).

**Reflection preserves the norm.** Proved result. The half-turn (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃) preserves the Euclidean distance from the origin. (`norm_of_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L19)).

**Reflection reverses normalized height.** Proved result. Under the half-turn (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃), the normalized height y₃/|y| changes sign. (`heightRatio_of_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L24)).

**Reflection preserves compactified radius.** Proved result. The compactified radial coordinate is unchanged by the half-turn (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃). (`chartCoord_of_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L28)).

**Reflected keys preserve phase.** Proved result. Reflecting the mode label and evaluating at (y₁,−y₂,−y₃) preserves the original oscillatory phase factor at the same time. (`keyPhase_of_flipKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L32)).

**The polar factor is even.** Proved result. The factor 1−x² has the same value at x and −x for every real x. (`polarFactor_of_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L59)).

**The axis factor is even.** Proved result. The factor (1−x²)² has the same value at x and −x for every real x. (`axisFactor_of_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L63)).

**Radial differentiation respects flip.** Proved result. Radial differentiation respects reflection. (`shiftedScale_of_reflected`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L67)).

**Negated reflection keeps height slope.** Proved result. Negated reflection preserves height slope. (`heightDeriv_of_reflected_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L70)).

**Odd height profiles have even slopes.** Proved result. If f(t,−x) = −f(t,x), then ∂ₓf(t,−x) = ∂ₓf(t,x) for every t and x, with derivatives assigned zero where they do not exist. (`heightDeriv_of_odd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L75)).

**Radial scaling preserves oddness.** Proved result. If an amplitude f is odd in x, applying the radial differential operator including its phase term preserves that oddness. (`shiftedScale_of_odd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L83)).

**Type-one reduced components.** Definition. The type-one reduced vector retains its radial and polar amplitudes and uses their divergence-canceling combination divided by angular frequency for the azimuthal component. (`compsOne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L93)).

**Type-two reduced components.** Definition. The type-two reduced vector uses weighted stream derivatives for its radial and polar components and the weighted swirl value for its azimuthal component. (`compsTwo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L97)).

**The type-one component expansion.** Proved result. A key with nonzero first label has type-one components built from the weighted radial and polar splines. (`reducedComps_of_typeOne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L101)).

**The type-two component expansion.** Proved result. A key with zero first label has type-two components built from the stream function, its radial weight, and the swirl spline. (`reducedComps_of_typeTwo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L109)).

**Type-one reflection changes two signs.** Proved result. For a nonzero angular mode, reversing the angular frequency and reflecting its radial amplitude evenly and polar amplitude oddly leaves the reduced radial component unchanged and negates the other two components at the reflected point. (`compsOne_of_reflected`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L116)).

**Odd type-two data give reflected signs.** Proved result. If both the stream and swirl amplitudes are odd in normalized height x, the zero angular mode's radial component is even in x and its other two reduced components are odd. (`compsTwo_of_odd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L134)).

**Component signs give reflected vectors.** Proved result. Equality of the reflected phases, together with signs (+,−,−) for the three reduced components, gives F′(y₁,−y₂,−y₃) = (F₁(y),−F₂(y),−F₃(y)). (`keyVector_of_flipped_comps`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L157)).

**Type-two keys are fixed by reflection.** Proved result. A mode with zero angular label is unchanged by the label reflection used for the half-turn symmetry. (`flipKey_of_typeTwo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L175)).

**Equal spline values on a full mesh.** Proved result. Agreeing splines on a full mesh have equal evaluated values at every coordinate pair. (`evalHalf_of_agreeing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L181)).

**Reflected agreement gives parity values.** Proved result. If T agrees with the even or odd reflected spline of S, T has a full mesh and S has the required joins, then T(t,x) = εS(t,−x), with ε = 1 for even reflection and ε = −1 for odd reflection. (`evalHalf_of_reflect_agree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L188)).

**Key fields satisfy reflection symmetry.** Proved result. For admissible shape data, reflecting the mode label and the spatial point produces the half-turn of the original vector field: F′(Ry) = RF(y). (`keyFlip_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyFlip.lean#L196)).

### Breakdown.CertCell.ShapeKeyRotation

This file derives the angular Fourier phase acquired under axial rotation and checks the axis case separately. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Rotation gives the first coordinate.** Proved result. Rotation through φ about the third coordinate axis sends the first Cartesian component to cos(φ)y₁−sin(φ)y₂. (`rot_apply_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L17)).

**Rotation gives the second coordinate.** Proved result. Rotation through φ about the third coordinate axis sends the second Cartesian component to sin(φ)y₁+cos(φ)y₂. (`rot_apply_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L21)).

**Rotation fixes the third coordinate.** Proved result. Rotation through any angle about the third coordinate axis leaves y₃ unchanged. (`rot_apply_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L25)).

**Rotation preserves the norm.** Proved result. For every angle φ and vector y, axial rotation satisfies |Rφy| = |y|. (`rot_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L28)).

**Rotation preserves normalized height.** Proved result. Axial rotation leaves the normalized height y₃/|y| unchanged. (`rot_heightRatio`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L34)).

**Rotation preserves compactified radius.** Proved result. Axial rotation leaves the compactified radial coordinate unchanged for every choice of chart parameters. (`rot_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L37)).

**Axial points are fixed by rotation.** Proved result. If y₁ = y₂ = 0, every rotation about the third coordinate axis fixes y. (`rot_of_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L41)).

**Plane rotation is complex multiplication.** Proved result. Identifying the horizontal plane with C, axial rotation satisfies (Rφy)₁+i(Rφy)₂ = eⁱφ(y₁+iy₂). (`rot_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L48)).

**Rotated arguments give rotated phases.** Proved result. For z ≠ 0, the unit phase of eⁱφz equals eⁱφ times the unit phase of z, independently of the branch chosen for the argument. (`exp_arg_rotate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L55)).

**Integer angular phases split.** Proved result. For real U,V,θ and integer a, exp(i(U+aθ+V)) = exp(i(U+V))(exp(iθ))ᵃ. (`phase_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L67)).

**Rotating keys adds their angular phase.** Proved result. Away from the rotation axis, rotating a point through φ multiplies a mode's phase by eⁱⁿφ, where n is its integer angular frequency. (`rot_keyPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L75)).

**Third type-one axis component vanishes.** Proved result. On the rotation axis, a nonzero angular mode whose low-order vanishing exponent is at least one has zero axial contribution from its radial and polar components. (`axis_third_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L92)).

**Positive order gives key rotation.** Proved result. If each nonzero angular mode has low-order vanishing exponent at least one, its field satisfies F(Rφy) = eⁱⁿφRφF(y), including points on the axis. (`keyRotation_of_lowOrder_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L113)).

**Key fields satisfy rotation covariance.** Proved result. Every mode in admissible shape data transforms under axial rotation by F(Rφy) = eⁱⁿφRφF(y), where n is its angular frequency. (`keyRotation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyRotation.lean#L144)).

### Breakdown.CertCell.ShapeKeyTime

This file identifies the scalar Fourier factor produced by time translation of a key field. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Time translation adds a Fourier phase.** Proved result. Translating normalized time by τ multiplies the phase of temporal frequency k by exp(2πikτ). (`keyPhase_add_time`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyTime.lean#L11)).

**Key fields obey the time-shift law.** Proved result. For every mode amplitude, its vector field satisfies F(σ+τ,y) = exp(2πikτ)F(σ,y), with k its integer temporal frequency. (`keyTimeShift_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKeyTime.lean#L20)).

### Breakdown.CertCell.ShapeKnotHessian

This file permits a Hessian representative to be set to zero on spline knots while preserving its almost-everywhere value, weak derivative meaning and symmetries. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Reflection closure of a knot set.** Proposition definition. A planar knot set is reflection closed when membership is unchanged by negating its height coordinate. (`IsMirrorClosed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L17)).

**Rotations preserve the meridian point.** Proved result. Axial rotation preserves the meridian coordinates (√(y₁²+y₂²),y₃). (`planeOf_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L19)).

**Reflection reverses meridian height.** Proved result. The half-turn (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃) sends meridian coordinates (r,z) to (r,−z). (`planeOf_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L27)).

**Rotation fixes the origin.** Proved result. Every axial rotation sends the zero vector to the zero vector. (`axialRot_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L33)).

**Reflection fixes the origin.** Proved result. The half-turn (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃) sends the origin to itself. (`flipPoint_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L36)).

**Knot-zeroing commutes with mode Hessians.** Proved result. Setting a Hessian field to zero over a meridian set N commutes with temporal and angular mode projection: the projected Hessian is zero over N and agrees with the original projection elsewhere. (`modeHess_zeroOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L39)).

**Knot-zeroing preserves reflection.** Proved result. If a meridian set is closed under z ↦ −z, setting the model Hessian to zero above that set preserves the half-turn symmetry of the velocity and Hessian. (`flipModel_zeroOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L50)).

**Knot-zeroing keeps harmonic expansion.** Proved result. Knot-zeroing preserves harmonic expansion. (`harmonicExpansion_zeroOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L63)).

**Almost every point avoids null knots.** Proved result. Almost every spatial point avoids the lifted planar knot set when that set has zero volume. (`ae_not_knot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L76)).

**Knot-zeroing preserves values a.e..** Proved result. Setting the Hessian to zero on a null knot set leaves it unchanged almost everywhere. (`zeroOn_ae_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L80)).

**Knot-zeroing preserves weak Hessians.** Proved result. Setting the Hessian to zero on a null knot set preserves the weak second-derivative condition. (`weakHessianState_zeroOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotHessian.lean#L86)).

### Breakdown.CertCell.ShapeKnots

This file names the planar and spatial knot-nullity obligations and proves that the mirrored knot set is closed under reflection. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Nullity of planar shape knots.** Proposition definition. This proposition requires the planar knot set of valid shape parameters to have zero volume. (`ShapeKnotsNull`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnots.lean#L17)).

**Mirrored knots are reflection closed.** Proved result. The union of all shape knots with their height reflections is closed under (r,z) ↦ (r,−z). (`mirrorKnots_closed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnots.lean#L20)).

**Nullity of spatial shape knots.** Proposition definition. This proposition requires the spatial lift of the mirrored planar knot set to have zero volume for valid shape parameters. (`ShapeKnotsNullSpace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnots.lean#L30)).

### Breakdown.CertCell.ShapeKnotsNull

This file covers the spline seams by finitely many coordinate planes, spheres and cones, then proves that the resulting spatial exceptional set has zero volume. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**The horizontal coordinate plane.** Definition. The horizontal plane is the set of points with third coordinate zero. (`flat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L13)).

**A sphere described by a quadratic.** Definition. The sphere equation sets the sum of three squared coordinates equal to the squared radius parameter. (`sph`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L15)).

**A cone described by a quadratic.** Definition. The cone equation sets squared height equal to b squared times total squared radius. (`cone`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L17)).

**The norm squared is the coordinate sum.** Proved result. For y ∈ R³, the squared Euclidean norm is |y|² = y₁²+y₂²+y₃². (`norm_sq_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L19)).

**Coordinate planes have zero volume.** Proved result. Each plane {y ∈ R³ : yⱼ = 0} has three-dimensional Lebesgue measure zero. (`coord_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L23)).

**The horizontal plane has zero volume.** Proved result. The horizontal plane {y₃ = 0} has three-dimensional Lebesgue measure zero. (`flat_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L37)).

**Spheres have zero volume.** Proved result. For every real r, the set {y ∈ R³ : |y|² = r²} has three-dimensional Lebesgue measure zero. (`sph_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L39)).

**A graph parameterizing a cone.** Definition. The cone graph keeps the horizontal coordinates and makes height equal to c times their Euclidean radius. (`lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L46)).

**Cone graph is differentiable off-axis.** Proved result. For every slope c, lifting a point of the horizontal plane to the cone z = c√(y₁²+y₂²) is differentiable away from the axis. (`lift_differentiableOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L50)).

**Cone height from planar radius.** Proved result. The cone graph keeps the first two coordinates and sets the third to c times their Euclidean radius. (`lift_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L62)).

**Cones have zero volume.** Proved result. For every real b, the double cone defined by y₃² = b²|y|² has three-dimensional Lebesgue measure zero. (`cone_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L66)).

**Spline seams lifted to spheres and cones.** Definition. The lifted spline seams are spheres at radial breakpoints together with cones at height breakpoints. (`splineSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L117)).

**Lifted spline seams have zero volume.** Proved result. The spatial surfaces obtained by lifting all radial and height breakpoints of a spline have three-dimensional Lebesgue measure zero. (`splineSet_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L120)).

**The union of a key's spline seams.** Definition. A key's seam set is the union of the radial, polar, stream, and swirl spline seams. (`keySet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L124)).

**A key's seam set has zero volume.** Proved result. The union of the lifted spline seams belonging to one mode amplitude has three-dimensional Lebesgue measure zero. (`keySet_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L127)).

**The set covering all spatial knots.** Definition. The spatial knot cover combines two coordinate planes, the origin-profile edge sphere, and the seam sets of all supplied keys. (`bigSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L131)).

**The covering knot set has zero volume.** Proved result. The finite union covering all lifted spline seams of the time-dependent shape data has three-dimensional Lebesgue measure zero. (`bigSet_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L134)).

**Meridian and spatial radii agree.** Proved result. If q₁ = √(y₁²+y₂²) and q₂² = y₃², then the squared radius q₁²+q₂² equals |y|². (`planeNorm_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L138)).

**Shape knots lie in the covering set.** Proved result. If a meridian point has the same horizontal radius and squared height as y and lies on a shape knot, then y belongs to the spatial set covering all lifted knots. (`mem_bigSet`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L142)).

**Spatial shape knots have zero volume.** Proved result. For admissible chart parameters, the spatial points whose meridian coordinates lie on a shape knot or its height reflection form a set of Lebesgue measure zero. (`shapeKnotsNullSpace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeKnotsNull.lean#L188)).

### Breakdown.CertCell.ShapeLogPhase

This file checks the logarithmic radial phase, including its first three derivatives and the positivity needed for the shifted logarithm. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Open-set equality preserves derivatives.** Proved result. If F and G agree on an open set and G has derivative H there, then F′(t) = H(t) at every point of that set. (`deriv_eq_of_eqOn_open`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeLogPhase.lean#L13)).

**The shifted coordinate is positive.** Proved result. Whenever t > −c, the shifted argument c+t is strictly positive. (`shifted_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeLogPhase.lean#L21)).

**The logarithmic phase derivative.** Proved result. For positive c and t greater than −c, the derivative of rate/2 times log(1+t/c) is rate divided by 2(c+t). (`logPhase_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeLogPhase.lean#L25)).

**The shifted reciprocal derivative.** Proved result. For t greater than −c, the derivative of rate divided by 2(c+t) is −rate divided by 2(c+t)². (`inv_shift_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeLogPhase.lean#L40)).

**The shifted reciprocal-square derivative.** Proved result. For t greater than −c, the derivative of −rate divided by 2(c+t)² is rate divided by (c+t)³. (`inv_sq_shift_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeLogPhase.lean#L46)).

**A positive scale gives a radial phase.** Proved result. For c > 0, the phase f(s) = (rate/2)log(1+s/c) is C³ on a neighborhood of [0,∞), and s f′(s), s²f″(s) and s³f‴(s) are uniformly bounded for s ≥ 0. (`radial_of_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeLogPhase.lean#L55)).

**The logarithmic phase is admissible.** Proved result. For any real rate and positive base scale c, the logarithmic radial phase (rate/2)log(1+s/c) has the three smooth derivatives and scaled derivative bounds required by the shape construction. (`logPhaseIsRadial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeLogPhase.lean#L111)).

### Breakdown.CertCell.ShapeMeasurable

This file passes measurability from the scalar chart values and speed data to the bound data used by the cell-layer argument. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Scalar value data give measurable bounds.** Proved result. Measurability of chart bounds makes the epsilon and mu speeds and all supplied harmonic bounds measurable when they are identified with those chart evaluations. (`measurableBoundData_of_valueSets`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeMeasurable.lean#L17)).

**Bound entries give measurable bounds.** Proved result. A valid bound-value entry gives measurable speed and harmonic bound data at every certified parameter. (`boundsMeasurable_of_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeMeasurable.lean#L33)).

### Breakdown.CertCell.ShapeModeOrthogonal

This file evaluates the time and angular Fourier averages of finite real wave sums, including their conjugate-frequency contributions. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Circle averaging selects frequency zero.** Proved result. Circle integration selects zero frequency. (`circle_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L9)).

**Time integration selects zero frequency.** Proved result. For integer m, ∫₀¹ exp(2πimτ)dτ equals 1 when m = 0 and equals 0 otherwise. (`line_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L32)).

**Angular averaging selects the zero mode.** Proved result. Angular integration selects the zero mode. (`inner_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L58)).

**Time integration removes nonzero modes.** Proved result. For a complex coefficient c and integer m, ∫₀¹ c exp(2πimτ)dτ equals c when m = 0 and equals 0 otherwise. (`outer_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L76)).

**Double averaging selects matching modes.** Proved result. Integrating a finite sum of temporal and angular exponential waves over τ ∈ [0,1] and φ ∈ [0,2π] keeps only terms with both frequencies zero, multiplying each surviving coefficient by 2π. (`double_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L82)).

**A real wave splits into conjugate waves.** Proved result. Writing Eν = exp(i(2πν₁τ+ν₂φ)), one has E₋ξ Re(wEν) = (w/2)Eν₋ξ+(conj(w)/2)E₋ν₋ξ, separating a real wave into its two complex frequencies. (`pointwise_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L126)).

**Two zero-frequency tests combine.** Proved result. Successively selecting zero temporal and angular frequency is equivalent to selecting the pair (0,0) at once, with the same angular integral factor 2π. (`ite_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L157)).

**Mode averaging selects wave coefficients.** Proved result. For a finite real sum of complex waves, its normalized coefficient at frequency ξ is the sum of w/2 from waves of frequency ξ and conj(w)/2 from waves of frequency −ξ. (`modeAverage_of_waveSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L165)).

**A real wave has two conjugate modes.** Proved result. A single real wave Re(w eⁱν·θ) has normalized coefficient w/2 at ν and conj(w)/2 at −ν, with both contributions added when ν = 0. (`modeAverage_of_wave`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L204)).

**Velocity modes select wave coefficients.** Proved result. If the velocity after time translation and rotation has a finite real wave expansion, its mode at ξ is the sum of half the vector coefficients at ξ and half the conjugate coefficients at −ξ. (`modeVel_of_waveSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L213)).

**Gradient modes select wave coefficients.** Proved result. If the gradient, with both its point and vector directions rotated, has a finite real wave expansion, its mode at ξ selects half the coefficients at ξ and half the conjugate coefficients at −ξ. (`modeGrad_of_waveSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L223)).

**Hessian modes select wave coefficients.** Proved result. If the Hessian, with its point and both input directions rotated, has a finite real wave expansion, its mode at ξ selects half the coefficients at ξ and half the conjugate coefficients at −ξ. (`modeSecondDeriv_of_waveSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeModeOrthogonal.lean#L234)).

### Breakdown.CertCell.ShapeOriginProfile

This file treats the origin correction as a polynomial joined to a constant tail and proves its C² and local second-derivative Lipschitz properties. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Polynomial evaluation is smooth.** Proved result. Evaluating a real polynomial as a function of its real argument gives a smooth function, hence a function of every finite differentiability order. (`polynomial_eval_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L11)).

**Clamping preserves a zero joining slope.** Proved result. If φ is differentiable everywhere and φ′(a) = 0, then t ↦ φ(min(t,a)) is differentiable with derivative φ′(min(t,a)), including at the joining point a. (`clamp_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L16)).

**The origin polynomial joins its tail.** Proved result. For an admissible origin profile whose joining point e lies below 1, the polynomial value at e equals the constant tail value. (`join_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L39)).

**The joining first derivative vanishes.** Proved result. For a valid origin profile whose joining edge is below one, the polynomial first derivative vanishes at that edge. (`join_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L43)).

**The joining second derivative vanishes.** Proved result. For a valid origin profile whose joining edge is below one, the polynomial second derivative vanishes at that edge. (`join_curvature`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L47)).

**Origin profile is a clamped polynomial.** Proved result. For an admissible origin profile with joining point e < 1, its value at t is p(min(t,e)), where p is the defining polynomial. (`eval_eq_clamp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L51)).

**Differentiating the clamped profile.** Proved result. The derivative of an admissible clamped origin profile is its polynomial derivative evaluated at the smaller of the argument and the edge. (`eval_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L59)).

**Differentiate the clamped profile.** Proved result. For a valid joining edge below one, the profile derivative is its polynomial derivative evaluated at the argument clamped above by that edge. (`deriv_eq_clamp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L65)).

**The clamped derivative differentiates.** Proved result. For a valid joining edge below one, the profile derivative has derivative equal to the polynomial second derivative evaluated at the clamped argument. (`deriv_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L69)).

**The clamped second derivative.** Proved result. For a valid joining edge below one, the second derivative as a function is the polynomial second derivative composed with clamping at the edge. (`second_deriv_eq_clamp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L76)).

**The joined origin profile is C².** Proved result. An admissible origin profile whose edge is strictly below one is globally C² after its polynomial is clamped to the tail. (`eval_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L80)).

**Second derivative is locally Lipschitz.** Proved result. For an admissible origin profile with joining point below 1, the second derivative is Lipschitz on every interval [−R,R], with a constant allowed to depend on R. (`second_deriv_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L90)).

**Polynomial profiles below the edge.** Proved result. When the profile edge equals one, the profile evaluation below one equals its polynomial evaluation. (`eval_eq_poly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L108)).

**Polynomial endpoint second derivatives.** Proved result. If the origin profile's endpoint is 1, its second derivative at each t < 1 is the value of the second derivative of its defining polynomial. (`second_deriv_eq_poly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L113)).

**The origin profile satisfies regularity.** Proved result. An admissible origin profile is C² below one and its second derivative is Lipschitz on every centered closed interval with radius less than one. (`originProfileSmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeOriginProfile.lean#L123)).

### Breakdown.CertCell.ShapeScalarStatements

This file specifies the rational Bernstein coefficient format for scalar weights and step bounds, including mesh validity, derivative joins, signs, defaults and reflection data. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Measurability and symmetry of minima.** Proposition definition. This proposition requires planar step minima to be measurable, invariant under axial rotations, and compatible with reflecting the step data. (`PlaneMinEvalFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L20)).

**Reflection of a chart bound.** Definition. Reflecting a chart bound mirrors its data and retains its radial power and origin value. (`mirror`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L26)).

**Measurability and symmetry of bounds.** Proposition definition. This proposition requires chart-bound evaluations to be measurable, invariant under axial rotations, and compatible with reflected bound data. (`ChartBoundFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L30)).

**Integers over natural denominators.** Data structure. A fraction stores an integer numerator and a natural-number denominator without imposing positivity on the denominator. (`Frac`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L34)).

**The rational value of a fraction.** Definition. The value of a stored fraction is the rational quotient of its numerator and denominator using Lean's totalized division. (`val`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L40)).

**An integer represented as a fraction.** Definition. An integer is stored as a fraction with denominator one. (`ofInt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L42)).

**Addition of fraction representations.** Definition. Fraction addition uses the cross-sum numerator and the product denominator. (`add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L44)).

**Multiplication of fractions.** Definition. Fraction multiplication multiplies the two numerators and the two denominators. (`mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L46)).

**Negation of a fraction representation.** Definition. Negating a fraction negates its numerator and retains its denominator. (`neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L48)).

**Subtraction of fraction representations.** Definition. Fraction subtraction adds the negated second fraction to the first. (`sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L50)).

**Natural powers of fractions.** Definition. Natural powers of stored fractions use denominator-one unity at exponent zero and repeated fraction multiplication. (`pow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L52)).

**A finite sum of fractions.** Definition. A list of stored fractions is summed recursively from the denominator-one representation of zero. (`sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L56)).

**Fraction lookup with an integer default.** Definition. Fraction lookup returns the requested list entry or the supplied integer represented with denominator one. (`fracAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L62)).

**A mesh with rational breakpoints.** Data structure. A rational mesh stores separate lists of fractional radial and height breakpoints. (`RationalMesh`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L64)).

**Rational mesh interpreted over the reals.** Definition. A rational mesh becomes a real tensor mesh by evaluating and casting each stored breakpoint. (`toMesh`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L70)).

**Valid ordered rational mesh data.** Proposition definition. Valid rational meshes have positive denominators, strictly increasing cross-products, and endpoints zero and one in both coordinates. (`IsValid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L73)).

**The radial mesh cell count.** Definition. The radial cell count is the radial breakpoint-list length minus one, using natural subtraction. (`tCount`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L81)).

**The height mesh cell count.** Definition. The height cell count is the height breakpoint-list length minus one, using natural subtraction. (`xCount`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L83)).

**A radial cell width as a fraction.** Definition. A radial cell width subtracts adjacent fractional breakpoints with default endpoints zero and one. (`tWidth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L85)).

**A height cell width as a fraction.** Definition. A height cell width subtracts adjacent fractional breakpoints with default endpoints zero and one. (`xWidth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L87)).

**A Bernstein basis on a physical interval.** Definition. A physical-cell Bernstein basis substitutes the normalized affine coordinate (x−lo)/(hi−lo) into a Bernstein polynomial. (`cellBasisPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L91)).

**Coefficient lookup with zero default.** Definition. A missing row or column coefficient is interpreted as the denominator-one fraction zero. (`coefAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L95)).

**Tensor-product Bernstein cell polynomial.** Definition. A cell polynomial sums the stored coefficients against the product of radial and height Bernstein bases. (`cellPiecePoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L97)).

**Forward coefficient differences.** Definition. The order-o forward difference is the alternating binomial sum of the first o+1 coefficients. (`windowDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L101)).

**A width-scaled coefficient difference.** Definition. A scaled coefficient difference multiplies the forward difference by the descending degree factorial and the specified width to the derivative order. (`scaledDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L105)).

**Cross-product relation for fractions.** Proposition definition. The stored fraction relation equates numerator-denominator cross products without requiring nonzero denominators. (`FracEq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L108)).

**Cross-product equality is decidable.** Instance. For two integer-numerator, natural-denominator pairs, equality of their cross-products can be determined by an exact integer comparison. (`unnamed instance at line 110`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L110)).

**One half of a coefficient scalar.** Data structure. One scalar half stores a rational tensor mesh, two polynomial degrees, and the coefficient arrays for its cells. (`CoefficientHalf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L112)).

**The coefficients of one mesh cell.** Definition. Cell coefficient lookup returns the selected two-dimensional array or an empty array when either cell index is missing. (`cell`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L122)).

**Bernstein coefficients as a spline.** Definition. The coefficient half is interpreted as a spline whose cell pieces are its tensor-product Bernstein polynomials. (`toSpline`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L124)).

**Positive denominators for coefficients.** Proposition definition. Coefficient denominator positivity requires a positive denominator at every in-range cell and polynomial coefficient. (`CoefDenPos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L129)).

**Radial derivative matching clauses.** Proposition definition. Radial joining requires cross-multiplied finite differences from neighboring radial cells to match through the chosen derivative order. (`TJoins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L132)).

**Height derivative matching clauses.** Proposition definition. Height joining requires cross-multiplied finite differences from neighboring height cells to match through the chosen derivative order. (`XJoins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L137)).

**Nonnegative coefficient numerators.** Proposition definition. Coefficient nonnegativity requires every in-range stored numerator to be nonnegative. (`CoefNonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L142)).

**Constant coefficients below a breakpoint.** Proposition definition. The constant-region condition equates all coefficients of cells ending below the chosen breakpoint with one stored value. (`CoefConstantBelow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L145)).

**Constant coefficients on the first edge.** Proposition definition. The initial-edge condition equates the radial-degree-zero coefficients in the first radial cells with one stored value. (`CoefFlatAtZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L150)).

**Radial matching is decidable.** Instance. Matching radial derivatives through a prescribed order across every cell interface can be checked by finitely many exact cross-product equalities between the rational coefficients. (`unnamed instance at line 153`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L153)).

**Height matching is decidable.** Instance. Matching height derivatives through a prescribed order across every cell interface can be checked by finitely many exact cross-product equalities between the rational coefficients. (`unnamed instance at line 155`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L155)).

**Coefficient nonnegativity is decidable.** Instance. Nonnegativity of every coefficient numerator in the prescribed cells and degree ranges can be checked by finitely many integer comparisons. (`unnamed instance at line 157`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L157)).

**Denominator positivity is decidable.** Instance. Strict positivity of every coefficient denominator in the prescribed cells and degree ranges can be checked by finitely many integer comparisons. (`unnamed instance at line 159`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L159)).

**Constant coefficient region is decidable.** Instance. The finite test for constant coefficients below a radial threshold can be evaluated exactly using integer cross-products to select cells and compare their coefficients with the prescribed value. (`unnamed instance at line 161`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L161)).

**Initial flatness is decidable.** Instance. The condition that all initial radial coefficients equal a prescribed rational value can be checked by finitely many exact cross-product equalities. (`unnamed instance at line 163`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L163)).

**Rational mesh validity is decidable.** Instance. Validity of a finite rational mesh can be determined from its finite endpoint, ordering and denominator conditions. (`unnamed instance at line 167`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L167)).

**Upper and lower coefficient scalars.** Data structure. A coefficient scalar pairs upper and lower coefficient halves with a natural decay order. (`CoefficientScalar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L169)).

**Coefficients as a chart scalar.** Definition. A coefficient scalar becomes a chart scalar by interpreting both halves as splines and retaining the decay order. (`toChartScalar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L178)).

**Reflection swaps the two scalar halves.** Definition. Reflecting a coefficient scalar exchanges its upper and lower halves and preserves the decay order. (`mirror`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L180)).

**Derivative matching across the plane.** Proposition definition. Plane joining matches cross-multiplied height differences across the two halves with a sign determined by derivative parity. (`PlaneJoins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L182)).

**Plane matching is decidable.** Instance. Matching upper and lower polynomial pieces across the symmetry plane through a prescribed derivative order can be checked by finitely many rational equalities, including the sign (−1)ᵒ at order o. (`unnamed instance at line 188`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L188)).

**All coefficient joining conditions.** Proposition structure. The joining package requires positive coefficient denominators, matching radial meshes and degrees, and all radial, height, and plane derivative joins. (`JoinClauses`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L190)).

**Nonnegativity in both scalar halves.** Proposition definition. Scalar coefficient nonnegativity combines positive denominators with nonnegative numerators in both halves. (`CoefNonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L202)).

**Constant core specified by coefficients.** Proposition definition. A constant-core certificate requires a positive core breakpoint present in the mesh and coefficients equal to one value below that breakpoint. (`CoefConstantCore`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L204)).

**Flatness at the origin by coefficients.** Proposition definition. The flat-origin certificate requires positive denominators and one common initial-edge value in both scalar halves. (`CoefFlat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L209)).

**Rational step-function values.** Data structure. Step values consist of a rational mesh, upper and lower fractional cell values, and an integer decay order. (`StepValues`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L214)).

**Step values interpreted over the reals.** Definition. Step data are obtained by evaluating the rational mesh and the upper and lower cell fractions over the reals. (`toStepDatum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L224)).

**Reflection swaps upper and lower steps.** Definition. Reflecting step values exchanges their upper and lower arrays while preserving the mesh and decay order. (`mirror`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L228)).

**Strictly positive rational step entries.** Proposition definition. Positive step entries require a valid mesh and strictly positive numerators and denominators in every in-range cell of both halves. (`EntriesPositive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L230)).

**Step-entry positivity is decidable.** Instance. Mesh validity and strict positivity of the numerators and denominators of all upper and lower step values can be checked by finitely many exact comparisons. (`unnamed instance at line 235`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L235)).

**Rational meshes give real tensor meshes.** Proposition definition. This proposition requires every valid rational mesh to evaluate to a valid real tensor mesh. (`MeshOfRational`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L239)).

**Coefficient joins give joined scalars.** Proposition definition. This proposition requires valid meshes and coefficient joining certificates to produce a joined chart scalar. (`JoinsOfCoefficients`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L242)).

**Coefficient signs imply nonnegativity.** Proposition definition. This proposition requires valid meshes and nonnegative coefficient certificates to produce nonnegative chart-scalar values. (`NonnegOfCoefficients`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L246)).

**Constant core from constant coefficients.** Proposition definition. This proposition requires matching valid radial meshes and a constant-core coefficient certificate to produce a constant chart-scalar core. (`CoreOfCoefficients`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L250)).

**Flat coefficients give origin flatness.** Proposition definition. This proposition requires valid meshes and flat initial-edge coefficients to produce a chart scalar flat at the origin. (`FlatOfCoefficients`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L254)).

**Positive entries give positive steps.** Proposition definition. This proposition requires strictly positive rational step entries to evaluate to a positive real step function. (`StepPositiveOfEntries`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L258)).

**Rational epsilon-block values.** Data structure. An epsilon block stores its mode set, coefficient weight, two shares, length, four time parameters, and scale as rational data. (`EpsValues`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L261)).

**Rational mu-block values.** Data structure. A mu block stores its mode set, coefficient weight, share and time step data, and the real parameter eta. (`MuValues`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L273)).

**Epsilon coefficients interpreted as data.** Definition. An epsilon value block is interpreted by converting its coefficient weight and every step array to real data. (`toGiven`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L280)).

**Mu coefficients interpreted as data.** Definition. A mu value block is interpreted by converting its coefficient weight and step arrays while preserving eta. (`toGiven`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L284)).

**Reflection of epsilon-block values.** Definition. Reflecting an epsilon block reflects its mode labels and mirrors its weight and every step array. (`mirror`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L287)).

**Reflection of mu-block values.** Definition. Reflecting a mu block reflects its mode labels and mirrors its weight and step arrays while preserving eta. (`mirror`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L291)).

**Rational values for all weight data.** Data structure. The rational weight package stores chart data, a fractional central radius, mode classes, coefficient weights, epsilon and mu blocks, and two real constants. (`RationalWeightValues`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L294)).

**Rational weights as real data.** Definition. The real weight package evaluates fractional radii, coefficient scalars, and block data while preserving the supplied class map and constants. (`toWeightValues`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L309)).

**Positive steps in an epsilon block.** Proposition definition. The epsilon positivity condition requires all eight step arrays in the block to have positive entries. (`StepsPositive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L322)).

**Positive steps in a mu block.** Proposition definition. The mu positivity condition requires its share and time arrays to have positive entries. (`StepsPositive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L326)).

**Shape requirements for rational weights.** Proposition structure. The rational weight shape conditions require a finite class type, valid charts and meshes, constants between zero and one, and decay orders zero, one, and two for the designated weights. (`WeightValuesShape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L328)).

**Coefficient conditions for the weights.** Proposition structure. The weight coefficient package combines derivative joins, constant cores, flatness, nonnegativity, positive steps, positive eta, and invariance under negating mode labels. (`WeightCoefficientsGiven`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L344)).

**Reflection closure of rational weights.** Proposition structure. Rational reflection closure identifies reflected class weights and permutes the epsilon and mu blocks onto their mirrors. (`IsMirrorClosedRational`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L362)).

**Coefficient conditions validate weights.** Proved result. The rational-mesh, joining, sign, core, flatness, and positivity assumptions turn a weight package with the coefficient certificates into valid real weight data. (`isWeightValues_of_conditions`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L369)).

**Rational flip closure gives symmetry.** Proved result. Rational reflection closure gives symmetry. (`isFlipClosed_of_rational`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L423)).

**Reflection closure of bound-value sets.** Proposition structure. Mirrored bound-value sets require reflected harmonic labels, reflected amplitude bounds, and reflection-fixed supremum bounds. (`BoundValueSetsMirrorClosed`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L444)).

**Flip and rotation of bound functions.** Proposition structure. The bound symmetry package requires reflection compatibility and axial rotation invariance for amplitudes and supremum bounds. (`BoundValuesFlipFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L453)).

**Bound symmetry from mirrored values.** Proved result. Mirrored bound values give bound symmetry. (`boundValuesFlipFacts_of_mirror`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L466)).

**Mirrored speeds give speed symmetry.** Proved result. Assuming the chart-bound identities, a permutation pairing each speed bound with its mirror makes every evaluated bound axisymmetric and gives vₚ₍β₎(Ry) = vβ(y) for the half-turn R. (`speedFacts_of_values`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeScalarStatements.lean#L490)).

### Breakdown.CertCell.ShapeSecondSymmetric

This file names symmetry of the chosen shape Hessian and transfers it from shape or jet entries to the cell-layer Hessian. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Symmetry of the shape Hessian.** Proposition definition. This proposition requires the shape Hessian to be unchanged when its two direction arguments are exchanged. (`FieldSecondSymmetric`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSecondSymmetric.lean#L11)).

**Shape entries give symmetric Hessians.** Proved result. Assuming symmetry of the constructed shape Hessian, admissible supplied shape data give H(σ,y)[u,w] = H(σ,y)[w,u] for all times, points and directions. (`givenSecondSymmetric_of_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSecondSymmetric.lean#L15)).

**Jet entries give symmetric Hessians.** Proved result. Assuming the jet construction results and symmetry of the shape Hessian, admissible supplied jet data give H(σ,y)[u,w] = H(σ,y)[w,u]. (`givenSecondSymmetric_of_jets`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSecondSymmetric.lean#L21)).

### Breakdown.CertCell.ShapeSecondSymmetricProof

This file proves symmetry of the totalized second Fréchet derivative and transfers it to the key and shape Hessians under the stated C¹ regularity. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**The totalized C¹ Hessian is symmetric.** Proved result. A C¹ function has a symmetric totalized second Fréchet derivative. (`secondDeriv_symmetric_of_contDiff_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSecondSymmetricProof.lean#L13)).

**Symmetric Hessians of regular keys.** Proved result. C¹ key fields with locally Lipschitz gradients have symmetric totalized second derivatives. (`keySecondDeriv_symmetric_of_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSecondSymmetricProof.lean#L21)).

**Shape Hessian symmetry from regularity.** Proved result. The key regularity assumptions imply symmetry of the assembled shape Hessian. (`fieldSecondSymmetric_of_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSecondSymmetricProof.lean#L33)).

### Breakdown.CertCell.ShapeSphericalDiv

This file expresses the divergence of a field written in the spherical frame, keeping the off-axis differentiability conditions explicit. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**A field in the spherical frame.** Definition. The spherical-frame field multiplies a radial, polar, and azimuthal amplitude combination by the key's complex phase. (`framedField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDiv.lean#L15)).

**The framed field is a three-term sum.** Proved result. The field reconstructed from three reduced components is the sum of the radial, polar and azimuthal frame vectors, each multiplied by its component and the common complex phase. (`framedField_eq_frameSum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDiv.lean#L24)).

**Spherical divergence away from the axis.** Proved result. Away from the axis, the divergence of a differentiable spherical-frame field equals phase divided by radius times the radial, weighted height, and angular-frequency contributions. (`complexDivergence_framedField_offAxis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDiv.lean#L34)).

**A coordinate patch gives divergence.** Proved result. For admissible shape parameters, differentiable reduced components and y₂ ≠ 0, the divergence is the phase divided by |y| times Dⱼuᵣ + 2uᵣ − ∂ₓ((1−x²)uθ) + inuφ. (`complexDivergence_framedField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDiv.lean#L145)).

**Framed fields differentiate off-axis.** Proved result. For admissible shape parameters, differentiability of all three reduced components in compactified radius and normalized height gives differentiability of the reconstructed spatial field away from the rotation axis. (`framedField_differentiableAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDiv.lean#L156)).

**Spherical divergence of key fields.** Proved result. Away from the axis, the key-field divergence is the spherical divergence expression evaluated on its reduced components. (`complexDivergence_keyVector_offAxis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDiv.lean#L178)).

### Breakdown.CertCell.ShapeSphericalDivFrame

This file computes derivatives and divergences of the radial, polar and azimuthal frames, then combines them with the chart and phase chain rules. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Inner products are coordinate sums.** Proved result. For y,w ∈ R³, their Euclidean inner product is y₁w₁+y₂w₂+y₃w₃. (`inner_coords`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L17)).

**Coordinate squares give the norm squared.** Proved result. For y ∈ R³, the sum y₁y₁+y₂y₂+y₃y₃ equals |y|². (`coords_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L20)).

**The norm derivative is a unit covector.** Proved result. At a nonzero point, the norm has Fréchet derivative given by the inner product with that point divided by its norm. (`norm_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L24)).

**Directional derivative of the norm.** Proved result. Away from zero, the directional derivative of the norm is the position-direction inner product divided by the position norm. (`norm_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L31)).

**Radial composition obeys the chain rule.** Proved result. If y ≠ 0 and h is differentiable at |y|, then D(h∘|·|)(y)[w] = h′(|y|)(y·w)/|y| for every direction w. (`radial_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L39)).

**Radial differentiability away from zero.** Proved result. Radial compositions differentiate off zero. (`radial_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L46)).

**Differentiating a coordinate.** Proved result. A coordinate derivative selects a component. (`coord_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L50)).

**Coordinates are differentiable.** Proved result. Each Cartesian coordinate function y ↦ yⱼ is differentiable at every point of R³. (`coord_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L56)).

**Reciprocal norm differentiates off zero.** Proved result. The function y ↦ 1/|y| is differentiable at every nonzero point of R³. (`inv_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L59)).

**The reciprocal norm derivative.** Proved result. Away from zero, the directional derivative of reciprocal radius is minus the inner product with the direction divided by radius cubed. (`inv_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L62)).

**The inverse-square norm differentiates.** Proved result. The reciprocal squared norm is differentiable at every nonzero point. (`inv_sq_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L68)).

**Divergence obeys the product rule.** Proved result. If a scalar c and vector field W are differentiable at y, then div(cW)(y) = Dc(y)[W(y)] + c(y)div W(y). (`div_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L72)).

**Divergence is additive.** Proved result. For vector fields F and G differentiable at y, div(F+G)(y) = div F(y)+div G(y). (`div_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L88)).

**Adding constants preserves divergence.** Proved result. Constant vectors do not change divergence. (`div_add_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L95)).

**The identity field has divergence three.** Proved result. The vector field y ↦ y has divergence 3 at every point of R³. (`div_id`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L100)).

**Constant fields have zero divergence.** Proved result. For every constant vector v, the field y ↦ v has divergence zero everywhere. (`div_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L105)).

**The radial frame field.** Definition. The radial frame field is the position vector divided by its norm. (`radialField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L109)).

**The scaled polar frame field.** Definition. The polar frame field is the position vector times height over radius squared, minus the third unit vector. (`polarField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L111)).

**The scaled azimuthal frame field.** Definition. The azimuthal frame field is the planar quarter-turn vector divided by total radius. (`azimField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L113)).

**The radial field matches its coordinates.** Proved result. The vector y/|y| has exactly the Cartesian components prescribed for the radial frame vector, with inverse radius taken to be zero at the origin. (`radialField_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L115)).

**The polar field matches its coordinates.** Proved result. The vector (y₃/|y|²)y−e₃ has exactly the Cartesian components prescribed for the polar frame vector, including the convention at the origin. (`polarField_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L118)).

**Azimuthal field matches its coordinates.** Proved result. The vector (−y₂,y₁,0)/|y| has exactly the Cartesian components prescribed for the azimuthal frame vector, with inverse radius taken to be zero at the origin. (`azimField_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L121)).

**The radial field differentiates off zero.** Proved result. The radial frame field y ↦ y/|y| is differentiable away from the origin. (`radialField_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L124)).

**The polar field differentiates off zero.** Proved result. The polar frame field y ↦ (y₃/|y|²)y−e₃ is differentiable away from the origin. (`polarField_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L127)).

**Azimuthal field differentiates off zero.** Proved result. The azimuthal frame field y ↦ (−y₂,y₁,0)/|y| is differentiable away from the origin. (`azimField_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L130)).

**Radial divergence is two over radius.** Proved result. For y ≠ 0, the radial unit field satisfies div(y/|y|) = 2/|y|. (`div_radialField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L133)).

**The polar frame divergence.** Proved result. Away from zero, the polar-frame divergence is twice the third coordinate divided by radius squared. (`div_polarField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L141)).

**Zero azimuthal divergence off zero.** Proved result. The azimuthal frame has zero divergence away from the origin. (`div_azimField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L156)).

**The compactified radius derivative.** Proved result. For a positive chart length and a nonzero point, the compactified-radius derivative is the radial derivative multiplied by the chart length over the squared shifted radius. (`chartCoord_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L172)).

**The normalized height derivative.** Proved result. Away from zero, differentiating normalized height gives the third direction coordinate over radius minus the third position coordinate times the radial inner product over radius cubed. (`heightRatio_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L187)).

**The radial phase derivative.** Proved result. Composing an admissible radial phase with squared radius gives twice the radial inner product times the phase derivative. (`radialPhase_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L203)).

**The complex plane-coordinate derivative.** Proved result. The derivative of the complex horizontal coordinate sends a direction to its first coordinate plus i times its second coordinate. (`planeCoord_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L217)).

**The angle derivative off its branch cut.** Proved result. Where the first coordinate is positive or the second is nonzero, the angle derivative is the oriented planar area divided by cylindrical radius squared. (`pointAngle_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L229)).

**Negation adds the integer angular phase.** Proved result. Away from the axis, replacing y by −y changes an integer angular wave by the factor exp(ikπ): eⁱᵏθ⁽ʸ⁾ = eⁱᵏθ⁽⁻ʸ⁾eⁱᵏπ. (`angularExp_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L254)).

**Angular waves differentiate off-axis.** Proved result. For integer k and a point off the axis, the angular wave eⁱᵏθ is differentiable with directional derivative eⁱᵏθ ik(y₁w₂−y₂w₁)/(y₁²+y₂²). (`angularExp_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L277)).

**The key phase splits into two factors.** Proved result. A mode's phase factors as exp(i(2πkσ+jβ(|y|²))) exp(inθ(y)), separating the temporal and radial oscillation from the angular wave. (`keyPhase_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L325)).

**Differentiate the key phase.** Proved result. Off the axis, the directional derivative of a key phase is i times that phase times the sum of its azimuthal frequency times the angular directional change and twice its radial phase index times the radial phase slope at squared radius times the position-direction inner product. (`keyPhase_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L335)).

**The two-variable chart chain rule.** Proved result. A differentiable two-variable chart composition differentiates as the sum of its two partial derivatives weighted by the chart-coordinate derivatives. (`comp_hasFDerivAt_chart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L356)).

**Real vectors embedded in complex space.** Definition. The complex lifting map embeds each coordinate of a real spatial vector into the complex numbers. (`liftVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L381)).

**Complex lifting preserves coordinates.** Proved result. Embedding a real vector in C³ preserves each Cartesian coordinate, now regarded as a complex number with zero imaginary part. (`liftVec_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L384)).

**Divergence of a complex weighted vector.** Proved result. The trace of the complex weighted-vector derivative is the scalar times the vector divergence plus the scalar derivative applied to the vector. (`cdiv_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L387)).

**Three linear maps have additive trace.** Proved result. For three linear maps A,B,C from R³ to C³, the diagonal sum of A+B+C equals the sum of their three diagonal sums. (`sum_three_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSphericalDivFrame.lean#L400)).

### Breakdown.CertCell.ShapeSplineAgree

This file proves the equivalence laws for spline agreement and shows that agreement respects joining, conjugation, reflection and evaluation. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Reflection preserves scalar factors.** Proved result. For a complex scalar c and polynomial P(t,x), reflection in the second variable satisfies (cP)(t,−x) = cP(t,−x). (`reflectPoly_C_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L15)).

**Polynomial reflection is an involution.** Proved result. Applying the substitution x ↦ −x twice to a two-variable complex polynomial returns the original polynomial. (`reflectPoly_reflectPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L20)).

**Reflection commutes with conjugation.** Proved result. Conjugating the coefficients of P(t,−x) gives the same polynomial as replacing x by −x after conjugating the coefficients of P(t,x). (`map_reflectPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L31)).

**Polynomial conjugation is an involution.** Proved result. Conjugating every coefficient of a complex polynomial twice returns the original polynomial. (`map_conj_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L42)).

**A parity sign squares to one.** Proved result. The sign ε used for even or odd reflection satisfies ε² = 1 in both cases. (`sign_mul_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L48)).

**A parity sign is real.** Proved result. The sign ε ∈ {1,−1} used for reflection is unchanged by complex conjugation. (`sign_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L51)).

**Reflection preserves the cell count.** Proved result. Negating and reversing a finite breakpoint list leaves its number of cells unchanged. (`cellCount_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L54)).

**Spline agreement is reflexive.** Proved result. Every spline agrees with itself in its mesh and in every polynomial piece used on that mesh. (`agrees_refl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L57)).

**Spline agreement is symmetric.** Proved result. If two splines agree in their meshes and relevant polynomial pieces, the same agreement holds with their roles interchanged. (`agrees_symm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L59)).

**Spline agreement is transitive.** Proved result. If S agrees with T and T agrees with U in their meshes and polynomial pieces, then S agrees with U. (`agrees_trans`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L64)).

**Conjugation preserves spline agreement.** Proved result. Agreement of two splines in their mesh and polynomial pieces is preserved when all coefficients of both splines are conjugated. (`agrees_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L72)).

**Reflection preserves spline agreement.** Proved result. Applying the same even or odd reflection to two agreeing splines preserves agreement of the reflected meshes and pieces. (`agrees_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L77)).

**Double conjugation gives agreement.** Proved result. Conjugating a spline twice produces a spline with the same mesh and relevant polynomial pieces as the original. (`agrees_conj_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L88)).

**Double reflection gives agreement.** Proved result. Reflecting a spline twice with the same even or odd sign produces a spline agreeing with the original on its mesh and pieces. (`agrees_reflect_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L91)).

**Spline reflection respects conjugation.** Proved result. Spline reflection commutes with conjugation. (`agrees_reflect_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L107)).

**Agreement transports spline joins.** Proved result. If S and T agree in their meshes and polynomial pieces, any derivative-matching orders (a,b) satisfied by S are also satisfied by T. (`joined_of_agrees`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L113)).

**Distinct endpoints require two breaks.** Proved result. A finite breakpoint list whose first and last entries are distinct must contain at least two entries. (`two_le_length_of_ends`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L124)).

**A cell index is below the cell count.** Proved result. For a breakpoint list containing at least two entries, every real coordinate is assigned an index strictly below the number of cells. (`cellIndex_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L135)).

**Agreement on a full mesh gives equality.** Proved result. Spline agreement on a full mesh gives equal evaluated values at every coordinate pair. (`evalHalf_of_agrees`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L141)).

**Spline agreement laws.** Proved result. Spline agreement is an equivalence relation compatible with reflection, conjugation, derivative joins, and evaluation on full meshes. (`splineAgreementRules`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineAgree.lean#L151)).

### Breakdown.CertCell.ShapeSplineConj

This file shows that complex conjugation commutes with polynomial partial derivatives, edge substitutions and evaluation at real coordinates. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Radial derivatives respect conjugacy.** Proved result. Radial derivatives commute with conjugacy. (`tDeriv_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineConj.lean#L15)).

**Height derivatives respect conjugacy.** Proved result. Height derivatives commute with conjugacy. (`xDeriv_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineConj.lean#L23)).

**First substitution respects conjugacy.** Proved result. First substitution commutes with conjugacy. (`atFirst_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineConj.lean#L31)).

**Second substitution respects conjugacy.** Proved result. Substituting a real number for the second variable of a complex polynomial commutes with conjugation of its coefficients. (`atSecond_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineConj.lean#L41)).

**Real evaluation commutes with conjugacy.** Proved result. At real coordinates (t,x), evaluation of the coefficientwise conjugate polynomial equals the conjugate of the original value P(t,x). (`eval_real_map_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineConj.lean#L51)).

**Conjugation preserves joined splines.** Proved result. Conjugating all coefficients preserves a spline's derivative-matching orders, and the resulting spline evaluates to the conjugate of the original value at every real pair (t,x). (`splineConjugation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineConj.lean#L62)).

### Breakdown.CertCell.ShapeSplineDeriv

This file identifies classical derivatives of joined splines with derivatives of the selected polynomial piece, including one-sided behavior at mesh breaks. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**The two polynomial partials commute.** Proved result. The two formal partial derivatives of a complex polynomial in t and x commute: ∂ₜ∂ₓP = ∂ₓ∂ₜP. (`pderiv_zero_one_comm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L17)).

**Height derivatives respect radial ones.** Proved result. Height derivatives commute with radial ones. (`xDeriv_pderiv_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L25)).

**Radial derivatives respect height ones.** Proved result. Radial derivatives commute with height ones. (`tDeriv_pderiv_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L31)).

**Height substitution keeps radial slopes.** Proved result. Height substitution preserves radial slopes. (`atSecond_pderiv_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L37)).

**Radial substitution keeps height slopes.** Proved result. Radial substitution preserves height slopes. (`atFirst_pderiv_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L46)).

**Fixing the first input preserves value.** Proved result. Fixing the first polynomial variable at c leaves its evaluation at (c,y) unchanged. (`eval_atFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L55)).

**Fixing the second input preserves value.** Proved result. Fixing the second polynomial variable at c leaves its evaluation at (y,c) unchanged. (`eval_atSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L63)).

**Differentiate the first polynomial input.** Proved result. Differentiating a polynomial along its first real input gives its first polynomial partial derivative evaluated at the same point. (`hasDerivAt_eval_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L71)).

**Differentiate the second input.** Proved result. Differentiating a polynomial along its second real input gives its second polynomial partial derivative evaluated at the same point. (`hasDerivAt_eval_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L98)).

**Distinct endpoints need two breaks.** Proved result. A finite breakpoint list whose first and last entries are distinct must contain at least two entries. (`two_le_length`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L125)).

**Cell indices stay within the mesh.** Proved result. For a breakpoint list containing at least two entries, every real coordinate is assigned an index strictly below the number of cells. (`cellIndex_lt_count`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L135)).

**Cell indices are locally right constant.** Proved result. For any breakpoint list and coordinate u, all sufficiently close coordinates s ≥ u are assigned the same cell as u. (`cellIndex_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L141)).

**Left cell indices count strict breaks.** Proved result. For s approaching u from below, the selected cell index eventually equals the number of interior breakpoints strictly less than u. (`cellIndex_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L158)).

**Ordered break counts are exact.** Proved result. In a strictly increasing list, exactly p entries lie below its entry at position p, and exactly p+1 entries lie at or below it, counting positions from zero. (`sorted_counts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L176)).

**Matching pieces have one derivative.** Proved result. Strictly ordered differentiable pieces whose values and first derivatives match at every internal breakpoint give the selected piecewise derivative everywhere. (`piecewise_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L198)).

**Derivatives and joins of splines.** Proved result. At a positive joining order, a joined spline differentiates to its corresponding derivative spline and loses one order of joining in that coordinate. (`splineDerivatives_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineDeriv.lean#L255)).

### Breakdown.CertCell.ShapeSplineReflect

This file reverses the height mesh and polynomial argument, accounting for the sign of each height derivative and the selected cell at a reflected breakpoint. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Evaluate a polynomial substitution.** Proved result. Evaluating a polynomial after polynomial substitution equals evaluating the original polynomial at the values of the substituted polynomials. (`eval_bind_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L15)).

**Reflection preserves scalar factors.** Proved result. Reflection P(t,x) ↦ P(t,−x) commutes with multiplication by a fixed complex scalar. (`reflectPoly_C_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L22)).

**Radial partials commute with reflection.** Proved result. The first-coordinate polynomial derivative commutes with reflection of the second coordinate: ∂ₜ(P(t,−x)) = (∂ₜP)(t,−x). (`pderiv_zero_reflectPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L26)).

**Height partials change reflection sign.** Proved result. Differentiating a reflected polynomial in its second coordinate gives ∂ₓ(P(t,−x)) = −(∂ₓP)(t,−x). (`pderiv_one_reflectPoly`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L38)).

**Radial derivatives respect reflection.** Proved result. Radial differentiation commutes with height reflection and preserves the scalar prefactor. (`tDeriv_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L53)).

**Height derivatives acquire parity signs.** Proved result. Reflecting the height coordinate multiplies its order-o derivative by the scalar prefactor times (-1)^o. (`xDeriv_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L61)).

**First substitution respects reflection.** Proved result. First substitution commutes with reflection. (`atFirst_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L71)).

**Reflected substitution in height.** Proved result. Second substitution reflects its argument. (`atSecond_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L77)).

**Polynomial reflection reverses height.** Proved result. Evaluating a signed reflected polynomial at (t,x) gives sP(t,−x) for every complex scalar s. (`eval_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L83)).

**Substituting the evaluation point.** Proved result. Substituting the second real evaluation coordinate into a polynomial leaves its value at that coordinate pair unchanged. (`eval_atSecond_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L90)).

**Reflection preserves the cell count.** Proved result. Negating and reversing a finite breakpoint list leaves its number of cells unchanged. (`cellCount_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L96)).

**Reflection reverses interior breaks.** Proved result. The interior breakpoints of the reflected mesh are exactly the original interior breakpoints, negated and listed in reverse order. (`interior_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L99)).

**Reflected indices count reversed breaks.** Proved result. The cell index at x in the reflected mesh equals the number of original interior breakpoints b satisfying −x ≤ b. (`cellIndex_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L104)).

**Breakpoint lookup under reflection.** Proved result. Reflecting a finite breakpoint list negates the entry at the reverse index. (`getD_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L113)).

**Opposite counts partition breakpoints.** Proved result. Opposite breakpoint counts split the list. (`count_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L118)).

**Ordered breakpoint endpoint counts.** Proved result. Ordered breakpoint counts include endpoints. (`sorted_filter_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L152)).

**Distinct endpoints need two breaks.** Proved result. A finite breakpoint list whose first and last entries are distinct must contain at least two entries. (`breaks_two_le_length`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L167)).

**A cell index is below the cell count.** Proved result. Cell indices lie within the mesh. (`cellIndex_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L174)).

**Interior and shifted lookups agree.** Proved result. Interior lookup agrees with shifted lookup. (`getD_interior`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L180)).

**Reflected splines have reflected values.** Proved result. For a joined spline S, its reflected spline evaluates to εS(t,−x), where ε is 1 for even reflection and −1 for odd reflection. (`evalHalf_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L188)).

**Reflection preserves spline joins.** Proved result. Reflecting a spline in its height coordinate, with either parity sign, preserves its derivative-matching orders in both coordinates. (`joined_reflect`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L227)).

**Reflection and joining of splines.** Proved result. Reflecting a joined spline preserves its joining orders and evaluates it at negated height with the selected parity sign. (`splineReflection`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineReflect.lean#L257)).

### Breakdown.CertCell.ShapeSplineSlope

This file bounds derivatives of the finitely many polynomial pieces on boxes and uses those bounds to obtain local Lipschitz control of a joined spline gradient. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Evaluation of the selected spline piece.** Definition. The piece evaluator chooses the two cell indices and evaluates that cell's bivariate polynomial at the given coordinates. (`pieceEval`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L18)).

**The selected cell is right locally fixed.** Proved result. For any finite breakpoint list, the cell selected at u remains selected for all sufficiently close coordinates to the right of u. (`cellIndex_eventually_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L21)).

**Cell indices are bounded by the count.** Proved result. A selected cell index never exceeds the number of interior breakpoints. (`cellIndex_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L41)).

**First-variable polynomial derivatives.** Proved result. Differentiating polynomial evaluation in the first real variable evaluates the first polynomial partial derivative. (`polyEval_hasDerivAt_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L44)).

**Second-variable polynomial derivatives.** Proved result. Differentiating polynomial evaluation in the second real variable evaluates the second polynomial partial derivative. (`polyEval_hasDerivAt_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L79)).

**Right derivative of the first input.** Proved result. The right derivative in the first coordinate of the selected piecewise polynomial equals its selected first polynomial partial derivative. (`pieceEval_right_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L114)).

**Right derivative of the second input.** Proved result. The right derivative in the second coordinate of the selected piecewise polynomial equals its selected second polynomial partial derivative. (`pieceEval_right_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L123)).

**Pairs of vectors depend continuously.** Proved result. The map from a real pair (t,x) to the complex vector (t,x) is continuous. (`continuous_pairVec`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L132)).

**Cell-piece values are bounded on boxes.** Proved result. For every box |t|,|x|≤R, one nonnegative constant bounds all values of the selected polynomial pieces. (`pieceEval_bounded`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L140)).

**Slice bounds from derivative bounds.** Proved result. A continuous scalar function with right derivatives bounded by M on [−R,R] has value differences at most M times the distance between arguments in that interval. (`slice_diff_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L163)).

**Piece values are Lipschitz on boxes.** Proved result. If the selected polynomial pieces give a continuous function, their value differences on a box are bounded by a constant times the sum of coordinate differences. (`pieceEval_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L178)).

**Operator bounds from coordinate bounds.** Proved result. Coordinate directions bound operator norm. (`opNorm_le_axes`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L203)).

**Joined spline gradients are Lipschitz.** Proved result. Joined splines with at least first-order joins in both coordinates have Lipschitz gradients on every closed ball. (`joinedSplineGradSlopeBound_of_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSlope.lean#L221)).

### Breakdown.CertCell.ShapeSplineSmooth

This file glues matching polynomial pieces across ordered radial and height breaks to prove the regularity dictated by their joining orders. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Counting breaks at or below a point.** Definition. The breakpoint counter counts list entries at or below the argument. (`belowCount`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L19)).

**Ordered counting handles the first break.** Proved result. For a strictly increasing list beginning at b, the number of entries at most u is zero if u < b, and otherwise is one plus the corresponding count in the remaining list. (`belowCount_cons`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L21)).

**Breakpoint counts do not exceed length.** Proved result. The number of breakpoints at or below a real coordinate u never exceeds the length of the breakpoint list. (`belowCount_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L32)).

**No later breakpoint precedes the first.** Proved result. In a strictly increasing list beginning at b, no later entry is at or below b. (`belowCount_at`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L34)).

**Matching pieces glue continuously.** Proved result. Continuous pieces selected by a continuous scalar coordinate glue to a continuous function when the switching levels are strictly ordered and neighboring pieces agree on each switching level. (`glue_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L42)).

**Matching first derivatives glue.** Proved result. Two differentiable functions joined across a level set of a continuous coordinate remain differentiable if both their values and their derivatives agree on that level set; the derivative is the corresponding piecewise derivative. (`glue_step`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L61)).

**Gluing preserves matching derivatives.** Proved result. Differentiable pieces selected by a continuous coordinate have the selected derivative when their values and derivatives match at every strictly ordered breakpoint. (`glue_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L92)).

**Evaluating bivariate real polynomials.** Definition. The polynomial evaluator embeds both real coordinates into the complex numbers before evaluating the bivariate polynomial. (`evP`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L125)).

**Polynomial derivative as a linear map.** Definition. The polynomial derivative map sums the two coordinate projections multiplied by the corresponding evaluated polynomial partials. (`dP`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L127)).

**Pair the partials with the direction.** Proved result. Applying the polynomial derivative to a direction gives the sum of each direction coordinate times the corresponding evaluated partial derivative. (`dP_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L131)).

**Polynomial derivatives from partials.** Proved result. A bivariate polynomial evaluated on real pairs has Fréchet derivative given by its two evaluated partial derivatives acting on the direction coordinates. (`evP_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L135)).

**Polynomial evaluation is continuous.** Proved result. A complex polynomial in two real coordinates defines a continuous function on R². (`evP_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L165)).

**Agreement on a line gives radial slopes.** Proved result. If two polynomials agree for every t on the line x = x₀, their first-coordinate derivatives agree everywhere on that line. (`evP_line_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L168)).

**Agreement on a line gives height slopes.** Proved result. If two polynomials agree for every x on the line t = t₀, their second-coordinate derivatives agree everywhere on that line. (`evP_line_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L179)).

**Polynomial partial derivatives commute.** Proved result. For every complex polynomial P(t,x), the mixed polynomial derivatives satisfy ∂ₜ∂ₓP = ∂ₓ∂ₜP. (`pderiv_swap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L190)).

**Height derivatives respect radial ones.** Proved result. Height derivatives commute with radial ones. (`xDeriv_pderiv_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L198)).

**Radial derivatives respect height ones.** Proved result. Radial derivatives commute with height ones. (`tDeriv_pderiv_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L206)).

**Evaluate polynomial substitution.** Proved result. Polynomial substitution can be evaluated by first evaluating the two substituted polynomials and then using their values as the inputs to the original polynomial. (`eval_bind_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L214)).

**Evaluation after fixing the first input.** Proved result. After fixing the first polynomial variable at c, evaluation gives the original polynomial at c and the second input coordinate. (`evP_atFirst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L221)).

**Evaluation after fixing the second input.** Proved result. After fixing the second polynomial variable at c, evaluation gives the original polynomial at the first input coordinate and c. (`evP_atSecond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L228)).

**Radial joining gives equal edge values.** Proved result. Equality of two polynomial restrictions at t = c implies equality of their values at every point (c,x) on that edge. (`join_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L235)).

**Height joining gives equal edge values.** Proved result. Equality of two polynomial restrictions at x = c implies equality of their values at every point (t,c) on that edge. (`join_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L240)).

**Tensor-piece derivative matching.** Proposition structure. The tensor joining package requires neighboring pieces to match the designated radial and height derivatives along their common edges. (`Joins`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L245)).

**Joining orders can be lowered.** Proved result. Polynomial pieces matching through orders (a,b) across a tensor mesh also match through any smaller pair of orders (a′,b′). (`mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L251)).

**Radial differentiation lowers join order.** Proved result. Differentiating all pieces in the radial coordinate lowers the radial matching order from a to a−1 when a ≥ 1 and leaves the height matching order b unchanged. (`first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L256)).

**Height differentiation lowers join order.** Proved result. Differentiating all pieces in the height coordinate lowers the height matching order from b to b−1 when b ≥ 1 and leaves the radial matching order a unchanged. (`second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L265)).

**The selected tensor-piece function.** Definition. The tensor-piece function selects its piece using the two breakpoint counts and evaluates that polynomial at the coordinate pair. (`spl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L274)).

**Joined pieces give a continuous function.** Proved result. On strictly ordered radial and height breakpoint lists, polynomial pieces satisfying the joining conditions define a continuous function of both coordinates. (`spl_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L277)).

**First-order joins give a derivative.** Proved result. First-order joins in both coordinates make the tensor spline differentiable with the derivative of its selected polynomial piece. (`spl_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L300)).

**Regularity from spline joining orders.** Proved result. A tensor spline is Cⁿ when its strictly ordered pieces match derivatives through at least order n in both variables. (`spl_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L337)).

**Interior breakpoint lists preserve order.** Proved result. Removing the two endpoints from a strictly increasing breakpoint list preserves strict order, leaves one fewer interior breakpoint than cells and shifts every remaining index by one. (`inner_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L351)).

**Spline joins give tensor-piece joins.** Proved result. A spline with matching orders (a,b) satisfies the same polynomial-piece joining conditions on the lists of interior radial and height breakpoints. (`joins_of_joined`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L369)).

**Joining orders give spline smoothness.** Proved result. A spline joined to orders a and b is continuously differentiable through order min(a,b). (`joinedSplineSmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSplineSmooth.lean#L389)).

### Breakdown.CertCell.ShapeStatements

This file states the analytic contracts required of the shape construction and records how they feed the cell layer, the given field and the actuator data. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**C¹ fields with locally Lipschitz slopes.** Proposition structure. The key regularity condition requires C¹ regularity and a Lipschitz gradient on every closed ball centered at the origin. (`IsKeyFieldSmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L17)).

**Inverse-radius decay through order two.** Proposition structure. The key decay condition bounds the value, first derivative, and totalized second derivative by inverse powers one, two, and three of one plus radius. (`IsKeyFieldDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L21)).

**The complex divergence.** Definition. Complex divergence is the sum of the three diagonal coordinate evaluations of the real Fréchet derivative. (`complexDivergence`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L25)).

**Admissibility of logarithmic phases.** Proposition definition. This proposition requires a logarithmic phase with positive base parameter to satisfy the radial-phase assumptions. (`LogPhaseIsRadial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L28)).

**C² profiles with Lipschitz curvature.** Proposition definition. This proposition requires admissible origin profiles to be C² below one and to have Lipschitz second derivatives on closed intervals strictly below that edge. (`OriginProfileSmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L31)).

**Regularity of joined splines.** Proposition definition. This proposition requires a spline joined to orders a and b to be C to order min(a,b). (`JoinedSplineSmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L35)).

**Locally Lipschitz spline gradients.** Proposition definition. This proposition requires a spline with at least first-order joins in both variables to have Lipschitz gradient on each closed ball. (`JoinedSplineGradSlopeBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L39)).

**Classical derivatives of joined splines.** Proposition definition. This proposition identifies each coordinate derivative with its derivative spline and reduces the corresponding joining order by one. (`SplineDerivatives`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L43)).

**Reflection of joined splines.** Proposition definition. This proposition requires reflected splines to preserve joining orders and evaluate with the selected parity sign at negated height. (`SplineReflection`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L50)).

**Conjugation of joined splines.** Proposition definition. This proposition requires conjugating a spline to preserve joining orders and conjugate its evaluated values. (`SplineConjugation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L55)).

**The laws of spline agreement.** Proposition definition. This proposition packages agreement as an equivalence compatible with reflection, conjugation, joining conditions, and evaluation on full meshes. (`SplineAgreementRules`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L59)).

**Jet splines have matching derivatives.** Proposition definition. This proposition requires valid radial and height jet axes to yield spline joining orders one less than their depths. (`JetSplineJoined`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L69)).

**Reflected jet coefficients give parity.** Proposition definition. This proposition requires reflection-fixed jet coefficients on a symmetric height axis to produce a spline agreeing with its parity reflection. (`JetReflection`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L73)).

**Conjugate reflection of jet coefficients.** Proposition definition. This proposition requires conjugate-reflection-fixed jet coefficients to produce a spline agreeing with its conjugate parity reflection. (`JetConjReflection`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L77)).

**Initial vanishing of jet splines.** Proposition definition. This proposition requires initial jet vanishing to make every first radial cell polynomial vanish on the initial edge. (`JetStartVanish`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L82)).

**Vanishing beyond the jet support edge.** Proposition definition. This proposition requires zero node and bubble coefficients beyond a breakpoint to give a spline vanishing from that breakpoint onward. (`JetSplineVanishesFrom`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L86)).

**Symmetry closure gives valid shape data.** Proposition definition. This proposition requires symmetry closure of valid given key data to yield valid time-field data. (`ClosureDataValid`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L92)).

**Type-one key regularity.** Proposition definition. This proposition requires keys with nonzero first label in valid shape data to have C¹ fields with gradients Lipschitz on closed balls. (`TypeOneKeySmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L96)).

**Type-two key regularity.** Proposition definition. This proposition requires keys with zero first label in valid shape data to have C¹ fields with gradients Lipschitz on closed balls. (`TypeTwoKeySmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L100)).

**Type-one key decay.** Proposition definition. This proposition requires valid nonzero-first-label keys to satisfy inverse-radius decay through second derivative order. (`TypeOneKeyDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L104)).

**Type-two key decay.** Proposition definition. This proposition requires valid zero-first-label keys to satisfy inverse-radius decay through second derivative order. (`TypeTwoKeyDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L108)).

**Zero divergence of key fields.** Proposition definition. This proposition requires every key field from valid shape and time-field data to have zero complex divergence. (`KeyDivergenceFree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L112)).

**Time translation of key fields.** Proposition definition. This proposition requires translating time by τ to multiply each key field by its temporal Fourier phase at τ. (`KeyTimeShift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L116)).

**Rotation covariance of key fields.** Proposition definition. This proposition requires axial rotation of the argument to rotate the vector and multiply it by the key's angular Fourier phase. (`KeyRotation`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L121)).

**Reflection covariance of key fields.** Proposition definition. This proposition requires a reflected key at a reflected point to equal the reflected original vector. (`KeyFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L127)).

**Conjugation of key fields.** Proposition definition. This proposition requires negating a key to conjugate its field componentwise. (`KeyConjugate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L131)).

**Joint regularity and time periodicity.** Proposition definition. This proposition requires joint C¹ regularity and time periodicity of the shape field together with almost-everywhere strong measurability and time periodicity of its Hessian. (`FieldJointSmooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L135)).

**Zero divergence of the shape field.** Proposition definition. This proposition requires the assembled shape field to have zero divergence at every time and point. (`FieldDivergenceFree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L140)).

**The weak Hessian of the shape field.** Proposition definition. This proposition requires each column of the shape gradient to have the corresponding Hessian column as its weak gradient. (`FieldWeakHessian`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L144)).

**Uniform decay of the shape field.** Proposition definition. This proposition requires one time-uniform constant to bound the shape field, gradient, and Hessian with inverse-radius powers one, two, and three. (`FieldDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L149)).

**Symmetry invariance of shape fields.** Proposition definition. This proposition requires reflection symmetry and the two coupled time-rotation symmetries determined by the azimuthal order. (`FieldClassInvariant`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L154)).

**Flip covariance of the shape Hessian.** Proposition definition. This proposition requires reflecting the point and both Hessian directions to reflect the Hessian output. (`FieldHessFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L162)).

**Velocity modes of the shape field.** Proposition definition. This proposition identifies each shape velocity mode with the sum of key fields carrying that harmonic label. (`FieldModeFormula`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L166)).

**Finite harmonic expansion of shapes.** Proposition definition. This proposition requires the field and Hessian to admit a finite harmonic expansion over any negation-closed set covering the supplied harmonics. (`FieldHarmonicExpansion`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L170)).

**Compact spatial support of shape fields.** Proposition definition. This proposition requires compact time-field data to give a spatial support radius uniform in time. (`CompactFieldSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L175)).

**Actuator shape requirements.** Proposition definition. This proposition requires compact valid shape data to satisfy the actuator's shape and label conditions. (`ActuatorShape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L179)).

**The shape-analysis requirements.** Proposition structure. The shape-analysis package collects the phase, profile, spline, jet, key-field, symmetry, harmonic, support, and actuator requirements. (`ShapeParts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L183)).

**Weak Hessians from shape contracts.** Proved result. The shape-analysis assumptions supply a weak Hessian state with a uniform decay constant for valid shape data. (`weakHessianState_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L218)).

**Shape contracts give flip invariance.** Proved result. The shape-analysis assumptions imply reflection covariance of both the shape field and its Hessian. (`flipModel_of_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L225)).

**Shape entries matching the cell data.** Proposition structure. A valid shape entry identifies the model and actuators with the cell layer's fields, Hessians, azimuthal order, and harmonic labels. (`IsGivenShapeEntry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L230)).

**Shape facts needed by cell assembly.** Proposition structure. The layer shape package records actuator shape conditions, a reflection-invariant weak Hessian model, and a finite harmonic expansion spanning the model field. (`LayerShapeFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L245)).

**Shape entries establish assembly facts.** Proved result. A valid shape entry and the shape-analysis assumptions supply the model and actuator facts required by cell-layer assembly. (`layerShapeFacts_of_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L254)).

**Shape entries determine velocity modes.** Proved result. A valid shape entry identifies each model velocity mode with the sum of key fields carrying that harmonic label. (`givenModeFormula_of_entry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L271)).

**Valid data from symmetry closure.** Proved result. The shape-analysis assumptions make the symmetry closure of valid given keys into valid time-field data. (`givenData_valid_of_closure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeStatements.lean#L278)).

### Breakdown.CertCell.ShapeSupport

This file states the explicit physical support radius obtained from a compactified radial edge and connects it with cell support coverage. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**The physical support radius.** Proposition definition. This proposition requires compact shape data with support edge t to vanish beyond the physical radius L t/(1−t), where L is the chart length. (`CompactFieldSupportRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupport.lean#L15)).

**Shape support is in the cell region.** Proved result. Shape support lies within the cell region. (`actuatorSupportInCells_of_shape`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupport.lean#L19)).

### Breakdown.CertCell.ShapeSupportRadius

This file proves that a compactly supported spline has zero reduced components beyond its edge and converts that chart edge into a physical support radius. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Earlier interior breaks form a sublist.** Proved result. If a breakpoint list has an entry beyond position k, its first k entries after the initial endpoint occur among its interior breakpoints. (`take_prefix_inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L15)).

**Earlier breaks precede the chosen cell.** Proved result. Earlier break indices precede cell indices. (`index_le_cellIndex`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L20)).

**Ordering of later defaulted breaks.** Proved result. Later defaulted breaks remain above a break. (`break_le_getD`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L40)).

**Zero spline values beyond support.** Proved result. Spline values vanish beyond the support edge. (`evalHalf_zero_beyond`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L52)).

**Derivatives vanish on a zero tail.** Proved result. If a complex-valued function vanishes for every s > c, then its derivative is zero at every t > c. (`deriv_zero_near`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L70)).

**The zero function has zero derivative.** Proved result. A function that is identically zero on R has derivative zero at every real argument. (`deriv_zero_everywhere`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L76)).

**Zero type-one values beyond support.** Proved result. Type-one components vanish beyond support. (`reducedComps_radialPolar_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L81)).

**Zero type-two values beyond support.** Proved result. Type-two components vanish beyond support. (`reducedComps_streamSwirl_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L95)).

**Passing the support edge in the chart.** Proved result. Physical radius beyond the edge gives t>tb. (`edge_lt_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L110)).

**Key components vanish beyond the edge.** Proved result. For compactly supported amplitude data whose support edge tᵦ is a mesh breakpoint, all three reduced components of every selected mode vanish whenever t > tᵦ. (`reducedComps_zero_past_edge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L119)).

**Validity of the physical support radius.** Proved result. Compact shape data with an edge breakpoint vanish beyond the radius obtained by inverting the compactifying chart. (`compactFieldSupportRadius_holds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeSupportRadius.lean#L136)).

### Breakdown.CertCell.ShapeTypeOneDecay

This file develops quantitative calculus for far-field bounds and proves inverse-radius decay of a type-one key field and its first two derivatives. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**A Lipschitz bound on a set.** Proposition definition. A slope bound on a set bounds each value difference by the constant times the distance between the two points. (`SlopeBoundOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L26)).

**Unit-ball value and derivative bounds.** Proposition definition. Unit-ball data require differentiability, a value bound, a derivative bound, and a Lipschitz bound for the derivative on the ball. (`BallData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L29)).

**Decay orders controlling two derivatives.** Proposition definition. Far decay of order a requires unit-ball value, derivative, and gradient-Lipschitz bounds with successive inverse-radius orders a, a+1, and a+2 beyond one fixed radius. (`FarDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L33)).

**Derivative bounds imply Lipschitz bounds.** Proved result. Differentiability and a derivative norm bound K throughout a ball imply a Lipschitz bound K throughout that ball. (`slopeBoundOn_of_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L37)).

**Equality transports Lipschitz bounds.** Proved result. Functions agreeing on a set share any Lipschitz constant valid for one of them on that set. (`slopeBoundOn_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L42)).

**Lipschitz bounds may be enlarged.** Proved result. A Lipschitz estimate remains valid after increasing its constant. (`slopeBoundOn_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L46)).

**Lipschitz bounds add.** Proved result. The sum of two functions with Lipschitz constants K₁ and K₂ on the same set has constant K₁+K₂ there. (`slopeBoundOn_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L49)).

**Rank-one operator norms multiply.** Proved result. For a bounded scalar-valued linear functional c and vector v, the rank-one map w ↦ c(w)v has operator norm at most ‖c‖‖v‖. (`norm_smulRight_le'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L57)).

**Ball bounds may be enlarged.** Proved result. Unit-ball value, derivative, and derivative-Lipschitz bounds remain valid when each of their three constants is increased. (`ballData_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L65)).

**Ball bounds add.** Proved result. Adding two fields adds their unit-ball value, derivative, and derivative-Lipschitz constants. (`ballData_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L69)).

**Zero derivative bounds for constants.** Proved result. A constant field has unit-ball value bound equal to its norm and zero derivative and derivative-Lipschitz bounds. (`ballData_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L79)).

**Pairing fields adds their ball bounds.** Proved result. Pairing two real fields gives unit-ball value, derivative, and derivative-Lipschitz bounds by adding the corresponding constants. (`ballData_prod`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L82)).

**Products obey a Lipschitz bound.** Proved result. If φ and L have Lipschitz bounds k₁ and k₂ on a set and satisfy |φ| ≤ v₁ and ‖L‖ ≤ v₂ there, their product has Lipschitz bound k₁v₂+v₁k₂. (`slopeBoundOn_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L115)).

**Lipschitz bounds for rank-one maps.** Proved result. Rank-one operators obey a Lipschitz bound. (`slopeBoundOn_smulRight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L131)).

**Products of fields bounded on balls.** Proved result. Products obey the ball-bound product rule. (`ballData_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L152)).

**Ball bounds for real rank-one maps.** Proved result. Real rank-one maps obey the product bound. (`slopeBoundOn_smulRightR`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L187)).

**Sums preserve decay order.** Proved result. The sum of two fields with remote unit-ball decay of order a retains value decay a, derivative decay a+1, and derivative-Lipschitz decay a+2. (`add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L208)).

**Constants have order-zero decay.** Proved result. A constant field has bounded values and zero derivatives on all remote unit balls, giving far-decay order zero. (`const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L215)).

**Pointwise bounds from ball decay.** Proved result. Remote unit-ball decay of order a yields pointwise value, first derivative, and totalized second derivative bounds with inverse-radius powers a, a+1, and a+2. (`bounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L219)).

**Products add their decay orders.** Proved result. Multiplying a scalar field of far-decay order a by a vector field of order b gives order a+b, with one and two additional inverse-radius powers for derivative and derivative-Lipschitz bounds. (`smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L237)).

**The norm derivative is the unit covector.** Proved result. At a nonzero point, the derivative of the norm is the radial unit covector. (`norm_hasFDerivAt'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L265)).

**The norm derivative has norm one.** Proved result. The radial unit covector at a nonzero point has operator norm one. (`normMap_norm'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L280)).

**Distance between normalized directions.** Proved result. Normalized directions obey a distance bound. (`unit_sub_le'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L283)).

**Differentiate a radial composition.** Proved result. Away from zero, composing a differentiable radial profile with the norm gives the profile derivative times the radial unit covector. (`radial_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L304)).

**Spatial decay from radial derivatives.** Proved result. If a radial profile and its first two radial derivatives have successive inverse-radius orders a, a+1, and a+2 beyond a positive threshold, composition with spatial radius has the corresponding remote unit-ball bounds. (`radial_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L311)).

**Degree-zero homogeneity rescales slopes.** Proved result. For a field invariant under positive scaling, multiplying the evaluation point by a positive factor multiplies its derivative by the reciprocal factor wherever the stated derivative exists. (`hom_fderiv'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L399)).

**Decay of degree-zero homogeneous fields.** Proved result. A degree-zero homogeneous field differentiable off zero with locally Lipschitz gradient has bounded values, inverse-radius gradient bounds, and inverse-square gradient-Lipschitz bounds on remote unit balls. (`hom_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L411)).

**C² homogeneity gives order-zero decay.** Proved result. A degree-zero homogeneous field that is C² off zero has bounded values and successive inverse-radius and inverse-square derivative bounds on remote unit balls. (`hom_FD_of_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L470)).

**Ball bounds under composition.** Proved result. Composition obeys the ball-bound chain rule. (`ballData_comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L481)).

**C¹ functions with Lipschitz gradients.** Proposition definition. The slope regularity condition requires C¹ regularity and a locally Lipschitz gradient. (`SlopeRegular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L521)).

**Pairs preserve order-zero decay.** Proved result. Pairing two real fields with bounded remote values and inverse-radius and inverse-square derivative bounds preserves those three orders. (`prod`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L523)).

**Bounded chart composition keeps decay.** Proved result. Composing a C¹ chart function with locally Lipschitz gradient with an order-zero decaying map into the closed unit ball preserves bounded values and the first two inverse-radius derivative orders. (`comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L530)).

**Local Lipschitz bounds for bilinear maps.** Proved result. A continuous bilinear map applied to two locally Lipschitz functions is locally Lipschitz. (`locSlopeBound_bilin'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L571)).

**C² implies locally Lipschitz gradients.** Proved result. A C² function G on R² is C¹ and its derivative is locally Lipschitz. (`of_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L626)).

**Sums preserve gradient regularity.** Proved result. The sum of two C¹ functions with locally Lipschitz gradients has the same regularity. (`add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L629)).

**Products preserve gradient regularity.** Proved result. The product of two complex C¹ functions with locally Lipschitz gradients has the same regularity. (`mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L637)).

**Joined splines have gradient regularity.** Proved result. A spline joined to at least first order in both variables is C¹ with locally Lipschitz gradient. (`spline`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L648)).

**Positive scaling fixes normalized height.** Proved result. For every positive s, scaling y to sy leaves the normalized height y₃/|y| unchanged. (`heightRatio_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L661)).

**Scaling fixes normalized coordinates.** Proved result. Positive scaling fixes normalized coordinates. (`coord_div_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L668)).

**Positive scaling fixes the point angle.** Proved result. For every positive s, scaling y to sy leaves the horizontal polar angle unchanged, including the convention on the axis. (`pointAngle_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L674)).

**Normalized coordinates are C² off zero.** Proved result. Each normalized Cartesian coordinate yⱼ/|y| is C² in a neighborhood of every nonzero point. (`coord_div_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L681)).

**Complex embedding keeps C² regularity.** Proved result. A real C² function at a point remains C² there after complex embedding. (`ofReal_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L687)).

**Positive scaling fixes the polar frame.** Proved result. Positive spatial scaling leaves the polar frame vector (y₃/|y|²)y−e₃ unchanged. (`polarVecQ_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L691)).

**Scaling fixes the azimuthal frame.** Proved result. Positive scaling fixes the azimuthal frame. (`azimVecQ_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L700)).

**Normalized height is C² off zero.** Proved result. The normalized height y ↦ y₃/|y| is C² away from the origin. (`heightRatio_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L706)).

**Normalized height has order-zero decay.** Proved result. Normalized height has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`heightRatio_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L709)).

**The complex radial frame.** Definition. The complex radial frame embeds each real radial-vector component into the complex numbers. (`radialC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L712)).

**The complex polar frame.** Definition. The complex polar frame embeds each real scaled polar-vector component into the complex numbers. (`polarC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L714)).

**The complex azimuthal frame.** Definition. The complex azimuthal frame embeds each real scaled azimuthal-vector component into the complex numbers. (`azimC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L716)).

**The radial frame has order-zero decay.** Proved result. The complex radial frame has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`radialC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L718)).

**The polar frame has order-zero decay.** Proved result. The complex polar frame has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`polarC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L725)).

**The azimuthal frame has order-zero decay.** Proved result. The complex azimuthal frame has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`azimC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L739)).

**The axis-regularized angular wave.** Definition. The regularized angular wave multiplies the integer angular exponential by the axis-vanishing factor at normalized height. (`angularC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L751)).

**Angular waves have order-zero decay.** Proved result. The axis-regularized integer angular wave has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`angularC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L754)).

**The shifted reciprocal derivative.** Proved result. Away from a zero shifted denominator, the derivative of its reciprocal is minus its reciprocal square. (`invShift_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L759)).

**The shifted reciprocal-square derivative.** Proved result. Away from a zero shifted denominator, the derivative of its reciprocal square is minus twice its reciprocal cube. (`invShift_sq_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L764)).

**Reciprocal bounds under positive shifts.** Proved result. For positive radius and shift, every natural power of the shifted reciprocal is at most the same power of the unshifted reciprocal. (`invShift_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L769)).

**The radial tail has inverse-radius decay.** Proved result. For positive chart length, the complex chart tail has value, derivative, and derivative-Lipschitz bounds C/r, C/r², and C/r³ on unit balls centered at sufficiently large radius r. (`tailC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L773)).

**Compactified radius has order-zero decay.** Proved result. For positive chart length, compactified radius has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`chartC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L799)).

**Admissible phases have three derivatives.** Proved result. For an admissible radial phase Φ and s > 0, Φ, Φ′ and Φ″ are differentiable at s with derivatives Φ′(s), Φ″(s) and Φ‴(s), respectively. (`phase_derivs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L835)).

**An absolute-value product bound.** Proved result. If x = aw, |a| ≤ M and w ≥ 0, then |x| ≤ Mw. (`abs_le_of_eq_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L859)).

**The square function has derivative 2r.** Proved result. For every real r, the derivative of the function r ↦ r² is 2r. (`sq_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L863)).

**Squared arguments obey the chain rule.** Proved result. If g has derivative g′ at r², then x ↦ g(x²) has derivative 2rg′ at r. (`comp_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L866)).

**Two summands obey the triangle bound.** Proved result. For real a,b,c,d, the bound |ca+db| ≤ |c||a|+|d||b| holds. (`abs_lin2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L870)).

**Three summands obey the triangle bound.** Proved result. For real a,b,e,c,d,f, the bound |ca+db+fe| ≤ |c||a|+|d||b|+|f||e| holds. (`abs_lin3`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L873)).

**Decay bounds for radial oscillations.** Proved result. The exponential of an admissible radial phase has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`phaseC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L876)).

**Radial phase slopes have order-0 decay.** Proved result. Twice squared radius times the derivative of an admissible radial phase has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`slopeC_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L949)).

**The radial polynomial weight.** Definition. The radial polynomial weight is t to the low order times (1−t) to the tail order, embedded in the complex numbers. (`weightLow`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1007)).

**The derivative of the radial weight.** Definition. The polynomial-weight derivative is the product-rule sum for t to the low order times (1−t) to the high order. (`weightDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1009)).

**The polynomial-weight product rule.** Proved result. Differentiating t to the low order times (1−t) to the high order gives the two product-rule terms stored in the weight derivative. (`wR_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1012)).

**Joined splines have radial derivatives.** Proved result. For joins of at least first order in both variables, the radial derivative at every real coordinate pair is the radial derivative spline evaluated at that pair. (`spline_t_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1018)).

**Joined splines have height derivatives.** Proved result. For joins of at least first order in both variables, the height derivative at every real coordinate pair is the height derivative spline evaluated at that pair. (`spline_x_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1029)).

**C² real data give regular complex data.** Proved result. Embedding a real C² function into the complex numbers gives a C¹ function with locally Lipschitz gradient. (`realC_reg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1040)).

**Constant complex data are regular.** Proved result. A constant complex function is C¹ and has a locally Lipschitz zero gradient. (`const_reg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1043)).

**Regular gradients of polynomial weights.** Proved result. The polynomial radial weight viewed as a two-variable function is C¹ with locally Lipschitz gradient. (`vT_reg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1045)).

**The weighted radial amplitude.** Definition. The weighted radial amplitude multiplies the radial spline value by the radial polynomial weight. (`radialPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1048)).

**The weighted polar amplitude.** Definition. The weighted polar amplitude multiplies the polar spline value by the radial polynomial weight. (`polarPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1050)).

**Azimuthal amplitude without phase slope.** Definition. The phase-free azimuthal amplitude combines radial differentiation and weighted polar-height differentiation, multiplied by i over the angular frequency. (`azimPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1052)).

**The phase-slope azimuthal amplitude.** Definition. The phase-slope azimuthal amplitude multiplies the weighted radial spline by the phase label and the factor i squared over angular frequency. (`azimSlopePart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1059)).

**Regularity of four key amplitudes.** Proved result. The radial, polar, azimuthal, and phase-slope amplitudes are C¹ with locally Lipschitz gradients when their radial and polar splines have the required joins. (`parts_regular`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1062)).

**The radial component exposes its tail.** Proved result. For a nonzero angular mode with high-order exponent n+1, its radial component factors as (1−x²)²(1−t) times tᵃ(1−t)ⁿ times the radial spline amplitude, where a is the low-order exponent. (`R0_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1081)).

**The polar component exposes its tail.** Proved result. For a nonzero angular mode with high-order exponent n+1, its polar component factors as (1−x²)²(1−t) times tᵃ(1−t)ⁿ times the polar spline amplitude. (`R1_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1090)).

**The azimuthal component exposes its tail.** Proved result. For a nonzero angular mode with high-order exponent n+1 and radial and polar joining orders (2,1) and (1,2), the azimuthal component factors out (1−x²)²(1−t), leaving the spline derivative contribution plus the radial phase slope times its phase contribution. (`R2_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1099)).

**Normalized height is at most one.** Proved result. Normalized height has absolute value at most 1. (`abs_heightRatio_le'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1134)).

**Compactified radius and its tail.** Proved result. Compactified radius is one minus the tail. (`chartCoord_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1146)).

**Chart tail equals the reciprocal tail.** Proved result. For positive chart length L, the chart tail is L divided by physical radius plus L. (`one_sub_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1153)).

**Chart and physical phase slopes agree.** Proved result. For positive chart length, the chart phase slope equals twice squared physical radius times the radial phase derivative there. (`phaseSlope_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1157)).

**The full phase splits into three factors.** Proved result. The oscillatory phase equals the product of exp(2πikσ), exp(inθ(y)) and exp(ijβ(|y|²)), separating temporal, angular and radial dependence. (`keyPhase_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1168)).

**The chart pair has order-zero decay.** Proved result. For positive chart length, the radial-height chart pair has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`chartPair_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1178)).

**The chart pair stays in the unit ball.** Proved result. For positive chart length, the compactified radius and normalized height both have absolute value at most one at every spatial point. (`chartPair_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1188)).

**Inverse-radius decay of type-one keys.** Proved result. For valid type-one data with positive outer vanishing order and radial/polar joins (2,1) and (1,2), the key field has remote value, derivative, and gradient-Lipschitz bounds with inverse-radius powers one, two, and three. (`key_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1201)).

**Near and far control give global decay.** Proved result. C¹ regularity with gradients Lipschitz on closed balls combines with remote decay of order one to give global value and derivative bounds by C/(1+r), C/(1+r)², and C/(1+r)³. (`decay_of_farDecay`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1234)).

**Type-one decay from regularity.** Proved result. Type-one key regularity implies global inverse-radius decay of the field and its first two totalized derivatives with powers one, two, and three. (`typeOneKeyDecay_of_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneDecay.lean#L1282)).

### Breakdown.CertCell.ShapeTypeOneOff

This file proves C¹ regularity and local Lipschitz control of the type-one gradient on the punctured space, using the angular regularization factor. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Gradient regularity away from zero.** Proposition definition. Punctured gradient regularity requires C¹ regularity and a locally Lipschitz gradient on the complement of the origin. (`OffSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L19)).

**The punctured space is a neighborhood.** Proved result. Every nonzero point has a neighborhood contained in R³ with the origin removed. (`off_nhds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L22)).

**Punctured space means nonzero points.** Proved result. Removing the singleton {0} from R³ gives exactly the set of nonzero vectors. (`off_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L25)).

**C¹ gives local Lipschitz continuity.** Proved result. C¹ regularity on the punctured space gives local Lipschitz continuity on that same domain. (`locSlopeBound_of_c1`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L29)).

**C² gives gradient control off zero.** Proved result. C² regularity on punctured space gives C¹ regularity there with a locally Lipschitz gradient. (`offSlope_of_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L35)).

**Equality keeps local Lipschitz bounds.** Proved result. Equality on punctured space transfers local Lipschitz continuity from one function to the other. (`locSlopeBound_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L43)).

**Lipschitz control bounds nearby values.** Proved result. For a K-Lipschitz function, moving at most unit distance within its domain increases its norm by at most K. (`norm_le_near`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L53)).

**Local Lipschitz bounds for bilinear maps.** Proved result. Applying a continuous bilinear map to two locally Lipschitz functions on punctured space preserves local Lipschitz continuity there. (`locSlopeBound_bilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L62)).

**C¹ functions differentiate off zero.** Proved result. A function that is C¹ on R³ with the origin removed is differentiable at every nonzero point. (`diff_of_c1`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L99)).

**Bilinear maps keep punctured regularity.** Proved result. A continuous bilinear combination of two C¹ fields with locally Lipschitz gradients on punctured space retains that regularity. (`bilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L103)).

**Sums preserve punctured regularity.** Proved result. Adding two C¹ fields with locally Lipschitz gradients on punctured space retains that regularity. (`add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L113)).

**Differences keep punctured regularity.** Proved result. Subtracting two C¹ fields with locally Lipschitz gradients on punctured space retains that regularity. (`sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L120)).

**Products preserve punctured regularity.** Proved result. Multiplying two complex C¹ fields with locally Lipschitz gradients on punctured space retains that regularity. (`mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L127)).

**Product regularity away from zero.** Proved result. Scalar multiplication of C¹ scalar and vector fields with locally Lipschitz gradients on punctured space retains that regularity. (`smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L131)).

**Constants satisfy punctured regularity.** Proved result. A constant field is C¹ with a locally Lipschitz zero gradient on punctured space. (`const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L135)).

**Chart composition keeps gradient control.** Proved result. Composing a C¹ chart function whose gradient is Lipschitz on closed balls with a C² punctured-space chart gives a C¹ field with locally Lipschitz gradient off zero. (`plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L139)).

**Complex lifting of punctured regularity.** Proved result. Complex embedding of a real C² field on punctured space gives a C¹ field with locally Lipschitz gradient there. (`ofReal_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L165)).

**Compactified radius is C² off zero.** Proved result. For positive chart length L, the compactified radius |y|/(|y|+L) is C² away from the origin. (`chartCoord_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L168)).

**Normalized height is C² off zero.** Proved result. The normalized height y₃/|y| is C² on R³ with the origin removed. (`heightRatio_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L176)).

**Complex regularity of the frame.** Proved result. A real frame that is componentwise C³ off zero gives a complex C¹ vector field with locally Lipschitz gradient off zero. (`frame_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L180)).

**Radial oscillation is regular off zero.** Proved result. For admissible shape parameters, the radial phase exponential is C¹ with locally Lipschitz gradient away from zero. (`phase_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L186)).

**Recovering radius from the chart.** Proved result. Radius is recovered from chart coordinates. (`chartRadius_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L196)).

**Chart phase slopes equal physical slopes.** Proved result. For positive chart length, the chart phase slope equals twice squared physical radius times the radial phase derivative there. (`phaseSlope_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L207)).

**Radial phase slopes are regular off zero.** Proved result. For admissible shape parameters, the integer multiple of the chart-composed phase slope is C¹ with locally Lipschitz gradient away from zero. (`slope_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L212)).

**Polynomial weights are infinitely smooth.** Proved result. Every weight tᵃ(1−t)ᵇ with nonnegative integer exponents is smooth on the real line. (`weight_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L227)).

**Chart weights are regular off zero.** Proved result. For positive chart length, a polynomial radial weight composed with compactified radius is C¹ with locally Lipschitz gradient off zero. (`weight_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L232)).

**Weight derivative regularity off zero.** Proved result. For positive chart length, the derivative of a polynomial radial weight composed with compactified radius is C¹ with locally Lipschitz gradient off zero. (`dweight_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L236)).

**Spline composition away from zero.** Proved result. A spline joined to at least first order in both coordinates composed with two C² punctured-space charts is C¹ with locally Lipschitz gradient off zero. (`spline_off`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L242)).

**Derivatives of radial spline slices.** Proved result. With at least first-order joins in both variables, radial differentiation evaluates the radial derivative spline. (`slice_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L249)).

**Derivatives of height spline slices.** Proved result. With at least first-order joins in both variables, height differentiation evaluates the height derivative spline. (`slice_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L260)).

**Factoring the radial component.** Proved result. For a nonzero-first-label key, the radial reduced component is the axis factor times the polynomial weight and radial spline. (`radialComp_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L271)).

**Factoring the polar component.** Proved result. For a nonzero-first-label key, the polar reduced component is the axis factor times the polynomial weight and polar spline. (`polarComp_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L276)).

**Expanding the azimuthal component.** Proved result. For a nonzero-first-label key with the required spline joins, the azimuthal component is i over the angular frequency times the radial, phase, divergence, and height-slope combination. (`azimComp_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L281)).

**The full phase splits into its factors.** Proved result. The phase of a mode is the product of its temporal factor exp(2πikσ), angular factor exp(inθ) and radial factor exp(ijβ(|y|²)). (`keyPhase_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L321)).

**Type-one keys have punctured regularity.** Proved result. Under the angular C³ assumption and radial/polar joins (2,1) and (1,2), a nonzero-first-label key is C¹ with locally Lipschitz gradient on punctured space. (`keyVector_offSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L331)).

**Type-one keys are C¹ off the origin.** Proved result. If each weighted angular wave (1−x²)²exp(ikθ) is C³ away from the origin, every nonzero angular mode built from admissible shape parameters and spline data is C¹ there. (`typeOneKey_contDiffOn_off_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L369)).

**Lipschitz gradients on compact sets.** Proved result. Type-one gradients are Lipschitz on compacta. (`typeOneKey_slope_off_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L377)).

**Type-one Lipschitz gradients on annuli.** Proved result. Under the C³ regularity of weighted angular waves, the derivative of each admissible nonzero angular mode is Lipschitz on every annulus ε ≤ |y| ≤ R with ε > 0. (`typeOneKey_slope_annulus_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L387)).

**Type-one keys satisfy off-origin bounds.** Proved result. Under the angular C³ assumption, valid type-one key fields are C¹ off zero and their gradients are Lipschitz on every compact set avoiding zero. (`typeOneKey_off_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOff.lean#L407)).

### Breakdown.CertCell.ShapeTypeOneOrigin

This file factors the type-one field into a quadratic angular zero and a controlled remainder, then uses rescaling to establish regularity at the origin. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Local derivative with Lipschitz control.** Proposition definition. Local gradient control means that a differentiable field has a Lipschitz derivative throughout some positive-radius neighborhood. (`TameAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L23)).

**Local gradient control bounds values.** Proved result. A derivative that is Lipschitz on a positive ball is bounded there, makes the function Lipschitz there, and bounds its values by the center value plus the derivative bound times the radius. (`tame_bounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L27)).

**C² functions have local gradient control.** Proved result. C² regularity at a point gives a neighborhood on which the function is differentiable and its derivative is Lipschitz. (`tame_of_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L55)).

**Local bounds from global regularity.** Proved result. A globally differentiable function with locally Lipschitz derivative has a differentiable neighborhood with Lipschitz derivative around every point. (`tame_of_global`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L65)).

**Local equality keeps gradient control.** Proved result. Agreement on a neighborhood transfers differentiability with a Lipschitz derivative on a smaller neighborhood. (`tame_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L73)).

**Sums preserve local gradient control.** Proved result. Adding functions that have differentiable neighborhoods with Lipschitz derivatives preserves that local regularity. (`tame_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L83)).

**Linear maps keep local gradient control.** Proved result. Applying a continuous linear map preserves differentiability with a Lipschitz derivative on a neighborhood. (`tame_clm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L99)).

**Composition keeps local gradient control.** Proved result. Composing two functions that are differentiable with Lipschitz derivatives near the relevant points preserves that local regularity. (`tame_comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L109)).

**Products preserve local gradient control.** Proved result. Multiplying complex functions with differentiable neighborhoods and Lipschitz derivatives preserves that local regularity. (`tame_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L146)).

**Negation keeps local gradient control.** Proved result. Negating a function preserves differentiability with a Lipschitz derivative on a neighborhood. (`tame_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L181)).

**Differences keep local gradient control.** Proved result. Subtracting functions with differentiable neighborhoods and Lipschitz derivatives preserves that local regularity. (`tame_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L184)).

**Local control gives a Lipschitz region.** Proved result. A local derivative witness gives an actual neighborhood where the function is differentiable and its Fréchet derivative has one Lipschitz constant. (`tame_region`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L188)).

**Insertion into one complex coordinate.** Definition. The coordinate insertion map places a complex scalar in one chosen vector component and zero in every other component. (`unitSlot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L196)).

**Coordinate control gives vector control.** Proved result. If each of the three complex coordinates has a differentiable neighborhood with Lipschitz derivative, the assembled vector field has such a neighborhood. (`tame_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L199)).

**Local gradient bounds for joined splines.** Proved result. Under the spline regularity and gradient assumptions, a spline joined to at least first order in both coordinates has a differentiable neighborhood with Lipschitz gradient around every point. (`spline_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L208)).

**Joined splines are differentiable.** Proved result. Assuming joined-spline regularity, a spline whose pieces match through at least first order in both coordinates is differentiable everywhere on R². (`spline_diff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L220)).

**Local control of radial spline slopes.** Proved result. With radial joining order at least two and height joining order at least one, the radial spline derivative is differentiable with Lipschitz gradient on some neighborhood of every point. (`spline_tderiv_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L226)).

**Local control of height spline slopes.** Proved result. With radial joining order at least one and height joining order at least two, the height spline derivative is differentiable with Lipschitz gradient on some neighborhood of every point. (`spline_xderiv_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L237)).

**A C³ radial partial derivative is C².** Proved result. If G(t,x) is C³ on R², its radial partial derivative ∂ₜG is C² on R². (`partial_t_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L248)).

**Local bounds for differentiated products.** Proved result. The radial derivative of a product has a differentiable neighborhood with Lipschitz gradient when the first factor is C³ and the second factor and its radial derivative have that local regularity. (`tderiv_mul_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L261)).

**The chart radius is C² below one.** Proved result. The inverse compactification r(t) = Lt/(1−t) is C² at every t < 1, for any real chart length L. (`chartRadius_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L277)).

**The phase slope is C² below one.** Proved result. For admissible radial phase data, the compactified phase slope has two continuous derivatives at every t < 1. (`phaseSlope_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L282)).

**Two extra radial powers factor as t².** Proved result. The radial weight with two extra powers of t satisfies tᵃ⁺²(1−t)ᵉ = t²[tᵃ(1−t)ᵉ]. (`weightPoly_add_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L299)).

**Weighted polar powers are C³.** Proved result. For nonnegative integers a,e,k, the two-variable polynomial tᵃ(1−t)ᵉ(1−x²)ᵏ is C³ on R². (`weight_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L305)).

**Weighted polar factors are C³.** Proved result. For nonnegative integers a and e, the weighted polar factor tᵃ(1−t)ᵉ(1−x²) is C³ on R². (`weight_q_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L312)).

**Quadratic factors in type-one components.** Proved result. Type-one components contain a quadratic zero. (`typeOne_factor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L319)).

**The complex horizontal coordinate.** Definition. The complex horizontal coordinate is the first real coordinate plus i times the second. (`planeOf`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L459)).

**A degree-two angular profile.** Definition. The planar angular profile multiplies squared planar radius by the integer angular exponential. (`planeMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L461)).

**The angular profile scales quadratically.** Proved result. For integer j and s > 0, the angular function Qⱼ(w) = |w|²exp(ij arg w) satisfies Qⱼ(sw) = s²Qⱼ(w). (`planeMap_scale`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L464)).

**Plane coordinate is infinitely smooth.** Proved result. The horizontal complex coordinate y ↦ y₁+iy₂ is smooth on R³. (`planeOf_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L471)).

**Plane coordinate respects scalar action.** Proved result. For every real s and vector y, the horizontal complex coordinate of sy is s(y₁+iy₂). (`planeOf_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L478)).

**Polar factor is a normalized plane norm.** Proved result. For y ≠ 0, the polar factor satisfies 1−(y₃/|y|)² = |y₁+iy₂|²/|y|². (`one_sub_heightRatio_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L483)).

**The regular factor near the origin.** Definition. The regular origin factor combines shifted inverse-radius-square decay, the temporal and radial phase, and the three frame amplitudes in rescaled coordinates. (`nearOriginProfile`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L498)).

**Near-origin factor has gradient control.** Proved result. If every amplitude component has locally Lipschitz derivative below the chart edge, each near-origin factor is differentiable with Lipschitz derivative near every point of nonnegative radial coordinate. (`nearOriginProfile_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L507)).

**Phase exposes the quadratic plane factor.** Proved result. For admissible shape parameters and y ≠ 0, multiplying the phase by (1−x²)t²c extracts the quadratic angular factor |y₁+iy₂|²exp(inθ), leaving c exp(i(2πkσ+jβ(|y|²)))/(|y|+L)². (`keyPhase_factor`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L552)).

**The key field factors near the origin.** Proved result. If every reduced component contains the factor (1−x²)t², the spatial mode at y ≠ 0 factors into |y₁+iy₂|²exp(inθ) and a remaining function of |y| and y/|y|. (`keyVector_near_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L577)).

**The rescaled type-one key.** Definition. The rescaled type-one key multiplies the quadratic planar angular profile by the regular origin factor evaluated at scaled radius and normalized direction. (`scaledKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L597)).

**Reciprocal bound for coordinate scaling.** Proved result. The coordinate rescaling has norm at most 1/s. (`scaleT_norm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L602)).

**Quadratic scaling transfers derivatives.** Proved result. When the rescaled field is differentiable, at positive scale s and nonzero point w the quadratic scaling identity gives the field derivative as s² times the rescaled-field derivative at (s,w/s), applied with zero scale component and spatial direction divided by s. (`scaled_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L610)).

**Regularity under quadratic rescaling.** Proved result. A field vanishing at zero with a quadratic rescaling law and locally Lipschitz derivatives of its rescaled factor has zero derivative at zero, quadratic value growth, linear derivative growth, and a Lipschitz gradient on a positive ball. (`scaled_origin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L628)).

**Quadratic vanishing of type-one fields.** Proved result. Type-one fields vanish quadratically at zero. (`typeOneKey_origin_bounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L751)).

**Type-one gradient regularity at zero.** Proved result. Under the spline assumptions, a valid type-one key field is differentiable at zero and its gradient is Lipschitz on some positive closed ball around zero. (`typeOneKey_origin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneOrigin.lean#L803)).

### Breakdown.CertCell.ShapeTypeOneSmooth

This file glues the origin and punctured-space estimates to obtain C¹ key fields whose gradients are Lipschitz on every closed ball. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Origin and punctured regularity give C¹.** Proved result. C¹ regularity off zero, differentiability at zero, and a Lipschitz gradient on a positive closed ball imply global C¹ regularity. (`contDiff_one_of_off_origin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneSmooth.lean#L13)).

**Separated points give a distance bound.** Proved result. If |x| < δ/2, |y| > δ > 0 and both ‖g(x)‖ and ‖g(y)‖ are at most M, then dist(g(x),g(y)) ≤ (4M/δ)dist(x,y). (`dist_le_of_far`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneSmooth.lean#L30)).

**Local and exterior slope bounds combine.** Proved result. A continuous map Lipschitz on compact sets avoiding zero and on one positive ball is Lipschitz on every closed ball centered at zero. (`slope_bound_of_off_origin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneSmooth.lean#L50)).

**Joining origin and punctured regularity.** Proved result. Punctured C¹ regularity, Lipschitz gradient bounds on compact sets off zero, differentiability at zero, and one origin gradient bound imply C¹ key regularity with a Lipschitz gradient on every closed ball. (`isKeyFieldSmooth_of_off_origin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneSmooth.lean#L100)).

**Type-one regularity by gluing.** Proved result. The type-one origin and punctured-space estimates combine to make every valid type-one key C¹ with gradients Lipschitz on closed balls. (`typeOneKeySmooth_of_off_origin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeOneSmooth.lean#L111)).

### Breakdown.CertCell.ShapeTypeTwoDecay

This file combines bounded-region estimates with type-two far-field estimates to obtain global inverse-radius decay. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Near and far bounds give weighted decay.** Proved result. C¹ key regularity and an order-one far-field bound give global inverse-radius bounds of orders one, two, and three for the value and first two totalized derivatives. (`bound_near_or_far`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecay.lean#L13)).

**Type-two decay from regularity.** Proved result. Type-two key regularity combines with its far-field estimate to give global inverse-radius bounds of orders one, two, and three. (`typeTwoKeyDecay_of_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecay.lean#L37)).

### Breakdown.CertCell.ShapeTypeTwoDecayBall

This file develops the product, composition and comparison rules for quantitative bounds on a field and its gradient on unit balls. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**A Lipschitz bound on a set.** Proposition definition. The slope condition bounds value differences on the set by a constant times distance. (`SlopeOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L18)).

**Derivative bounds give a Lipschitz bound.** Proved result. A derivative norm bound K throughout a ball gives the same K as a Lipschitz constant for the function on that ball. (`slopeOn_of_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L21)).

**Lipschitz constants may be enlarged.** Proved result. A Lipschitz bound K on a set remains valid after replacing K by any larger real constant K′. (`mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L26)).

**Lipschitz constants add.** Proved result. If f and g have Lipschitz bounds K₁ and K₂ on the same set, f+g has Lipschitz bound K₁+K₂ there. (`add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L30)).

**Equality preserves Lipschitz bounds.** Proved result. Functions agreeing on a set share any Lipschitz bound valid there. (`congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L36)).

**Bilinear products obey a slope bound.** Proved result. For a bilinear map satisfying ‖B(u,v)‖ ≤ ‖u‖‖v‖, fields with Lipschitz bounds K₁,K₂ and size bounds M₁,M₂ yield a product B(f,g) with Lipschitz bound K₁M₂+M₁K₂. (`bilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L41)).

**Bounds on a field and its derivative.** Proposition structure. The unit-ball package stores differentiability, value and derivative bounds, and a Lipschitz bound for the derivative. (`BallBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L60)).

**Ball bounds may be enlarged.** Proved result. Increasing the value, derivative, and derivative-Lipschitz constants preserves a unit-ball bound. (`mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L66)).

**Ball bounds add.** Proved result. Adding two fields adds their unit-ball value, derivative, and derivative-Lipschitz constants. (`add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L70)).

**Negation preserves ball bounds.** Proved result. Negating a field preserves its unit-ball value, derivative, and derivative-Lipschitz bounds. (`neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L79)).

**Bilinear products obey ball bounds.** Proved result. A norm-one bilinear combination has unit-ball bounds v₁v₂ for values, v₁d₂+d₁v₂ for derivatives, and 2d₁d₂+v₁l₂+l₁v₂ for derivative Lipschitz constants. (`bilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L87)).

**Pairing fields adds ball bounds.** Proved result. Pairing two real fields adds their corresponding unit-ball value, derivative, and derivative-Lipschitz constants. (`pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L120)).

**Ball bounds under composition.** Proved result. Composition with an outer function bounded by c₀ whose derivative is bounded by c₁ and c₂-Lipschitz gives ball bounds c₀, c₁d, and c₂d²+c₁l. (`comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L142)).

**Local equality preserves ball bounds.** Proved result. Equality on an open neighborhood containing a unit ball transfers the value, derivative, and derivative-Lipschitz bounds on that ball. (`congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L166)).

**Far-field bounds through two derivatives.** Proposition definition. A far-field bound of order a requires successive inverse-radius bounds of orders a, a+1, and a+2 on unit balls centered beyond one radius. (`FarBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L178)).

**Nearby points have comparable radii.** Proved result. If |z−y| < 1, then |y|−1 < |z| < |y|+1. (`ball_norm_near`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L182)).

**Reciprocal bounds at comparable radii.** Proved result. If s is at least r/2 with positive r and nonnegative C, then C/sᵏ is at most 2ᵏC/rᵏ. (`pow_div_le_of_half`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L189)).

**Sums preserve far-field bounds.** Proved result. Adding two fields of far-field order a preserves the value order a and the derivative orders a+1 and a+2. (`add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L195)).

**Negation preserves far-field bounds.** Proved result. Negation preserves all three value, derivative, and derivative-Lipschitz far-field bounds. (`neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L203)).

**Bilinear products add decay orders.** Proved result. A bounded bilinear combination adds far-field value decay orders and retains the successive extra inverse-radius powers for its derivatives. (`bilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L207)).

**A decay order can be weakened.** Proved result. A far-field bound of higher natural decay order implies any lower decay order. (`degree_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L234)).

**Constants have order-zero far bounds.** Proved result. A constant field has bounded remote values and zero derivative and derivative-Lipschitz constants. (`farBound_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L240)).

**Eventual equality preserves far bounds.** Proved result. Fields agreeing beyond some radius share their far-field value, derivative, and derivative-Lipschitz order. (`congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L249)).

**Three tail bounds from order-one decay.** Proved result. Order-one far-field bounds give pointwise inverse-radius, inverse-square, and inverse-cube estimates for the value and first two totalized derivatives. (`bounds_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayBall.lean#L259)).

### Breakdown.CertCell.ShapeTypeTwoDecayChart

This file applies the far-field calculus to compactified coordinates, spherical frames and regular chart functions. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Pairs preserve order-zero far bounds.** Proved result. Pairing two real fields with bounded remote values and derivative orders one and two preserves those three bounds. (`pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L17)).

**Products add far-field decay orders.** Proved result. Multiplying scalar fields adds their far-field value orders and the corresponding derivative decay orders. (`mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L24)).

**Decay orders add under scalar products.** Proved result. Multiplying a scalar and a vector field adds their far-field value orders and the corresponding derivative decay orders. (`smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L29)).

**Larger powers improve reciprocal decay.** Proved result. For radius at least one, nonnegative shift and coefficient, and k≥m, c/(r+L)ᵏ is at most c/rᵐ. (`div_add_pow_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L34)).

**The radial formula for chart tails.** Proved result. For positive chart length L, one minus the compactified radius equals L divided by physical radius plus L. (`one_sub_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L39)).

**Compactified radius has order-0 bounds.** Proved result. For positive chart length, compactified radius has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`farBound_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L46)).

**The chart tail decays as inverse radius.** Proved result. For positive chart length, one minus compactified radius has value, derivative, and derivative-Lipschitz bounds C/r, C/r², and C/r³ on unit balls centered at sufficiently large radius r. (`farBound_weight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L79)).

**Positive scaling fixes normalized height.** Proved result. For every positive scale s, the normalized height of sy equals that of y. (`heightRatio_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L115)).

**Positive scaling fixes coordinate ratios.** Proved result. For s > 0, each normalized Cartesian coordinate satisfies (sy)ⱼ/|sy| = yⱼ/|y|. (`coord_div_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L119)).

**Coordinate ratios are C² off zero.** Proved result. For every Cartesian component j, the function y ↦ yⱼ/|y| is C² at every nonzero point. (`coord_div_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L123)).

**Normalized height is C² off zero.** Proved result. The normalized height y ↦ y₃/|y| has two continuous derivatives away from the origin. (`heightRatio_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L127)).

**Normalized height is at most one.** Proved result. Normalized height has absolute value at most 1. (`abs_heightRatio_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L130)).

**Normalized height has order-zero bounds.** Proved result. Normalized height has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`farBound_heightRatio`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L134)).

**Chart composition preserves far bounds.** Proved result. A C¹ chart function with Lipschitz gradient on the closed unit ball, composed with positive-length compactified radius and normalized height, has bounded remote values and derivative decay orders one and two. (`farBound_chart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L137)).

**C² chart functions have order-0 bounds.** Proved result. A C² chart function composed with positive-length compactified radius and normalized height has bounded remote values and derivative decay orders one and two. (`farBound_chart_smooth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L147)).

**The radial frame has order-zero bounds.** Proved result. The radial frame has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`farBound_radialFrame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L151)).

**Positive scaling fixes the polar frame.** Proved result. For s > 0, the polar frame vector evaluated at sy equals the polar frame vector at y. (`polarVecQ_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L159)).

**The polar frame has order-zero bounds.** Proved result. The polar frame has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`farBound_polarFrame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L172)).

**Scaling fixes the azimuthal frame.** Proved result. Positive scaling fixes the azimuthal frame. (`azimVecQ_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L187)).

**Azimuthal frame has order-zero bounds.** Proved result. The azimuthal frame has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`farBound_azimFrame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayChart.lean#L195)).

### Breakdown.CertCell.ShapeTypeTwoDecayKey

This file uses the polynomial form of the origin profile near the outer chart edge to complete the type-two key decay estimate. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Joined spline charts have order-0 bounds.** Proved result. For positive chart length, composing a spline with joins of at least first order in both coordinates with the radial-height chart gives bounded remote values and derivative decay orders one and two. (`farBound_spline`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayKey.lean#L22)).

**Both partial derivatives of the spline.** Proved result. A spline with at least first-order joins in both variables differentiates in each variable by evaluating the corresponding derivative spline. (`spline_partials`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayKey.lean#L29)).

**Origin profile is polynomial near one.** Proved result. Every admissible origin profile agrees with a single polynomial on some interval t₀ < t < 1, where 0 ≤ t₀ < 1. (`origin_eq_poly_near_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayKey.lean#L59)).

**Large radius approaches the chart edge.** Proved result. Large physical radius gives a near-one chart. (`chartCoord_gt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayKey.lean#L68)).

**Complex embedding keeps C² regularity.** Proved result. Complex embedding of a real C² chart function preserves C² regularity. (`contDiff_ofReal_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayKey.lean#L76)).

**Type-two keys have inverse-radius decay.** Proved result. A valid type-two key has remote unit-ball bounds of inverse-radius order one for its value, order two for its derivative, and order three for derivative Lipschitz constants. (`farBound_typeTwoKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayKey.lean#L79)).

### Breakdown.CertCell.ShapeTypeTwoDecayPhase

This file controls the radial phase and its slope at infinity and removes the angular phase from a type-two key. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Weighted bounds for phase derivatives.** Proved result. An admissible radial phase has its first three derivatives at every positive argument, with u times the first, u² times the second, and u³ times the third uniformly bounded in absolute value. (`radialPhase_derivs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayPhase.lean#L15)).

**Squared arguments obey the chain rule.** Proved result. If f′ is the derivative of f at s², then the derivative of x ↦ f(x²) at s is 2sf′(s²). (`comp_sq_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayPhase.lean#L46)).

**Nonnegative factors keep absolute bounds.** Proved result. Multiplication by a nonnegative constant c turns an absolute bound |a|≤B into |ca|≤cB. (`abs_const_mul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayPhase.lean#L51)).

**Recovering physical radius from charts.** Proved result. Chart radius recovers the physical radius. (`chartRadius_chartCoord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayPhase.lean#L55)).

**The phase slope has order-zero bounds.** Proved result. For admissible shape data, the integer-weighted chart phase slope has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`farBound_phaseSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayPhase.lean#L61)).

**Type-two phases have no angular factor.** Proved result. A mode with zero angular label has phase exp(i(2πkσ+jβ(|y|²))), with no dependence on the polar angle. (`keyPhase_typeTwo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayPhase.lean#L136)).

**Type-two key phases have order-0 bounds.** Proved result. For valid zero-first-label keys, the time-radial phase has bounded values, derivative norm at most C/r, and derivative Lipschitz constant at most C/r² on unit balls centered at sufficiently large radius r. (`farBound_keyPhase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayPhase.lean#L141)).

### Breakdown.CertCell.ShapeTypeTwoDecayRadial

This file transports one-dimensional radial estimates and degree-zero homogeneity into spatial far-field derivative bounds. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Differentiate the norm off zero.** Proved result. At each nonzero point, the Fréchet derivative of the norm is the inner-product covector divided by that point’s norm. (`norm_hasFDerivAt_of_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L17)).

**The normalized covector has norm one.** Proved result. For z ≠ 0, the linear functional w ↦ (z·w)/|z| has operator norm one. (`norm_unitMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L33)).

**Distance between normalized directions.** Proved result. Normalized directions obey a distance bound. (`unit_diff_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L36)).

**Far bounds from radial derivatives.** Proved result. Radial value and first-two-derivative bounds of successive orders a, a+1, and a+2 beyond a radius at least one give the same three far-field orders after composition with spatial radius. (`farBound_radial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L56)).

**Homogeneity rescales derivatives.** Proved result. If A(sy) = A(y) for every s > 0 and A is differentiable at z/s, then DA(z) = s⁻¹DA(z/s). (`homog_fderiv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L122)).

**Degree-zero homogeneity gives far bounds.** Proved result. A C² field homogeneous of degree zero away from the origin has bounded remote values and inverse-radius and inverse-square derivative bounds. (`farBound_homog`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L134)).

**Unit-ball composition keeps far bounds.** Proved result. Composing an order-zero far-field map into the closed unit ball with a C¹ function whose gradient is Lipschitz there preserves its three far-field bounds. (`comp_unitBall`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L188)).

**Unit-ball gradient control from C².** Proved result. A C² chart function is C¹ and has a Lipschitz gradient on the closed unit ball. (`unitBall_of_contDiff_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoDecayRadial.lean#L224)).

### Breakdown.CertCell.ShapeTypeTwoOff

This file decomposes the type-two field into three explicit spherical components and proves C¹ and gradient Lipschitz bounds away from the origin. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**C¹ fields with local gradient bounds.** Proposition definition. Gradient regularity on a set means C¹ regularity there together with a locally Lipschitz Fréchet derivative. (`GradSlopeOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L21)).

**Equality keeps local Lipschitz bounds.** Proved result. Equality on a set transfers local Lipschitz continuity from one function to the other on that set. (`locSlopeBound_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L24)).

**Composition keeps local Lipschitz bounds.** Proved result. Composing locally Lipschitz functions preserves local Lipschitz continuity when the inner map sends the first domain into the second. (`locSlopeBound_comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L33)).

**Smooth composition keeps local slopes.** Proved result. Smooth composition preserves local slopes. (`locSlopeBound_comp_global`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L43)).

**Local Lipschitz bounds for bilinear maps.** Proved result. A continuous bilinear combination of locally Lipschitz functions on a set is locally Lipschitz there. (`locSlopeBound_bilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L49)).

**C¹ gives local Lipschitz control.** Proved result. A C¹ function on an open set is locally Lipschitz on that set. (`locSlopeBound_of_contDiffOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L101)).

**C² gives local gradient control.** Proved result. A C² function on an open set is C¹ there and has a locally Lipschitz gradient there. (`gradSlope_of_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L107)).

**Local equality keeps gradient control.** Proved result. Equality on an open set transfers C¹ regularity and a locally Lipschitz gradient to the equal function. (`gradSlope_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L113)).

**Sums preserve gradient control.** Proved result. Adding two C¹ functions with locally Lipschitz gradients on an open set preserves that regularity. (`gradSlope_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L119)).

**Bilinear maps preserve gradient control.** Proved result. A continuous bilinear combination of C¹ functions with locally Lipschitz gradients on an open set preserves that regularity. (`gradSlope_bilin`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L126)).

**Composition preserves gradient control.** Proved result. Composition preserves C¹ regularity and locally Lipschitz gradients on open domains when the inner map takes values in the outer domain. (`gradSlope_comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L136)).

**Products preserve gradient control.** Proved result. Pointwise multiplication preserves C¹ regularity and locally Lipschitz gradients on an open set. (`gradSlope_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L148)).

**Scalar products keep gradient control.** Proved result. Pointwise scalar multiplication preserves C¹ regularity and locally Lipschitz gradients on an open set. (`gradSlope_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L152)).

**Negation preserves gradient control.** Proved result. Negation preserves C¹ regularity and a locally Lipschitz gradient on an open set. (`gradSlope_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L157)).

**Constants have gradient control.** Proved result. A constant field is C¹ with a locally Lipschitz zero gradient on every open set. (`gradSlope_const`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L163)).

**Complex embedding keeps gradient control.** Proved result. Embedding a real-valued function into the complex numbers preserves C¹ regularity and locally Lipschitz gradient on an open set. (`gradSlope_ofReal`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L166)).

**A uniform gradient bound on compact sets.** Proved result. Compactness gives a single gradient bound. (`gradSlope_slopeBound_of_compact`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L171)).

**Restricting gradient bounds to subsets.** Proved result. Restricting to a subset preserves C¹ regularity and local Lipschitz continuity of the gradient on the restricted set. (`gradSlope_mono`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L175)).

**The open strip of chart coordinates.** Definition. The chart band consists of coordinate pairs whose first coordinate lies strictly between minus one and one. (`chartBand`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L184)).

**The chart-coordinate strip is open.** Proved result. The coordinate strip {(t,x) ∈ R² : −1 < t < 1} is open. (`chartBand_open`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L186)).

**The radial and height chart pair.** Definition. The chart pair combines compactified physical radius with normalized height. (`chartPair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L188)).

**Compactified radius is in the strip.** Proved result. Compactified radius lies in the chart strip. (`chartCoord_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L190)).

**Normalized coordinates are C² off zero.** Proved result. Each normalized Cartesian coordinate yⱼ/|y| has two continuous derivatives away from the origin. (`ratio_cdAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L199)).

**Normalized height is C² off zero.** Proved result. The normalized height y₃/|y| is C² near every nonzero spatial point. (`height_cdAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L202)).

**The polar frame is C² off zero.** Proved result. Every Cartesian component of the polar frame (y₃/|y|²)y−e₃ is C² away from the origin. (`polar_cdAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L204)).

**The azimuthal frame is C² off zero.** Proved result. Every Cartesian component of the azimuthal frame (−y₂,y₁,0)/|y| is C² away from the origin. (`azim_cdAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L211)).

**Componentwise C² fields off zero.** Proved result. Componentwise C² regularity away from zero gives C² regularity of the complex vector field on punctured space. (`vecC_cd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L217)).

**The chart pair is C² off zero.** Proved result. For positive L, the coordinate pair (|y|/(|y|+L),y₃/|y|) is C² away from the origin. (`chartPair_cd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L221)).

**Polynomial weights have every derivative.** Proved result. Every polynomial weight tᵃ(1−t)ᵇ has continuous derivatives of every order on R. (`weightPoly_cd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L229)).

**The phase slope is C² below one.** Proved result. For admissible shape parameters, the compactified radial phase slope is C² on the entire interval t < 1. (`phaseSlope_cd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L233)).

**Type-two key phases are C².** Proved result. For admissible radial phase data, the spatial phase of a zero angular mode is C² on all of R³, including the origin. (`keyPhase_cd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L245)).

**Joined splines are C¹.** Proved result. Under the joined-spline regularity assumption, joins of at least first order in both variables give a C¹ spline evaluation. (`spline_cd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L267)).

**Joined splines have gradient control.** Proved result. Under the spline regularity assumptions, a spline joined to at least first order in both variables is C¹ with locally Lipschitz gradient on any chosen subset of its coordinate plane. (`spline_gs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L271)).

**Height spline slices are differentiable.** Proved result. Assuming joined-spline regularity and matching orders at least one in both coordinates, every fixed-radial-coordinate slice of the spline is differentiable in height. (`slice_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L280)).

**Radial spline slices are differentiable.** Proved result. Assuming joined-spline regularity and matching orders at least one in both coordinates, every fixed-height slice of the spline is differentiable in the radial coordinate. (`slice_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L285)).

**Origin-profile slope regularity.** Proved result. If the origin profile is C² below one with locally Lipschitz second derivative, its first derivative is C¹ with locally Lipschitz derivative on (−1,1). (`originDeriv_gs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L292)).

**The type-two radial amplitude.** Definition. The type-two radial amplitude is the negative weighted height derivative of the polar-factor times the stream function. (`compZero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L307)).

**The type-two polar amplitude.** Definition. The type-two polar amplitude negates the weighted stream's radial scaling, phase-slope contribution, and twice its value. (`compOne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L311)).

**The type-two azimuthal amplitude.** Definition. The type-two azimuthal amplitude is the radial polynomial weight times the swirl spline. (`compTwo`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L318)).

**The radial stream derivative.** Proved result. For a zero-first-label key with the required stream joins, the radial component is the expanded weighted height derivative of the stream expression. (`reduced_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L320)).

**The polar stream derivative.** Proved result. Below the chart edge, a zero-first-label key with C² origin data has the expanded radial-scaling and phase expression as its polar component. (`reduced_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L337)).

**The weighted swirl component.** Proved result. For a zero-first-label key, the azimuthal component is the polynomial weight times the swirl spline. (`reduced_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L355)).

**The complex radial frame.** Definition. The complex radial frame embeds the real radial-vector coordinates into the complex numbers. (`radialC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L365)).

**The complex polar frame.** Definition. The complex polar frame embeds the real scaled polar-vector coordinates into the complex numbers. (`polarC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L367)).

**The complex azimuthal frame.** Definition. The complex azimuthal frame embeds the real scaled azimuthal-vector coordinates into the complex numbers. (`azimC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L369)).

**Type-two fields are a framed sum.** Proved result. Assuming the spline regularity and derivative formulas, positive chart length, a zero angular label, a stream spline joined through order two and a C² origin profile, the spatial field is its phase times the sum of the three explicitly differentiated radial, polar and azimuthal components. (`keyVector_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L371)).

**Gradient control of type-two amplitudes.** Proved result. With stream joins (2,2), swirl joins (1,1), and the origin-profile estimates, all three type-two amplitudes are C¹ with locally Lipschitz gradients on the chart band. (`amplitude_gs`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L381)).

**Type-two keys are regular off the origin.** Proved result. Under the spline and origin-profile assumptions, a valid type-two key is C¹ away from zero and its gradient is Lipschitz on every bounded annulus with positive inner radius. (`typeTwoKey_offOrigin_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOff.lean#L452)).

### Breakdown.CertCell.ShapeTypeTwoOrigin

This file separates the affine type-two behavior at the origin from a quadratic remainder and proves local regularity of the remainder after rescaling. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**The affine axis field's coordinates.** Definition. The linear axis field keeps the first two coordinates and multiplies the third by minus two. (`linS`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L20)).

**A normalized radial component.** Definition. The normalized radial component divides the selected coordinate by the vector norm. (`radC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L22)).

**A normalized polar component.** Definition. The normalized polar component uses products with normalized height in the first two coordinates and normalized height squared minus one in the third. (`polC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L24)).

**A normalized azimuthal component.** Definition. The normalized azimuthal component is the planar quarter-turn divided by total radius, with zero third coordinate. (`azC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L27)).

**The rescaled type-two remainder.** Definition. The rescaled type-two remainder combines the linear-axis correction with the scaled quadratic remainder in the normalized spherical frame. (`scaledRem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L29)).

**The linear part at the origin.** Definition. The leading origin field is the linear axis field multiplied by the negative axis coefficient divided by chart length. (`linPart`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L37)).

**A quadratic after removing linear terms.** Proved result. Removing the linear part leaves a quadratic. (`scaled_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L39)).

**A linear factor from the origin value.** Proved result. A unit origin value exposes a linear factor. (`origin_quadratic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L75)).

**The radial phase at zero angular label.** Proved result. For a zero-first-label key, the phase depends only on temporal frequency and the radial phase of squared radius. (`keyPhase_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L86)).

**The type-two key phase is C².** Proved result. For admissible shape parameters and a zero angular mode, the spatial phase is C² at every point of R³. (`keyPhase_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L92)).

**Polynomial evaluation is C².** Proved result. Evaluation of a real polynomial gives a C² function of its real argument. (`poly_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L103)).

**The profile quotient is polynomial.** Proved result. Writing Sₑ(t) = ∑ᵢ₌₀ᵉ⁻¹(1−t)ⁱ, the origin-profile quotient is the polynomial q(t)−Sₑ(t)−tSₑ(t)q(t). (`profQuot_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L106)).

**The slope quotient is C² below one.** Proved result. For admissible radial phase data, the slope quotient, regarded as a function of the radial-height pair, is C² at every pair with first coordinate below 1. (`slopeQuot_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L113)).

**Remainder components have local control.** Proved result. With stream and quotient-stream joins (2,2) and swirl-quotient joins (2,1), each remainder component has a differentiable neighborhood with Lipschitz derivative below the chart edge. (`rem_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L128)).

**The rescaled remainder has local control.** Proved result. With stream and quotient-stream joins (2,2) and swirl-quotient joins (2,1), each rescaled remainder component is differentiable with Lipschitz derivative near every point with nonnegative scaling coordinate and nonzero direction vector. (`scaledRem_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L180)).

**Type-two keys are C¹ near the origin.** Proved result. Assuming joined-spline regularity and local Lipschitz bounds for spline gradients, every admissible zero angular mode is C¹ on some ball about the origin and has a Lipschitz derivative on that ball. (`typeTwoKey_near_origin_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOrigin.lean#L236)).

### Breakdown.CertCell.ShapeTypeTwoOriginScale

This file develops local derivative bounds stable under algebra and composition, then applies quadratic rescaling to control a gradient near zero. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Local derivative with Lipschitz control.** Proposition definition. Local gradient control means that the field has a Lipschitz derivative on some positive-radius ball around the point. (`TameAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L22)).

**Local gradient control bounds values.** Proved result. A derivative that is Lipschitz on a positive ball is bounded there, makes the function Lipschitz there, and bounds its values by the center value plus the derivative bound times the radius. (`tame_bounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L26)).

**C² functions have local gradient control.** Proved result. C² regularity at a point gives a neighborhood on which the function is differentiable and its derivative is Lipschitz. (`tame_of_contDiffAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L54)).

**A Lipschitz gradient gives local control.** Proved result. A differentiable function whose gradient is Lipschitz on every centered closed ball has a differentiable neighborhood with Lipschitz derivative around each point. (`tame_of_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L64)).

**Local equality keeps gradient control.** Proved result. Agreement on a neighborhood transfers differentiability with a Lipschitz derivative on a smaller neighborhood. (`tame_congr`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L78)).

**Sums preserve local gradient control.** Proved result. Adding functions that have differentiable neighborhoods with Lipschitz derivatives preserves that local regularity. (`tame_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L88)).

**Linear maps keep local gradient control.** Proved result. Applying a continuous linear map preserves differentiability with a Lipschitz derivative on a neighborhood. (`tame_clm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L104)).

**Composition keeps local gradient control.** Proved result. Composing two functions that are differentiable with Lipschitz derivatives near the relevant points preserves that local regularity. (`tame_comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L114)).

**Products preserve local gradient control.** Proved result. Multiplying complex functions with differentiable neighborhoods and Lipschitz derivatives preserves that local regularity. (`tame_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L151)).

**Negation keeps local gradient control.** Proved result. Negating a function preserves differentiability with a Lipschitz derivative on a neighborhood. (`tame_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L186)).

**Differences keep local gradient control.** Proved result. Subtracting functions with differentiable neighborhoods and Lipschitz derivatives preserves that local regularity. (`tame_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L189)).

**Local control gives a Lipschitz region.** Proved result. A local derivative witness gives an actual neighborhood where the function is differentiable and its Fréchet derivative has one Lipschitz constant. (`tame_region`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L193)).

**Coordinate control gives vector control.** Proved result. If all three complex coordinate functions have differentiable neighborhoods with Lipschitz derivatives, the assembled vector field has that local regularity. (`tame_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L201)).

**Reciprocal bound for coordinate scaling.** Proved result. The coordinate rescaling has norm at most 1/s. (`scale_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L214)).

**Quadratic scaling transfers derivatives.** Proved result. If the rescaled field is differentiable at (s,w/s), with s positive and w nonzero, the quadratic scaling identity gives the original field derivative as s² times that derivative applied in directions (0,h/s). (`scaled_hasFDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L222)).

**Lipschitz gradients by quadratic scaling.** Proved result. Quadratic scaling gives a Lipschitz gradient. (`scaled_fderiv_slope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginScale.lean#L240)).

### Breakdown.CertCell.ShapeTypeTwoOriginSplit

This file divides initial vanishing spline pieces by the radial coordinate and separates type-two components into linear and quadratic radial terms. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Positive lower bound for finite breaks.** Proved result. Finite positive breaks have a lower bound. (`pos_lower_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L21)).

**Near zero the first cell is selected.** Proved result. For a strictly increasing breakpoint list beginning at zero, there is c > 0 such that every coordinate t < c is assigned to the first cell. (`first_cell_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L32)).

**Multiplying after first substitution.** Proved result. First substitution respects multiplication. (`atFirst_mul_X`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L46)).

**Subtracting the initial value exposes t.** Proved result. For every two-variable polynomial R, the difference R(t,x)−R(0,x) is divisible by t. (`sub_atFirst_dvd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L51)).

**Height substitution keeps the t factor.** Proved result. Height substitution preserves the t factor. (`atSecond_X0_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L71)).

**Height derivatives preserve the t factor.** Proved result. Differentiating a polynomial tq(t,x) any number of times in x preserves its factor t. (`xDeriv_X0_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L75)).

**A spline quotient from initial vanishing.** Proved result. If a joined spline vanishes identically on the edge t = 0 of every first radial cell, then near that edge it equals t times a spline with radial matching order two and the original height matching order. (`first_row_quotient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L86)).

**Joined splines are differentiable.** Proved result. Assuming joined-spline regularity, matching through at least first order in both coordinates makes the evaluated spline differentiable on R². (`spline_differentiable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L117)).

**Local gradient bounds for joined splines.** Proved result. Under the spline regularity assumptions, joins of at least first order in both coordinates give a differentiable neighborhood with Lipschitz gradient around every spline point. (`spline_tame`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L121)).

**Height derivatives of joined splines.** Proved result. A joined spline's height derivative evaluates the height derivative spline when both joining orders are at least one. (`spline_hasDerivAt_x`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L126)).

**Radial derivatives of joined splines.** Proved result. A joined spline's radial derivative evaluates the radial derivative spline when both joining orders are at least one. (`spline_hasDerivAt_t`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L137)).

**The radial tail polynomial.** Definition. The radial tail weight is (1−t) raised to its natural exponent and embedded in the complex numbers. (`wt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L148)).

**The derivative of the radial tail.** Definition. The tail derivative is minus the exponent times (1−t) raised to one lower natural exponent. (`wtDeriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L150)).

**A finite geometric tail sum.** Definition. The geometric tail is the sum of the first e powers of 1−t. (`geomTail`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L152)).

**The origin-profile quotient.** Definition. The profile quotient subtracts the geometric tail and its t-weighted product with the origin quotient from that quotient. (`profQuot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L154)).

**The radial phase-slope quotient.** Definition. The phase-slope quotient is twice the squared chart-length-over-tail factor times t and the radial phase derivative at squared physical radius. (`slopeQuot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L157)).

**The full stream amplitude.** Definition. The full stream adds the axis coefficient times the origin polynomial and height to the stream spline. (`streamFull`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L160)).

**The radial derivative of the full stream.** Definition. The radial stream derivative combines the derivative of the origin polynomial with the radial derivative spline. (`streamFullT`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L163)).

**The leading reduced components.** Definition. The leading reduced components are −α(1−3x²), −3αx, and zero. (`leadComp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L166)).

**The quadratic remainder components.** Definition. The quadratic remainder separates the profile quotient, quotient stream spline, and swirl spline after removing the leading radial-order components. (`remComp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L168)).

**Splitting components by radial order.** Proved result. Type-two components split by radial order. (`reduced_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoOriginSplit.lean#L178)).

### Breakdown.CertCell.ShapeTypeTwoSmooth

This file combines the near-origin and annular estimates to finish the type-two key regularity contract. Appendix B, the construction and regularity of shape fields used in the cell coercivity route; supporting library for the shape construction around B.6–B.8.

**Origin and punctured C¹ regularity glue.** Proved result. A function C¹ on punctured space and on one positive-radius ball around zero is globally C¹. (`contDiff_of_punctured_and_ball`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoSmooth.lean#L15)).

**Slope bounds over a finite closed cover.** Proved result. If two closed sets cover a convex set and the function is K-Lipschitz on both, it is K-Lipschitz on the convex set. (`slopeBoundOn_of_closed_cover`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoSmooth.lean#L25)).

**Ball bounds from origin and annuli.** Proved result. Lipschitz bounds on every bounded positive-inner-radius annulus and one positive origin ball give a Lipschitz bound on every centered closed ball. (`slopeBoundOn_closedBall_of_annuli_and_ball`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoSmooth.lean#L45)).

**Local pieces give key-field regularity.** Proved result. C¹ regularity and Lipschitz gradient bounds on the punctured annuli and near the origin give a globally C¹ key field whose gradient is Lipschitz on each closed ball. (`keyFieldSmooth_of_pieces`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoSmooth.lean#L66)).

**Type-two regularity from its parts.** Proved result. C¹ regularity and Lipschitz gradient bounds near the origin and on every annulus combine into type-two key regularity on closed balls. (`typeTwoKeySmooth_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ShapeTypeTwoSmooth.lean#L78)).

### Breakdown.CertCell.SideTraceMatch

This file approximates asymmetric tent functions by smooth compactly supported tests to prove equality of weak side traces. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Smooth approximation to a positive part.** Definition. The kink profile multiplies its argument by the smooth transition from zero to one. (`kinkProfile`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L18)).

**The kink profile is infinitely smooth.** Proved result. The regularized positive-part function used to construct tent tests has derivatives of every order on R. (`kinkProfile_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L20)).

**The kink profile is zero below zero.** Proved result. The regularized positive-part function has value zero for every x ≤ 0. (`kinkProfile_of_nonpos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L23)).

**The kink profile equals x above one.** Proved result. The regularized positive-part function equals x whenever x ≥ 1. (`kinkProfile_of_one_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L26)).

**The kink slope is zero below zero.** Proved result. The derivative of the regularized positive-part function is zero on the open interval x < 0. (`deriv_kinkProfile_of_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L29)).

**The kink slope is one above one.** Proved result. The derivative of the regularized positive-part function is one on the open interval x > 1. (`deriv_kinkProfile_of_one_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L35)).

**The kink slope is globally bounded.** Proved result. One real constant bounds the absolute derivative of the kink profile at every real argument. (`deriv_kinkProfile_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L41)).

**The rescaled smooth kink.** Definition. The smooth kink at width ε is ε times the base kink evaluated at the argument divided by ε. (`kinkAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L55)).

**The rescaled kink is infinitely smooth.** Proved result. For every real scale ε, the rescaled positive-part approximation is smooth as a function of its real argument. (`kinkAt_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L57)).

**Differentiating the rescaled kink.** Proved result. For positive smoothing width, the rescaled kink derivative is the profile derivative evaluated at the argument divided by that width. (`kinkAt_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L60)).

**The rescaled kink is zero below zero.** Proved result. For a positive smoothing width ε, the rescaled positive-part approximation vanishes for y ≤ 0. (`kinkAt_of_nonpos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L72)).

**Rescaled kink equals x beyond its width.** Proved result. For a positive smoothing width ε, the rescaled positive-part approximation equals y whenever y ≥ ε. (`kinkAt_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L75)).

**The rescaled kink is bounded by |x|.** Proved result. For positive smoothing width, the absolute value of the rescaled kink is at most the absolute value of its argument. (`abs_kinkAt_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L80)).

**The step function at zero.** Definition. The step function is one for positive arguments and zero otherwise. (`unitStep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L88)).

**The step function is monotone.** Proved result. The function equal to zero on the nonpositive half-line and one on the positive half-line is nondecreasing. (`unitStep_monotone`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L90)).

**Absolute bound for the step function.** Proved result. The step function has absolute value at most 1. (`abs_unitStep_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L99)).

**The positive part is bounded by |x|.** Proved result. The absolute value of the positive part of a real number is at most its absolute value. (`abs_max_zero_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L103)).

**The three-coefficient tent combination.** Definition. The tent combination uses the reciprocal left width, the negative sum of reciprocal widths, and the reciprocal right width. (`comb`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L109)).

**The tent combination has a uniform bound.** Proved result. If p < m < q and |u|,|v|,|w| ≤ K, the three-term tent combination is bounded in absolute value by 2K((m−p)⁻¹+(q−m)⁻¹). (`abs_comb_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L112)).

**A smooth approximation to a tent.** Definition. The smooth tent combines three shifted smooth kinks with the left and right reciprocal-width coefficients. (`tentApprox`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L132)).

**The piecewise linear tent function.** Definition. The piecewise linear tent uses the same three coefficients on positive parts at its left endpoint, peak, and right endpoint. (`tentFn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L135)).

**The piecewise constant tent slope.** Definition. The tent slope uses the same three coefficients on step functions at the left endpoint, peak, and right endpoint. (`tentSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L137)).

**The weak pairing with a tent function.** Definition. The weak tent pairing is the function times the tent slope plus its candidate derivative times the tent value. (`pairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L139)).

**Tent approximation is infinitely smooth.** Proved result. For any real endpoints p,m,q and smoothing scale ε, the regularized tent function is smooth on R. (`tentApprox_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L142)).

**The three-term smooth tent slope.** Proved result. The tent-approximation derivative is the same three-term linear combination of rescaled kink slopes used to build the tent. (`tentApprox_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L149)).

**Compact support of tent approximations.** Proved result. The tent approximation vanishes outside support. (`tentApprox_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L163)).

**Tent support stays in a short interval.** Proved result. For p < m < q and ε > 0, the closed support of the regularized tent lies in [p,q+ε]. (`tentApprox_tsupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L178)).

**Uniform tent-approximation slope bounds.** Proved result. For positive tent widths and smoothing width, the absolute smooth-tent derivative is at most twice the sum of reciprocal tent widths times a global kink-slope bound. (`abs_deriv_tentApprox_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L184)).

**Interval width bounds point differences.** Proved result. The distance between two points strictly inside an interval is at most its width. (`abs_sub_le_width`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L190)).

**Uniform tent-approximation value bounds.** Proved result. Tent approximations have a uniform value bound. (`abs_tentApprox_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L195)).

**Tent function has a uniform value bound.** Proved result. If a < p < m < q < b, the tent function on (a,b) is bounded in absolute value by 2((m−p)⁻¹+(q−m)⁻¹)(b−a). (`abs_tentFn_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L202)).

**The tent slope has a uniform bound.** Proved result. For p < m < q, the piecewise tent slope is bounded everywhere by 2((m−p)⁻¹+(q−m)⁻¹). (`abs_tentSlope_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L209)).

**The tent slope is measurable.** Proved result. For any real p,m,q, the piecewise slope used for the tent test is measurable on R. (`tentSlope_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L213)).

**The tent function is continuous.** Proved result. For any real p,m,q, the piecewise linear tent function is continuous on R. (`tentFn_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L222)).

**The smoothing scale is positive.** Proved result. For δ > 0 and every integer n ≥ 0, the smoothing width δ/(n+2) is strictly positive. (`seq_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L226)).

**Smoothing scale is below its upper bound.** Proved result. For δ > 0 and every integer n ≥ 0, the smoothing width δ/(n+2) is strictly less than δ. (`seq_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L228)).

**Smoothing scale eventually becomes small.** Proved result. For any real δ and every positive w, δ/(n+2) < w for all sufficiently large integers n. (`seq_eventually_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L232)).

**Smoothed kinks approach positive parts.** Proved result. Smoothed kinks eventually match positive parts. (`kinkAt_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L242)).

**Kink slopes eventually match the step.** Proved result. If δ > 0 and w ≠ 0, the derivative of the positive-part profile at w/(δ/(n+2)) eventually equals the step value at w. (`kinkSlope_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L250)).

**Tent approximations stabilize pointwise.** Proved result. Tent approximations eventually match the tent. (`tentApprox_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L259)).

**Tent slopes stabilize pointwise.** Proved result. Tent slopes eventually match the step slope. (`deriv_tentApprox_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L265)).

**The pairing vanishes to the left.** Proved result. For p < m < q, the weak pairing integrand formed from the tent and its slope vanishes at every x ≤ p. (`pairing_outer_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L272)).

**The pairing vanishes to the right.** Proved result. For p < m < q, the weak pairing integrand formed from the tent and its slope vanishes at every x > q. (`pairing_outer_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L287)).

**The lower weak tent pairing.** Proved result. On the lower side of the tent, the weak pairing is the function divided by the lower width plus its derivative times the increasing linear weight. (`pairing_lower`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L306)).

**The upper weak tent pairing.** Proved result. On the upper side of the tent, the weak pairing is the derivative times the decreasing linear weight minus the function divided by the upper width. (`pairing_upper`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L323)).

**The two weak tent pairings agree.** Proved result. If f has weak derivative f′ on an interval containing p < m < q, then the left tent integral ∫ₚᵐ[f/(m−p)+(x−p)f′/(m−p)] equals the right tent integral ∫ₘᵠ[f/(q−m)−(q−x)f′/(q−m)]. (`tent_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L345)).

**Lower side trace is an interval integral.** Proved result. For arbitrary functions f,g and o < c, the left trace expression at c is ∫ from o to c of [f(r)/(c−o)+(r−o)g(r)/(c−o)]dr. (`sideTrace_of_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L464)).

**Upper side trace is an interval integral.** Proved result. For arbitrary functions f,g and c < o, the right trace expression at c is ∫ from c to o of [f(r)/(o−c)−(o−r)g(r)/(o−c)]dr. (`sideTrace_of_gt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L470)).

**The two side traces match.** Proved result. If f has weak derivative f′ on an open interval containing c and two distinct auxiliary endpoints, the integral formula for the trace at c gives the same value using either endpoint. (`sideTraceMatch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SideTraceMatch.lean#L492)).

### Breakdown.CertCell.SixthPowerStatements

This file names the line, three-slice, three-halves and sixth-power inequalities used to derive the Sobolev estimate for weak perturbations. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Smooth sixth-power gradient inequality.** Proposition definition. The smooth sixth-power condition bounds the squared L6 norm of a compactly supported C¹ vector field by C times its gradient energy. (`SmoothSixthPowerBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerStatements.lean#L14)).

**Scalar three-halves gradient inequality.** Proposition definition. The three-halves condition bounds the L to the power 3/2 norm of a compactly supported C¹ scalar field by C times the integral of its derivative norm. (`ThreeHalvesGradientBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerStatements.lean#L18)).

**The three-slice product inequality.** Proposition definition. The three-slice condition bounds the integral of the square root of three paired-coordinate functions by the square root of their three integrals multiplied together. (`TripleSliceBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerStatements.lean#L22)).

**A line integral bounds the point value.** Proposition definition. The line-gradient condition bounds the value of a compactly supported C¹ scalar field by half the integral of its absolute derivative along any coordinate line. (`LineGradientBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerStatements.lean#L27)).

### Breakdown.CertCell.SixthPowerWeak

This file mollifies a weak field, controls its sixth power by gradient energy and passes to shrinking kernels to prove the weak Sobolev bound. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The squared matrix norm is continuous.** Proved result. The sum of the squared Cartesian entries of a linear map R³ → R³ depends continuously on that map. (`continuous_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L10)).

**The squared matrix norm is nonnegative.** Proved result. For every linear map R³ → R³, the sum of its squared Cartesian entries is nonnegative. (`matSq_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L14)).

**Averaging bounds the squared norm.** Proved result. For a nonnegative integrable weight of mass one, the squared norm of its weighted vector average is at most the weighted average of squared norms when both integrals exist. (`sq_norm_integral_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L17)).

**The sixth power lies above its tangent.** Proved result. For nonnegative r and a, convexity of the sixth power gives a⁶+6a⁵(r−a) ≤ r⁶. (`sixth_le_tangent`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L38)).

**Averaging bounds the sixth power.** Proved result. For a nonnegative integrable weight of mass one, the sixth power of its weighted vector average is at most the weighted average of sixth powers when both integrals exist. (`sixth_norm_integral_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L48)).

**Mollify the weak-gradient column.** Proved result. Each coordinate derivative of convolution with a normalized smooth bump equals convolution of that bump with the corresponding weak-gradient column. (`fderiv_convolution_column`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L78)).

**Mollified fields obey the L6 bound.** Proved result. Under the smooth Sobolev estimate, normalized bump convolution of a weak-gradient field with finite sixth-power and gradient energies has sixth-power integral at most the cube of C times the original gradient energy. (`mollified_sixthPower_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L116)).

**A sequence of shrinking smooth bumps.** Definition. The nth smoothing bump has inner radius 1/(n+2) and outer radius 2/(n+2). (`shrinkingBump`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L192)).

**Weak sixth-power gradient bound follows.** Proved result. A nonnegative-constant compactly supported C¹ Sobolev bound transfers to weak-gradient fields with finite sixth-power and gradient-energy integrals using the same constant. (`sixthPowerGradientBound_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeak.lean#L198)).

### Breakdown.CertCell.SixthPowerWeakCutoff

This file introduces large-radius cutoffs and controls their gradient error by an L6 tail, allowing the compact-support estimate to extend to global fields. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Weighted squares control a sum.** Proved result. For positive δ, the squared norm of a+b is at most (1+δ) times the squared norm of a plus (1+1/δ) times the squared norm of b. (`norm_add_sq_le_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L9)).

**A linear bound by a shifted cubic.** Proved result. For nonnegative u and positive a, u is at most a plus u cubed divided by a squared. (`le_add_cube_div_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L20)).

**A cube-root bound gives a cube bound.** Proved result. If x ≥ 0 and x¹ᐟ³ ≤ c, then x ≤ c³. (`le_cube_of_rpow_third_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L31)).

**Coordinate unit vectors have norm one.** Proved result. Each Cartesian coordinate unit vector in R³ has Euclidean norm one. (`norm_unitVector_eq_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L40)).

**The squared matrix norm is continuous.** Proved result. The sum of the squared Cartesian entries of a linear map R³ → R³ is a continuous function of its entries. (`continuous_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L43)).

**The unit-radius cutoff bump.** Definition. The unit cutoff bump has inner radius one and outer radius two. (`unitBump`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L48)).

**A smooth cutoff at radius R.** Definition. The radius-R cutoff evaluates the unit bump after scaling space by the reciprocal of R. (`cutoff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L50)).

**The radial cutoff is C¹.** Proved result. For every real scale R, the radial cutoff used in the weak Sobolev argument is C¹ on R³. (`cutoff_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L52)).

**The cutoff is nonnegative.** Proved result. The radial cutoff has a nonnegative value at every point and for every scale R. (`cutoff_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L55)).

**The cutoff is at most one.** Proved result. The radial cutoff has value at most one at every point and for every scale R. (`cutoff_le_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L57)).

**The cutoff equals one on the inner ball.** Proved result. For R > 0, the radial cutoff equals one throughout the closed ball |y| ≤ R. (`cutoff_eq_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L59)).

**Cutoff is zero outside the outer ball.** Proved result. For R > 0, the radial cutoff vanishes wherever |y| ≥ 2R. (`cutoff_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L66)).

**Cutoff derivatives use inverse scaling.** Proved result. The rescaled cutoff derivative is the unit-bump derivative at the reciprocally scaled point, precomposed with multiplication by the totalized reciprocal radius. (`fderiv_cutoff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L75)).

**The unit cutoff derivative is bounded.** Proved result. The derivative of the fixed unit cutoff has one finite norm bound valid throughout space. (`exists_fderiv_unitBump_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L82)).

**The cutoff derivative is bounded by M/R.** Proved result. At positive radius R, a global derivative bound M for the unit bump gives derivative bound M/R for its radial cutoff. (`norm_fderiv_cutoff_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L86)).

**Cutoff derivative vanishes below radius.** Proved result. For positive cutoff radius R, the cutoff derivative vanishes wherever the distance from the origin is strictly below R. (`fderiv_cutoff_eq_zero_of_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L100)).

**Cutoff derivative vanishes beyond 2R.** Proved result. For positive cutoff radius R, the cutoff derivative vanishes wherever the distance from the origin is strictly above twice R. (`fderiv_cutoff_eq_zero_of_gt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L107)).

**Cutting off gives compact support.** Proved result. For R > 0, multiplying any vector field by the radial cutoff gives a field whose closed support is compact. (`cutoff_smul_hasCompactSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L114)).

**Gradient energy of a cutoff.** Proved result. Cutting off gives a gradient energy bound. (`matSq_fderiv_cutoff_smul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L120)).

**Cutoff error has a L6 tail bound.** Proved result. The cutoff error has a sixth-power tail bound. (`integral_fderiv_cutoff_sq_mul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L157)).

**L6 bounds on balls from cutoffs.** Proved result. Ball sixth powers obey the cutoff estimate. (`setIntegral_ball_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L225)).

**Smooth L6 bound extends globally.** Proved result. The smooth sixth-power bound extends globally. (`sixthPower_le_of_contDiff_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SixthPowerWeakCutoff.lean#L284)).

### Breakdown.CertCell.SmoothSixthPower

This file applies the scalar three-halves estimate to the fourth power of a vector norm and obtains the sixth-power bound with constant 4/3. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The Frobenius norm bounds operator norm.** Proved result. The operator norm of a spatial linear map is at most the square root of the sum of squared column norms. (`opNorm_le_sqrt_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SmoothSixthPower.lean#L9)).

**The quartic norm derivative is bounded.** Proved result. The derivative norm of the fourth power of a vector norm is at most four times its norm cubed. (`norm_fderiv_quartic_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SmoothSixthPower.lean#L23)).

**The squared matrix norm is nonnegative.** Proved result. For every real 3 × 3 matrix A, the squared Frobenius norm ∑ᵢⱼAᵢⱼ² is nonnegative. (`matSq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SmoothSixthPower.lean#L33)).

**Smooth Sobolev constant is four-thirds.** Proved result. The scalar inequality ‖u‖₃ᐟ₂ ≤ (2√3)⁻¹‖∇u‖₁ for C¹ compactly supported u implies ‖w‖₆² ≤ (4/3)‖∇w‖₂² for C¹ compactly supported vector fields w. (`smoothSixthPowerBound_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/SmoothSixthPower.lean#L36)).

### Breakdown.CertCell.StretchFlip

This file tracks coordinate signs through reflection of the gradient, curl and vorticity gradient, which is needed for evenness of the stretch density. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Reflection acts by coordinate signs.** Proved result. The half-turn R acts componentwise as (Ry)ⱼ = εⱼyⱼ with signs ε = (1,−1,−1). (`flipPoint_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L13)).

**The first reflection sign is positive.** Proved result. The sign multiplying the first Cartesian component under the half-turn is +1. (`frameSign_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L16)).

**The second reflection sign is negative.** Proved result. The sign multiplying the second Cartesian component under the half-turn is −1. (`frameSign_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L18)).

**The third reflection sign is negative.** Proved result. The sign multiplying the third Cartesian component under the half-turn is −1. (`frameSign_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L20)).

**Each reflection sign squares to one.** Proved result. Each of the three half-turn signs εⱼ satisfies εⱼ² = 1. (`frameSign_mul_self`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L22)).

**Unit vectors transform by flip signs.** Proved result. Unit vectors transform by reflection signs. (`flipPoint_unitVector`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L26)).

**Alternating symbols respect flip signs.** Proved result. Alternating symbols respect reflection signs. (`sign_symbol_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L31)).

**Reflection as a continuous linear map.** Definition. The linear reflection fixes the first coordinate projection and negates the second and third coordinate projections. (`flipMap`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L35)).

**Linear flip matches point flip.** Proved result. The linear reflection matches point reflection. (`flipMap_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L40)).

**Reflect the point and derivative input.** Proved result. For a differentiable reflection-compatible field, reflecting the evaluation point and direction reflects the resulting derivative value. (`fderiv_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L43)).

**Two signs in matrix reflection.** Proved result. Reflected matrix entries acquire two signs. (`map_unit_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L56)).

**Three signs in Hessian reflection.** Proved result. Reflected Hessian entries acquire three signs. (`bilin_unit_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L61)).

**Curl is a signed coordinate sum.** Proved result. For a linear map A representing a gradient, its curl component is the signed sum (curl A)ᵢ = ∑ⱼₗ εᵢⱼₗ(Aeⱼ)ₗ. (`curlVec_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L70)).

**Curl transforms by reflection signs.** Proved result. If two gradient maps satisfy A(Ra) = R(Ba) for the half-turn R, their curls satisfy (curl A)ᵢ = εᵢ(curl B)ᵢ. (`curlVec_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L74)).

**Vorticity gradients acquire two signs.** Proved result. If Hessian maps satisfy A(Ra,Rb) = R B(a,b), their vorticity-gradient entries satisfy (∇curl A)ⱼₘ = εⱼεₘ(∇curl B)ⱼₘ. (`vortGrad_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchFlip.lean#L84)).

### Breakdown.CertCell.StretchMeanIntegral

This file proves integrability and reflection parity of the stretch form and converts its full space-time integral to the weighted half-plane average. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Reflection is an involution.** Proved result. Applying the half-turn (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃) twice returns y. (`flip_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L24)).

**Flip reverses the height coordinate.** Proved result. Reflection reverses the height coordinate. (`flip_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L28)).

**Cylindrical coordinates preserve height.** Proved result. The cylindrical coordinate map (r,z,θ) ↦ (r cos θ,r sin θ,z) has third Cartesian component z. (`cylF_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L31)).

**Meridian rotation gives cylinder points.** Proved result. Cylindrical points are rotated meridian points. (`cylF_eq_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L34)).

**The half-plane is measurable.** Proved result. The meridian quadrant {(r,z) : r > 0, z > 0} is measurable in R². (`measurableSet_halfPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L37)).

**The horizontal plane has zero volume.** Proved result. The plane {y ∈ R³ : y₃ = 0} has three-dimensional Lebesgue measure zero. (`coord_two_null`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L40)).

**Shifting a periodic angular integral.** Proved result. Periodic angular integrals can be shifted. (`lintegral_angle_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L50)).

**Flip folds the integral to a half-plane.** Proved result. Reflection folds the integral to a half-plane. (`lintegral_fold`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L64)).

**The space-time orbit map is measurable.** Proved result. The map (r,z,σ,θ) ↦ (σ,Rθ(r,0,z)) from meridian, time and angle coordinates to space-time is measurable. (`measurable_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L132)).

**Folding space-time into the half-plane.** Proved result. Space-time integration folds to the half-plane. (`lintegral_spacetime`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L141)).

**Orbit coordinates are positive a.e..** Proved result. Orbit coordinates are positive almost everywhere. (`ae_orbit_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L168)).

**Orbit coordinates preserve null sets.** Proved result. The cylindrical space-time map pulls null sets in [0,1] × R³ back to null sets in r > 0, z > 0, 0 < σ ≤ 1 and 0 < θ ≤ 2π. (`qmp_orbit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L177)).

**Folded space-time integrals agree.** Proved result. For an integrable function on [0,1] × R³ that is invariant almost everywhere under the half-turn, the whole-space integral equals twice its cylindrical integral over r,z > 0, with Jacobian r; the weighted cylindrical integrand is integrable. (`integral_spacetime`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L212)).

**The stretch form has an absolute bound.** Proved result. For a periodic C¹ divergence-free model with weak Hessian and decay constant D, the stretching form is bounded by 729|D|(6|G|²+|v|²/(1+|y|)⁶) at every time and point. (`abs_stretch_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L314)).

**Weighted sixth-power term is integrable.** Proved result. For every admissible periodic perturbation, ∫₀¹∫R³ |v(σ,y)|²/(1+|y|)⁶ dy dσ is finite. (`sixth_weight_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L361)).

**The squared matrix norm is continuous.** Proved result. The squared Frobenius norm of a real 3 × 3 matrix is continuous in the matrix entries. (`continuous_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L410)).

**Stretch form has a nonnegative majorant.** Proved result. A model with weak Hessian and decay constant D gives the nonnegative pointwise majorant 729|D|(6|G|²+|v|²/(1+|y|)⁶) for the absolute value of the stretching form. (`enorm_stretch_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L414)).

**The stretch form is integrable.** Proved result. For a model with the prescribed weak Hessian and decay bounds and an admissible periodic perturbation, the stretching form is absolutely integrable over [0,1] × R³. (`stretch_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L430)).

**Stretch form is reflection-even a.e..** Proved result. The stretch form is reflection-even almost everywhere. (`stretch_flip_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L478)).

**The stretch mean has the folded integral.** Proved result. The perturbation's sixth-power integrability, the rotation-average identity and half-turn symmetry together give integrability of the stretching form and its mean, with total integral 4π∫r,z>0 r times the mean stretching density. (`stretchMeanIntegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchMeanIntegral.lean#L520)).

### Breakdown.CertCell.StretchTripleBound

This file bounds the stretch bilinear form using complex Cauchy-Schwarz estimates and the relation between curl and gradient energy. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Complex squared norms are nonnegative.** Proved result. For every finite complex vector x, the sum ∑ⱼ|xⱼ|² is nonnegative. (`cnormSq_nonneg_aux`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchTripleBound.lean#L11)).

**Cauchy-Schwarz bounds a complex pairing.** Proved result. The absolute value of a finite complex bilinear sum is at most the product of the two square-root sum-of-squares norms. (`norm_sum_mul_le_sqrt_cnormSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchTripleBound.lean#L14)).

**A square bound gives a norm bound.** Proved result. If γ ≥ 0 and c ≤ γ²d, then √c ≤ γ√d, with the real square root assigned zero for negative arguments. (`sqrt_le_mul_sqrt_of_le_sq_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchTripleBound.lean#L20)).

**Difference square is at most two squares.** Proved result. The squared norm of a complex difference is at most twice the sum of the two squared norms. (`norm_sub_sq_le_two_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchTripleBound.lean#L25)).

**Curl energy bounded by gradient energy.** Proved result. Curl energy is at most twice gradient energy. (`cnormSq_curlOfGrad_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchTripleBound.lean#L30)).

**The rotational stretch term is bounded.** Proved result. A curl-gradient operator bound γ gives a rotational stretch bound √2 γ/2 times the velocity and gradient square-energy norms. (`rotation_term_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchTripleBound.lean#L43)).

**Stretch bilinear form obeys its bound.** Proved result. If the symmetric model gradient and the model vorticity gradient have operator bounds σ ≥ 0 and γ ≥ 0, the stretching bilinear form is bounded by σ|curl g||curl g′|+√2γ|a||g′|+(√2/2)γ|a′||g|. (`stretchBilin_norm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StretchTripleBound.lean#L83)).

### Breakdown.CertCell.StripDataFlipAxis

This file treats the radial axis in the strip reflection argument using weighted integrability and the independence of a weak trace from its outer height. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Side trace at zero is the upper trace.** Proved result. For h > 0, the side trace at z = 0 using endpoint h equals the upper trace expression formed from the same function and candidate derivative. (`sideTrace_zero_eq_upperTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipAxis.lean#L13)).

**Strip weight is continuous on its domain.** Proved result. If the radial weight and radial test function are continuous, their product, viewed as a complex-valued function on any meridian set, is continuous there. (`weight_continuousOn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipAxis.lean#L26)).

**Weighted strip data are integrable.** Proved result. For h > 0, an integrable function on [lo,hi] × [0,h] remains integrable after multiplication by the product of two continuous radial factors. (`weighted_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipAxis.lean#L30)).

**Axis-weighted strip data are integrable.** Proved result. If the radial test weight factors as r times a continuous function and rg is integrable on [0,hi] × [0,h], then the weighted function is integrable on the same strip. (`axis_weighted_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipAxis.lean#L36)).

**Outer height does not change side traces.** Proved result. The side trace is independent of outer height. (`side_eq_at_heights`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipAxis.lean#L51)).

**Axis strip data obey reflection.** Proved result. The plane reflection, trace, mode derivative and axis integrability results give the half-turn law for strip moments down to r = 0: velocity moments acquire εₐ, and admissibly weighted height-derivative moments acquire −εₐ, independently of the positive strip height. (`stripDataFlipAxis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipAxis.lean#L64)).

### Breakdown.CertCell.StripDataFlipLinks

This file supplies rectangle integrability for the labeled fields and connects the height-trace identity with the strip reflection contract. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Mode fields are integrable on rectangles.** Proved result. For an admissible perturbation, each velocity mode and the mode fields representing its first and second weak height derivatives are integrable on every closed meridian rectangle whose radial lower endpoint is strictly positive. (`plane_rect_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipLinks.lean#L14)).

**The upper trace is independent of height.** Proved result. Assuming trace independence, if f has weak derivative f′ on every symmetric interval about zero, the upper trace at zero is independent of the chosen positive interval height. (`trace_eq_at_heights`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipLinks.lean#L42)).

**Reflection of strip data.** Proved result. The plane-reflection, strip-trace, and height-derivative assumptions give reflection compatibility of the strip data. (`stripDataFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripDataFlipLinks.lean#L52)).

### Breakdown.CertCell.StripMomentTrace

This file proves the strip-moment trace contract from the underlying one-dimensional weak trace formulas. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Strip moments recover their trace.** Proved result. For h > 0, lo < hi, integrable functions F,G on the strip and continuous radial weight and test function, the height-strip moment formed from F,G at z = 0 equals the radial integral of that weight times the upper trace expression of each slice. (`stripMomentTrace`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripMomentTrace.lean#L13)).

### Breakdown.CertCell.StripTraceParts

This file obtains radial and height integration-by-parts formulas for strip moments from weak one-dimensional primitives, including the radial axis limit. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Supported test products are integrable.** Proved result. If f is integrable on an open interval and θ is continuous with compact support inside it, the product θf is integrable on the whole real line. (`supported_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L13)).

**Recover the integral primitive a.e..** Proved result. On an open interval, an integrable function with the prescribed integrable weak derivative equals one constant plus the integral of that derivative from the lower endpoint, almost everywhere. (`weak_rep`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L26)).

**Primitive pairings integrate by parts.** Proved result. For integrable D on [a,b] and C¹ function k, writing F(x) = c+∫ₐˣD gives ∫ₐᵇ[Dk+Fk′] = F(b)k(b)−ck(a). (`primitive_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L68)).

**The ramp derivative is the inverse width.** Proved result. The derivative of the linear ramp (x-o)/d is the constant 1/d, with totalized division. (`ramp_deriv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L146)).

**Traces from weak line pairings.** Proved result. Weak line pairings recover endpoint traces. (`line_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L151)).

**The reciprocal is not integrable at zero.** Proved result. For every δ > 0, the function t ↦ 1/t is not integrable on (0,δ). (`not_integrable_inv`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L207)).

**Radial weights remove the axis term.** Proved result. Radial weights remove the axis boundary term. (`axis_line_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L217)).

**Enclosing intervals symmetrically.** Proved result. Every interval lies in a symmetric interval. (`sym_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L364)).

**Iterated integrals of products.** Proved result. Product integrals equal iterated integrals. (`prod_iter`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L367)).

**Supported slice integrals are integrable.** Proved result. If H is integrable on [c,d] × [−Z,Z] and χ is continuous, the weighted slice integral r ↦ ∫ from −Z to Z of χ(z)H(r,z)dz is integrable on [c,d]. (`slice_int`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L372)).

**Slicing product test pairings.** Proved result. Product test pairings separate into slices. (`slice_pair`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L379)).

**Height averages of radial weak pairs.** Proved result. A smooth compactly supported height cutoff gives a one-dimensional weak radial derivative identity by integrating both entries of the radial weak pair against the same cutoff. (`radial_slices`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L403)).

**Radial line boundary terms cancel.** Proved result. For 0≤a< b< u, assume complex-valued f and rf′ are integrable on (0,u), f′ is integrable on (δ,u) for every δ>0, and f′ is the weak derivative of f on (0,u). For every k∈C¹(ℝ;ℂ), integration by parts gives ∫ₐᵇ[rf′k+f(k+rk′)−bk(b)(f+(r−a)f′)/(b−a)−ak(a)(f+(r−b)f′)/(a−b)]dr = 0. (`radial_line`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L456)).

**Bounded sets lie in a symmetric interval.** Proved result. Every compact subset of R is contained in some symmetric interval [−Z,Z]. (`bounded_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L536)).

**Slice identity passes to the rectangle.** Proved result. For a fixed radial interval [a,b], let α be continuous and suppose F and β(r)G are integrable on [a,b]×[-Z,Z] for every Z > 0. If every smooth compactly supported height test χ satisfies ∫ₐᵇ[α(r)∫χ(z)F(r,z)dz+β(r)∫χ(z)G(r,z)dz]dr = 0, then ∫_[a,b]×[lo,hi]t(z)[α(r)F(r,z)+β(r)G(r,z)]dr dz = 0 for every height weight t, with a nonintegrable integral assigned zero. (`slice_core`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L543)).

**Radial strip pairings integrate by parts.** Proved result. For a radial weak pair and C¹ k, integration by parts on [a,b] × [lo,hi], with 0 ≤ a < b, rewrites ∂rF·rk+F(k+rk′) as the two radial endpoint trace terms; the bulk term and the upper trace term are integrable against a continuous height test. (`radial_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L614)).

**Weighted rectangle slices are integrable.** Proved result. If rG is integrable on a rectangle and a bounded continuous radial cutoff χ vanishes for |r| < δ with δ > 0, then χG is integrable on that rectangle. (`wslice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L738)).

**Product integrals may reverse order.** Proved result. For an integrable function on a product of two real sets, the product integral equals the iterated integral taken first in the first coordinate and then in the second. (`prod_iter_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L764)).

**The reversed test pairing separates.** Proved result. If χH is integrable on [−R,R] × [c,d], χ vanishes outside [−R,R] and continuous θ vanishes outside [c,d], the whole-plane integral of χ(r)θ(z)H(r,z) equals ∫θ(z)[∫₋Rᴿχ(r)H(r,z)dr]dz. (`slice_pair_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L769)).

**Radial averages of height weak pairs.** Proved result. A smooth radial cutoff supported away from the axis gives a one-dimensional weak height derivative identity after both entries of the height weak pair are averaged against it. (`height_slices`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L797)).

**Height line boundary terms cancel.** Proved result. Let a< b and suppose complex-valued f and g are integrable on (a−1,b+1), with g the weak derivative of f there. For every k∈C¹(ℝ;ℂ), integration by parts gives ∫ₐᵇ[gk+fk′−k(b)(f+(x−a)g)/(b−a)−k(a)(f+(x−b)g)/(a−b)]dx = 0. (`height_line`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L850)).

**The height identity passes to rectangles.** Proved result. For continuous α and β, assume rF and rG are integrable on every bounded radial strip over [a,b], and F and G are locally integrable away from r = 0. If ∫ₐᵇ[α(z)∫χ(r)F(r,z)dr+β(z)∫χ(r)G(r,z)dr]dz = 0 for every smooth compactly supported radial test χ vanishing near the axis, then ∫_[lo,hi]×[a,b]w(r)[α(z)F(r,z)+β(z)G(r,z)]dr dz = 0 for every radial weight w, with a nonintegrable integral assigned zero. (`height_core`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L880)).

**Height strip pairings integrate by parts.** Proved result. Let H be the weak height derivative of F off the axis, with rF and rH locally integrable on ℝ² and F,H locally integrable where r≠0, and let k∈C¹(ℝ;ℂ) and t∈C(ℝ;ℂ). On Q=[lo,hi]×[a,b] with a< b, all three integrands are integrable and ∫Q r(Hk+Fk′)t = k(b)∫Q rt[F+(z−a)H]/(b−a) + k(a)∫Q rt[F+(z−b)H]/(a−b), where k and k′ depend on z and t on r. (`height_parts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/StripTraceParts.lean#L976)).

### Breakdown.CertCell.TailAngular

This file derives angular lower bounds from the rotation generators acting on velocity, gradient, curl and Hessian modes. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Angular mode inequalities a.e..** Proposition definition. This proposition requires the angular energy relations to hold almost everywhere in time and space for every mode of a positive-period perturbation. (`AngularModePointwise`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L19)).

**Complex square sum is the Euclidean norm.** Proved result. For a finite complex vector x, √(∑ⱼ|xⱼ|²) is its Euclidean norm. (`sqrt_cnormSq_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L30)).

**A norm lower bound from angular data.** Proved result. Angular identities give a lower norm bound. (`lower_of_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L35)).

**Radius bounds angular contraction.** Proved result. The norm of angular contraction is at most cylindrical radius times the square root of the sum of squared matrix entries. (`contract_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L57)).

**The nonnegative angular gain is bounded.** Proved result. If the rotation-generator error has norm at most c times the field norm, the positive part of |k|−c times the field norm is at most cylindrical radius times the derivative square-energy norm. (`gain_max`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L80)).

**Bounding a squared difference.** Proved result. Difference squares obey the two-term bound. (`sq_norm_sub_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L91)).

**The first curl component is a difference.** Proved result. For a complex gradient matrix g indexed by output then differentiation direction, the first curl component is g₃₂−g₂₃. (`curlOfGrad_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L96)).

**Second curl component is a difference.** Proved result. For a complex gradient matrix g indexed by output then differentiation direction, the second curl component is g₁₃−g₃₁. (`curlOfGrad_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L100)).

**The third curl component is a difference.** Proved result. For a complex gradient matrix g indexed by output then differentiation direction, the third curl component is g₂₁−g₁₂. (`curlOfGrad_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L104)).

**Curl energy bounded by gradient energy.** Proved result. Curl energy is at most twice gradient energy. (`cnormSq_curlOfGrad_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L108)).

**The rotation generator on matrix entries.** Definition. The matrix rotation generator differentiates both the output-vector rotation and the inverse rotation of the input coordinate. (`pairGen`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L121)).

**The rotation generator on vectors.** Definition. The vector rotation generator records the components of the infinitesimal azimuthal field on coordinate unit vectors. (`vecGen`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L125)).

**The angular derivative law for curl.** Proved result. Curl obeys the angular differentiation law. (`curl_identity`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L127)).

**Angular mode bounds from derivatives.** Proved result. The mode derivative and rotation identities imply the angular energy inequalities almost everywhere in time and space for every mode of a positive-period perturbation. (`angularModePointwise_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngular.lean#L151)).

### Breakdown.CertCell.TailAngularPlane

This file transports almost-everywhere angular estimates from space to the meridian half-plane and checks the measurability needed for labeled mode integrals. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Meridian points are a two-coordinate sum.** Proved result. The embedding of a meridian pair (r,z) in R³ is re₁+ze₃ = (r,0,z). (`planePoint_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L20)).

**Meridian embedding is continuous.** Proved result. The map (r,z) ↦ (r,0,z) from the meridian plane into R³ is continuous. (`continuous_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L24)).

**Rotated meridian points are cylindrical.** Proved result. Rotating the meridian point (r,0,z) through θ gives the cylindrical point (r cos θ,r sin θ,z). (`axialRot_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L29)).

**The meridian orbit map is continuous.** Proved result. The map ((r,z),θ) ↦ Rθ(r,0,z) is continuous jointly in radius, height and angle. (`continuous_orbitPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L35)).

**Cylindrical spatial integration.** Proved result. Space integration has cylindrical coordinates. (`lintegral_eq_cylindrical`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L47)).

**Good rotations for almost every meridian.** Proved result. Almost every meridian has a good rotation. (`ae_exists_rotation_planePoint_of_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L82)).

**Radius on the meridian section.** Proved result. At a positive-radius meridian point, cylindrical radius equals the first planar coordinate. (`cylRadius_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L121)).

**Angular bounds descend to the plane.** Proved result. Almost-everywhere spatial angular energy inequalities imply the corresponding cylindrical weighted label inequalities almost everywhere on the half-plane. (`angularModeBounds_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L129)).

**Full turns leave rotations unchanged.** Proved result. For every integer n, rotation through φ+2πn gives the same vector as rotation through φ. (`axialRot_add_int_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L176)).

**A periodic null set is globally null.** Proved result. If a subset of R is invariant under shifts by integer multiples of 2π and has measure zero in (−π,π), then it has measure zero on all of R. (`volume_eq_zero_of_periodic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L181)).

**Angular orbits avoid null sets a.e..** Proved result. Almost every angular orbit avoids a null set. (`ae_volume_rotation_planePoint_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L219)).

**Equal coordinate maps preserve null sets.** Proved result. Any map equal to (r,z,σ,θ) ↦ (σ,Rθ(r,0,z)) pulls space-time null sets back to null sets when r,z > 0 and σ,θ range over R. (`quasiMeasurePreserving_of_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L249)).

**Meridian orbit map preserves null sets.** Proved result. The cylindrical orbit map (r,z,σ,θ) ↦ (σ,Rθ(r,0,z)) preserves almost-everywhere statements when pulled back to r,z > 0 with arbitrary real time and angle. (`quasiMeasurePreserving_orbitPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L284)).

**Orbit averages are a.e. measurable.** Proved result. Orbit averages are almost-everywhere measurable. (`aestronglyMeasurable_orbitAverage`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L293)).

**Field measurability from coordinates.** Proved result. Measurable coordinates give measurable fields. (`aestronglyMeasurable_of_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L333)).

**Labeled fields are a.e. measurable.** Proved result. Labeled fields are almost-everywhere measurable. (`aestronglyMeasurable_labelFields`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailAngularPlane.lean#L340)).

### Breakdown.CertCell.TailCoefficients

This file compares mode coefficients with the uniform bounds recorded in a set of piece data. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**A logical indicator equals its bit value.** Proved result. If a condition holds exactly when a given binary flag is true, its 0-or-1 indicator equals the numeric value of that flag. (`ind_eq_bit`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L13)).

**Logical indicators are nonnegative.** Proved result. The 0-or-1 indicator of any condition is nonnegative. (`ind_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L19)).

**Boolean bit values are nonnegative.** Proved result. Each of the two numeric values assigned to a binary flag, 0 and 1, is nonnegative. (`bit_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L23)).

**A bit preserves inequalities.** Proved result. If x ≤ y whenever a binary flag is true, multiplying both sides by its 0-or-1 value gives an inequality valid in both flag states. (`bit_mul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L27)).

**The first amplitude is velocity.** Proved result. The first entry in the four harmonic amplitude bounds is the velocity amplitude bound. (`ampOf_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L32)).

**The second amplitude is gradient.** Proved result. The second entry in the four harmonic amplitude bounds is the velocity-gradient amplitude bound. (`ampOf_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L34)).

**The third amplitude is vorticity.** Proved result. The third entry in the four harmonic amplitude bounds is the vorticity amplitude bound. (`ampOf_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L36)).

**Fourth amplitude is vorticity gradient.** Proved result. The fourth entry in the four harmonic amplitude bounds is the vorticity-gradient amplitude bound. (`ampOf_three`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L38)).

**Harmonic amplitude sums are nonnegative.** Proved result. For admissible weak model data and multiplier weights, the total harmonic amplitude sum is nonnegative at every spatial point. (`harmonicSum_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L47)).

**Inward gradient sums are nonnegative.** Proved result. For admissible weak model data, the inward sum of gradient-amplitude contributions is nonnegative for every mode set, target frequency and point. (`inward_gradW_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L54)).

**Share coefficient obeys its upper bound.** Proved result. For admissible weak data, if the piece bounds are valid on a mode set I and meridian region Z, then each mode in I and point in Z satisfies the prescribed upper enclosure for the summed share coefficient. (`shareHat_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L70)).

**Curl coefficient obeys its lower bound.** Proved result. For admissible weak data and valid piece bounds on I × Z, the prescribed curl lower bound is at most the mode's curl coefficient after subtracting its convection correction. (`curl_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L82)).

**Gradient coefficient lower bound.** Proved result. The gradient coefficient obeys its lower bound. (`grad_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L114)).

**Velocity coefficient lower bound.** Proved result. The velocity coefficient obeys its lower bound. (`vel_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L139)).

**Uniform coefficient lower bounds.** Proved result. Admissibility and valid set-piece coefficient bounds imply domination of the lower point coefficients on every designated mode and region. (`uniformCoefficientBounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailCoefficients.lean#L180)).

### Breakdown.CertCell.TailExteriorLinks

This file combines coefficient domination, cross-term absorption and inverse-square estimates to justify the exterior nonnegativity condition. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Stretch adjustments preserve domination.** Proved result. Coefficientwise domination survives the stretching correction when its scale is nonnegative, the comparison uses larger curl and gradient bounds and both sides have the same positive length scale. (`dominates_withStretch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L22)).

**The cross term is absorbed by squares.** Proved result. For χ ≥ 0, ρ > 0 and s > 0, the mixed term (χ/ρ)x₁x₀ is at most (χ/(2s))x₁²+(χs/2)x₀²/ρ². (`cross_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L76)).

**Absorbed coefficients satisfy the tests.** Proved result. If c > 0, v,χ ≥ 0 and v/c+χ/√c ≤ g, then v+χ√c/2 lies between zero and c(g−χ/(2√c)), and g−χ/(2√c) is nonnegative. (`coeff_facts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L85)).

**Positive-part differences balance.** Proved result. For nonnegative x and y, their positive parts satisfy max(x−y,0)+y = max(y−x,0)+x. (`ofReal_sub_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L106)).

**Controlling the negative integral part.** Proved result. An almost-everywhere density lower bound by γS−αV, the absorption relation α≤γc, and a finite inverse-square integral estimate bound the negative density integral by the positive one. (`lintegral_neg_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L116)).

**The plane radius is continuous.** Proved result. The meridian radius (r,z) ↦ √(r²+z²) is continuous on R². (`continuous_planeRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L169)).

**Complex squared norms are continuous.** Proved result. For every finite complex vector, its sum of squared component moduli depends continuously on the vector. (`continuous_cnormSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L173)).

**Complex squared norms are nonnegative.** Proved result. For every finite complex vector, the sum of squared component moduli is nonnegative. (`cnormSq_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L177)).

**Exterior bounds imply exterior soundness.** Proved result. Angular inequalities, pointwise quadratic tests, coefficient bounds, finite label-gradient energy, and ray and square inverse-square estimates imply the certified exterior negative-to-positive integral bound. (`exteriorConditionSound_of_bounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailExteriorLinks.lean#L184)).

### Breakdown.CertCell.TailFlipDecay

This file proves reflection parity of velocity modes and the sixth-power finiteness needed for the exterior approximation arguments. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Pulling a.e. facts back to orbits.** Proved result. Almost-everywhere facts pull back to orbits. (`ae_orbit_of_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L23)).

**Meridian rotation gives cylinder points.** Proved result. Cylindrical coordinates equal rotated points. (`cylArg_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L46)).

**Reflection reverses orbit angle.** Proved result. Rotating the reflected meridian point (r,0,−z) through φ equals applying the half-turn to the original meridian point rotated through −φ. (`rot_plane_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L51)).

**Rotation and reflection reverse signs.** Proved result. For the half-turn R and signs ε = (1,−1,−1), the components satisfy (R₋φRw)ₐ = εₐ(Rφw)ₐ. (`rot_neg_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L57)).

**Adding a full turn preserves rotation.** Proved result. Adding 2π to an axial rotation angle leaves the rotated vector unchanged. (`axialRot_add_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L62)).

**Negated full turns preserve rotation.** Proved result. Replacing −φ by −(φ+2π) leaves the axial rotation unchanged. (`axialRot_neg_add_period`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L65)).

**Reflection and angle reversal keep phase.** Proved result. Reflection and angle reversal preserve phase. (`expFactor_flip_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L70)).

**Mode flip gives coordinate sign changes.** Proved result. Mode reflection gives coordinate sign changes. (`modeVel_flip_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L76)).

**Time slices satisfy a sixth-power bound.** Proved result. Almost every time in the unit period has finite gradient energy and a sixth-power velocity bound controlled by the cube of that energy. (`slice_sixth_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L126)).

**Space-time orbit maps preserve null sets.** Proved result. The space-time rotation map (y,σ,θ) ↦ (σ,Rθy) pulls Lebesgue-null sets back to null sets in the product of space, time and angle. (`orbit_qmp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L142)).

**Rotation keeps the sixth-power integral.** Proved result. Rotation preserves the sixth-power integral. (`rot_lintegral_sixth`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L171)).

**An orbit integral bounds each mode.** Proved result. A velocity-mode component is bounded by the integral of the field norm over its unit-time and full-angle orbit. (`modeVel_enorm_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L184)).

**Squared L6 norm is time integrable.** Proved result. The squared sixth-power norm is time integrable. (`velocity_sixth_square`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L210)).

**Finite sixth power of each velocity mode.** Proved result. Each velocity mode has finite sixth power. (`mode_sixth_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L232)).

**Labeled velocity modes obey reflection.** Proved result. For an admissible perturbation with positive period and the half-turn among its symmetries, each labeled velocity mode satisfies the corresponding height-reflection law with the angular label reversed. (`labelFlipEvenHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L375)).

**Time integrability of squared L6 norms.** Proposition definition. This proposition requires the squared spatial L6 norm of a perturbation to be integrable over the unit time period. (`VelocitySixthSquareIntegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L398)).

**L6 integrability of each velocity mode.** Proposition definition. This proposition requires each velocity mode at time zero to have finite spatial sixth-power integral. (`ModeVelSixthFinite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L402)).

**The time-integrated L6 bound is proved.** Proved result. For every perturbation, the squared spatial L6 norm is integrable over the unit time period. (`velocitySixthSquareIntegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L406)).

**Velocity-mode sixth powers are finite.** Proved result. Every velocity mode of an admissible periodic perturbation has finite spatial sixth-power integral at normalized time zero. (`modeVelSixthFinite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailFlipDecay.lean#L409)).

### Breakdown.CertCell.TailGradFinite

This file bounds the labeled gradient energy by space-time orbit averages and proves its weighted half-plane integral is finite. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Choosing an a.e. measurable majorant.** Proved result. An almost-everywhere measurable majorant exists. (`exists_measurable_ge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L19)).

**A shifted period integral is bounded.** Proved result. For a nonnegative extended-valued 2π-periodic function, its integral over (0,2π] is at most twice its integral over (−π,π). (`lintegral_period_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L40)).

**Cylindrical coordinates are periodic.** Proved result. The cylindrical point (r cos θ,r sin θ,z) is unchanged when θ is replaced by θ+2π. (`cylPoint_add_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L65)).

**Meridian rotation and cylindrical points.** Proved result. Meridian rotation gives cylindrical coordinates. (`axialRot_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L68)).

**Cylindrical coordinates are measurable.** Proved result. The cylindrical coordinate map ((r,z),θ) ↦ (r cos θ,r sin θ,z) is measurable. (`measurable_cylPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L73)).

**The cylindrical integral bound.** Proved result. For a measurable nonnegative extended-valued function, the cylindrical integral over the half-plane and one full turn is at most twice its spatial integral. (`cyl_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L77)).

**Matrix entry is bounded by operator norm.** Proved result. Every matrix entry obtained by rotating the input and output frames is bounded in absolute value by the original operator norm. (`norm_entry_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L107)).

**Columns bound the operator norm.** Proved result. For a real linear map A on R³, ‖A‖ ≤ ∑ⱼ‖Aeⱼ‖, so the sum of its column norms bounds its operator norm. (`opNorm_le_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L116)).

**Matrix energy bounds operator norm.** Proved result. The square of the spatial operator norm is at most three times the sum of squared column norms. (`norm_sq_le_three_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L129)).

**Averaging bounds gradient-mode entries.** Proved result. A gradient-mode entry is bounded by 1/(2π) times the unit-time and full-angle integral of any pointwise operator-norm majorant. (`enorm_modeGrad_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L139)).

**Cauchy-Schwarz bounds a squared integral.** Proved result. The square of a nonnegative lower integral is at most the total measure times the lower integral of the square. (`sq_lintegral_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L164)).

**Orbit energy bounds label gradients.** Proved result. The labeled gradient square energy is bounded by 9/(2π) times the full-angle and unit-time integral of a measurable squared gradient majorant along its cylindrical orbit. (`labelGrad_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L177)).

**Finite weighted label-gradient energy.** Proved result. Label gradients have finite weighted energy. (`labelGradFinite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailGradFinite.lean#L225)).

### Breakdown.CertCell.TailPointwise

This file provides the elementary quadratic and angular-ratio inequalities used in the pointwise exterior test. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The quadratic test gives nonnegativity.** Proved result. If A,B ≥ 0 and c² ≤ 4AB, the quadratic form Ax²+By²−cxy is nonnegative for all real x and y. (`quadForm_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailPointwise.lean#L36)).

**Squaring the angular ratio bound.** Proved result. For positive radius and nonnegative frequency and amplitude, squaring the angular bound gives frequency squared times amplitude squared over radius squared at most the gradient variable squared. (`sq_ratio_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailPointwise.lean#L52)).

### Breakdown.CertCell.TailRayBound

This file proves a radial Hardy estimate on domains that begin once along each ray and transfers it from smooth compact fields to weak fields. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Measurable exterior cut once on each ray.** Proposition definition. A ray exterior is a measurable set whose intersection with each positive unit ray is either empty or an open tail starting at a positive radius. (`IsRayExterior`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L20)).

**Gradient applied in the radial direction.** Definition. The radial application of a linear map evaluates it on the unit radial direction. (`radialApply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L24)).

**The weak inverse-square estimate on rays.** Interface. This proposition bounds the inverse-radius-square energy of an L6 field with integrable weak-gradient energy on a ray exterior by four times its radial-gradient energy there. (`RadialRayStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L26)). Proof route: `Breakdown.CertCell.TailBand.radialRay`.

**A radial line obeys the Hardy bound.** Proved result. For a C¹ compactly supported vector field u, a nonzero ray direction e and a > 0, ∫ₐ∞|u(re)|²dr ≤ 4∫ₐ∞r²|Du(re)[e]|²dr. (`line_sum`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L37)).

**The lower endpoint of exterior rays.** Proved result. An exterior ray integral starts at its radius. (`ray_cut`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L76)).

**Each exterior ray obeys the Hardy bound.** Proved result. Let S be measurable and suppose its intersection with each positive unit ray is empty or exactly {re : r > a} for some a > 0 depending on the ray. Every C¹ compactly supported field u satisfies ∫ₐ∞|u(re)|²dr ≤ 4∫ₐ∞r²|∂ᵣu(re)|²dr on each nonempty ray, and both restricted integrals vanish on an empty ray. (`dir_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L90)).

**Radial derivative energy is measurable.** Proved result. If a matrix field A is measurable, the squared norm |A(y)[y/|y|]|² of its radial action is measurable, with the radial direction assigned zero at the origin. (`slope_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L141)).

**Exterior Hardy bounds for compact fields.** Proved result. Compact fields obey the exterior Hardy bound. (`compact_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L147)).

**Weighted squares split a perturbation.** Proved result. For vectors b,c and θ > 0, |b+c|² ≤ (1+θ)|b|²+(1+θ⁻¹)|c|². (`sq_le_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L158)).

**Matrix square energy is nonnegative.** Proved result. The squared Frobenius norm of every real 3 × 3 matrix is nonnegative. (`entrySq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L167)).

**Energy controls radial derivative errors.** Proved result. The squared difference of the two radial applications is at most the sum of squared matrix entries of the difference map. (`slope_diff_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L170)).

**Weak radial derivatives are measurable.** Proved result. If a matrix field G is measurable up to a null set, its radial action G(y)[y/|y|] is also measurable up to a null set. (`slope_aesm`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L183)).

**Hardy bounds by smooth approximation.** Proved result. Smooth approximation transfers the Hardy bound. (`transfer`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L189)).

**Exterior Hardy bounds for smooth fields.** Proved result. Smooth fields obey the exterior Hardy bound. (`smooth_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayBound.lean#L267)).

### Breakdown.CertCell.TailRayModes

This file splits complex mode energy into real, imaginary, radial and angular pieces and prepares the cylindrical reduction of the ray estimate. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Real matrices act by coordinate sums.** Proved result. The real matrix obtained from a complex matrix g acts by (Re g·x)ᵢ = ∑ⱼRe(gᵢⱼ)xⱼ. (`reMat_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L23)).

**Imaginary matrix action by coordinates.** Proved result. Imaginary matrices act by coordinate sums. (`imMat_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L27)).

**Real vectors select real coordinates.** Proved result. Taking the real vector associated with a complex vector x gives Cartesian components Re(xᵢ). (`reVec_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L31)).

**Taking imaginary vector coordinates.** Proved result. Imaginary vectors select imaginary coordinates. (`imVec_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L35)).

**Norm square is three coordinate squares.** Proved result. For a real vector x ∈ R³, |x|² = x₁²+x₂²+x₃². (`norm_sq_three`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L39)).

**Complex energy is six real squares.** Proved result. The squared norm of a complex three-vector is the sum of the squares of the real and imaginary parts of its three coordinates. (`cnormSq_three`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L43)).

**Real and imaginary energy splitting.** Proved result. Complex energy splits into real and imaginary. (`cnormSq_re_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L48)).

**Radial and angular row-energy bounds.** Proved result. At positive cylindrical radius, the squared radial projection plus squared angular projection of a real row is at most the row's squared Euclidean norm. (`row_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L53)).

**The angular matrix-row contraction.** Proved result. Contracting a complex matrix row with the angular direction gives its second entry times the first spatial coordinate minus its first entry times the second coordinate, separated into real and imaginary parts. (`contract_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L60)).

**Splitting each gradient row's energy.** Proved result. Each gradient row splits into two energies. (`grad_row`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L65)).

**Bounds for radial and angular energy.** Proved result. At positive cylindrical radius, real and imaginary radial-gradient energies plus cylindrical-normalized angular-contraction energy are at most the full complex matrix energy. (`grad_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L85)).

**Angular gain squares to an energy bound.** Proved result. If u = ikw+Jw, where J generates axial rotation, then max(|k|−1,0)²|w|² ≤ |u|² for every real k and complex vector w. (`gain_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L96)).

**Complex scaling rescales square energy.** Proved result. Multiplying a finite complex vector by c multiplies its squared norm by |c|². (`cnormSq_const_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L129)).

**Rotation preserves complex vector energy.** Proved result. Axial rotation, extended to complex vectors, preserves the sum of squared component moduli. (`cnormSq_rotC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L133)).

**Inverse rotation transposes its matrix.** Proved result. The matrix of rotation through −ψ is the transpose of the matrix of rotation through ψ. (`rot_transpose`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L138)).

**Rotation preserves complex matrix energy.** Proved result. Rotating both indices of a complex matrix preserves its squared Frobenius norm. (`cnormSq_rotCMat`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L142)).

**Time shift adds a phase to mode averages.** Proved result. Time shift multiplies mode averages by phase. (`modeAverage_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L160)).

**Time shift keeps velocity-mode energy.** Proved result. Time shift preserves velocity-mode energy. (`cnormSq_modeVel_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L211)).

**Time shift keeps gradient-mode energy.** Proved result. Time shift preserves gradient-mode energy. (`cnormSq_modeGrad_shift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L224)).

**Inverse rotation recovers the meridian.** Proved result. Inverse rotation returns the meridian point. (`rot_cyl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L239)).

**Plane coordinates of cylindrical points.** Proved result. Cylindrical points recover plane coordinates. (`pointPlane_cyl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L246)).

**Cylindrical and meridian radii agree.** Proved result. The Euclidean norm of the cylindrical point (r cos θ,r sin θ,z) equals √(r²+z²), independently of θ. (`norm_cyl`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L252)).

**The meridian projection is measurable.** Proved result. The meridian projection y ↦ (√(y₁²+y₂²),y₃) is measurable. (`pointPlane_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L259)).

**Ray exterior regions are measurable.** Proved result. For a measurable direction-dependent radius R, the meridian set {r,z > 0 : √(r²+z²) > R(r,z)} is measurable. (`planeRayRegion_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L263)).

**A ray region lifts to a spatial exterior.** Proved result. If R is measurable, unchanged by positive scaling and bounded between positive R₀ and finite R₁, lifting its meridian exterior to R³ gives a measurable set that meets each ray in an empty set or an interval beyond a positive radius. (`rayExterior_lift`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L271)).

**Planar reduction by axisymmetry.** Proved result. Axisymmetric integrals reduce to the plane. (`cyl_transfer`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L310)).

**Pulling back null sets through cylinders.** Proved result. A spatial property holding almost everywhere pulls back almost everywhere to the restricted cylindrical region. (`ae_region_of_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L337)).

**Complex square energies are nonnegative.** Proved result. Every finite complex vector has nonnegative squared Euclidean norm. (`cnormSq_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L343)).

**A sixth-power bound gives L6 membership.** Proved result. If f is measurable up to a null set, |f(y)|² ≤ B(y) everywhere and ∫B(y)³dy is finite, then f belongs to L⁶(R³). (`memLp_six_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L346)).

**Matrix square energy is continuous.** Proved result. The squared Frobenius norm is a continuous function of a real matrix. (`entrySq_cont`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L358)).

**Finite matrix energy gives integrability.** Proved result. If a matrix field A is measurable up to a null set and its squared Frobenius norm is bounded by a function with finite nonnegative integral, then |A|² is integrable. (`integrable_entrySq_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L362)).

**Real and imaginary matrix energies.** Proved result. Matrix energy splits into real and imaginary. (`entrySq_re_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L370)).

**Complex energy bounds real matrices.** Proved result. The sum of squared entries of the real matrix part is at most the sum of squared absolute complex entries. (`entrySq_reMat_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L377)).

**Complex energy bounds imaginary matrices.** Proved result. The sum of squared entries of the imaginary matrix part is at most the sum of squared absolute complex entries. (`entrySq_imMat_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L382)).

**Complex energy bounds real vectors.** Proved result. The squared Euclidean norm of the real vector part is at most the sum of squared absolute complex components. (`reVec_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L387)).

**Complex energy bounds imaginary vectors.** Proved result. The squared Euclidean norm of the imaginary vector part is at most the sum of squared absolute complex components. (`imVec_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L391)).

**Choosing a slice with all weak data.** Proved result. One time slice simultaneously has real and imaginary weak mode gradients, the almost-everywhere angular derivative identity, and integrable velocity and gradient rotation orbits. (`slice_choice`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L396)).

**Rotation preserves velocity-mode energy.** Proved result. If the velocity is integrable over the time-angle orbit through y, the squared norm of each velocity mode at Rψy equals its squared norm at y. (`cnormSq_vel_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L442)).

**Rotation preserves gradient-mode energy.** Proved result. If the gradient is integrable over the time-angle orbit through y, the squared Frobenius norm of each gradient mode is unchanged by rotating y. (`cnormSq_grad_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L450)).

**Ray regions stay in the upper half-plane.** Proved result. Ray regions lie in the positive half-plane. (`plane_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L463)).

**Restricted integrals using indicators.** Proved result. Region indicators give restricted integrals. (`plane_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L466)).

**Exterior indicators keep measurability.** Proved result. Exterior indicators preserve measurability. (`indicator_aemeasurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L478)).

**Cylindrical radius is positive a.e..** Proved result. Cylindrical radius is positive almost everywhere. (`region_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailRayModes.lean#L484)).

### Breakdown.CertCell.TailSquareDensity

This file extends the square-exterior Hardy estimate to weak symmetric fields by radial cutoffs, symmetry-preserving convolution and shrinking exterior collars. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The lifted square exterior in space.** Definition. The spatial square exterior is the inverse image of the planar square exterior under cylindrical-radius and height projection. (`spaceSquareExterior`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L17)).

**Rotation and flip covariance of a field.** Proposition definition. An axial reflection field is covariant under every axial rotation and under the prescribed spatial reflection. (`IsAxialFlipField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L20)).

**Smooth square-exterior Hardy inequality.** Interface. This proposition bounds twice the inverse-radius-square energy of a compactly supported C¹ axial reflection field on the square exterior by its gradient energy there. (`SquareExteriorSpaceSmoothStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L24)). Proof route: `Breakdown.CertCell.TailBand.squareExteriorSpaceSmooth_of`.

**Weak square-exterior Hardy inequality.** Interface. This proposition requires the same square-exterior bound for weak-gradient fields with finite L6 and gradient energies and almost-everywhere rotation and reflection covariance. (`SquareExteriorSpaceWeakStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L30)). Proof route: `Breakdown.CertCell.TailBand.squareExteriorSpaceWeak_of`.

**Radial cutoffs keep the field symmetries.** Proved result. Radial cutoffs preserve the field symmetries. (`cutoff_smul_isAxialFlipField`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L39)).

**Sixth-power tails tend to zero.** Proved result. If |w|⁶ is integrable on R³, its integral outside the ball of radius n+1 tends to zero as n tends to infinity. (`tail_sixth_tendsto`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L49)).

**Exterior bounds transferred by cutoffs.** Proved result. Cutting off extends the smooth exterior bound. (`cutoff_stage`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L66)).

**Coordinates of the square exterior.** Proved result. Membership in the spatial square exterior means positive cylindrical radius and height, with at least one exceeding the exterior threshold. (`mem_spaceSquareExterior`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L186)).

**The spatial square exterior is open.** Proved result. The spatial region obtained by lifting the open meridian square exterior is open in R³. (`isOpen_spaceSquareExterior`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L191)).

**A collar around the square exterior.** Definition. The exterior collar allows height down to −η while retaining the condition that cylindrical radius or height exceeds R. (`collar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L202)).

**The exterior collar is open.** Proved result. For any R and η, the region {(r,z) : r > R or z > R, and z > −η}, lifted by r = √(y₁²+y₂²), is open in R³. (`isOpen_collar`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L205)).

**Nearby points enter the exterior collar.** Proved result. A point within distance η of the lifted square exterior at radius R+η lies in the enlarged exterior region with radial or height threshold R and lower height −η. (`mem_collar_of_near`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L210)).

**Regularity by symmetric mollification.** Proved result. Positive-scale radial convolution of an L6 weak-gradient field with almost-everywhere rotation and reflection symmetry is C¹, remains L6, and has those symmetries everywhere. (`weakGradient_smoothing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L223)).

**Collar bounds for mollified energy.** Proved result. When twice the smoothing scale is at most the collar width, smoothed gradient energy outside the enlarged square is at most the original weak-gradient energy in the exterior collar. (`smoothing_energy_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L252)).

**Weak square-exterior inequality follows.** Proved result. The smooth square-exterior inequality extends to weak-gradient fields with finite L6 and gradient energies and almost-everywhere axial and reflection symmetry. (`squareExteriorSpaceWeak_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareDensity.lean#L324)).

### Breakdown.CertCell.TailSquareModes

This file applies the spatial square-exterior estimate to the real and imaginary parts of zero-azimuth modes and transports it to the labeled half-plane fields. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Real vectors select real coordinates.** Proved result. The real vector associated with a complex vector x has components Re(xᵢ). (`reVec_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L24)).

**Taking imaginary vector coordinates.** Proved result. Imaginary vectors select imaginary coordinates. (`imVec_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L27)).

**Real matrices act by coordinate sums.** Proved result. The real matrix associated with a complex matrix g acts on real vectors by (Re g·x)ᵢ = ∑ⱼRe(gᵢⱼ)xⱼ. (`reMat_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L30)).

**Imaginary matrix action by coordinates.** Proved result. Imaginary matrices act by coordinate sums. (`imMat_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L34)).

**Real and imaginary energy splitting.** Proved result. Complex energy splits into real and imaginary. (`cnormSq_eq_re_im`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L38)).

**A phase can be removed from real vectors.** Proved result. For a complex vector x and real α, Re x = cos(α)Re(eⁱαx)+sin(α)Im(eⁱαx). (`reVec_unphase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L43)).

**Removing phase from imaginary vectors.** Proved result. A phase can be removed from imaginary vectors. (`imVec_unphase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L51)).

**Phase can be removed from real matrices.** Proved result. For a complex matrix g and real α, Re g = cos(α)Re(eⁱαg)+sin(α)Im(eⁱαg). (`reMat_unphase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L59)).

**Removing phase from imaginary matrices.** Proved result. A phase can be removed from imaginary matrices. (`imMat_unphase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L69)).

**Real parts commute with rotation.** Proved result. Taking the real part of a complex vector after axial rotation gives the axial rotation of its real part. (`reVec_rotC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L79)).

**Imaginary parts commute with rotation.** Proved result. Taking the imaginary part of a complex vector after axial rotation gives the axial rotation of its imaginary part. (`imVec_rotC`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L84)).

**Vector rotation respects complex scalars.** Proved result. Axial rotation of complex vectors commutes with multiplication by any complex scalar. (`rotC_const_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L89)).

**Matrix rotation respects complex scalars.** Proved result. Rotation of both indices of a complex matrix commutes with multiplication by any complex scalar. (`rotCMat_const_mul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L95)).

**Composing vector rotations.** Proved result. Vector rotations compose by angle addition. (`rotC_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L101)).

**Composing matrix rotations.** Proved result. Matrix rotations compose by angle addition. (`rotCMat_add`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L106)).

**Flip in the complex coordinate frame.** Definition. Complex frame reflection multiplies each vector component by the corresponding real reflection sign. (`frameFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L112)).

**Frame reflection is an involution.** Proved result. Applying the component signs (1,−1,−1) to a complex vector twice returns that vector. (`frameFlip_frameFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L114)).

**Frame reflection reverses rotation angle.** Proved result. For the component half-turn R, complex axial rotations satisfy R₋θR x = R Rθx. (`rotC_frameFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L118)).

**Real parts commute with frame reflection.** Proved result. The real part of the complex component half-turn is the real spatial half-turn of the real part. (`reVec_frameFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L126)).

**Imaginary parts respect frame reflection.** Proved result. Imaginary parts commute with frame reflection. (`imVec_frameFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L130)).

**A good slice of a full-measure product.** Proved result. A property depending only on the second variable holds almost everywhere when it holds almost everywhere on a positive-measure product. (`ae_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L134)).

**Second coordinate is nonzero a.e..** Proved result. The second coordinate is nonzero almost everywhere. (`ae_ne_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L139)).

**Scalar multiples preserve weak gradients.** Proved result. If g is the weak gradient of f, then cg is the weak gradient of cf for every real constant c. (`weak_smul`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L145)).

**Linear combinations keep weak gradients.** Proved result. Linear combinations preserve weak gradients. (`weak_comb`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L158)).

**Velocity-mode rotation on a common set.** Proved result. Velocity modes rotate on a common full set. (`good_vel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L163)).

**Gradient-mode rotation on a common set.** Proved result. Gradient modes rotate on a common full set. (`good_grad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L180)).

**Rotation covariance along orbits.** Proved result. Rotation covariance propagates along an orbit. (`good_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L197)).

**Mode field reflects almost everywhere.** Proved result. If a complex vector field is rotation covariant almost everywhere and obeys the height-reflection law on almost every meridian point with r,z > 0, it obeys the spatial half-turn law almost everywhere in R³. (`flip_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L202)).

**Unit complex phases preserve energy.** Proved result. Multiplying every component of a finite complex vector by exp(iα) preserves its squared norm. (`cnormSq_phase`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L241)).

**Matrix square energy is nonnegative.** Proved result. The sum of squared entries of a real 3 × 3 matrix is nonnegative. (`matSq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L245)).

**Complex energy bounds real vectors.** Proved result. The squared Euclidean norm of the real vector part is at most the full complex component square energy. (`reVec_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L248)).

**Complex energy bounds imaginary vectors.** Proved result. The squared Euclidean norm of the imaginary vector part is at most the full complex component square energy. (`imVec_sq_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L252)).

**Dominated fields have finite sixth power.** Proved result. If |f(y)|² is bounded by the squared norm of a complex vector field u(y) and ∫|u|⁶ is finite, then ∫|f|⁶ is finite. (`sixth_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L256)).

**Gradient modes have finite total energy.** Proved result. For every admissible perturbation and every temporal-angular mode, the squared norm of its gradient mode at time zero has finite spatial integral. (`modeGrad_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L262)).

**Composition keeps finite matrix energy.** Proved result. Composition preserves finite matrix energy. (`matSq_lintegral_finite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L284)).

**The flipped harmonic at azimuth zero.** Proved result. Zero-azimuth labels share the flipped harmonic. (`labelHarmonic_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L289)).

**A positive angular factor cancels.** Proved result. For nonnegative possibly infinite a,b, the inequality 2(2πa) ≤ 2πb implies 2a ≤ b. (`cancel_two_pi`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L297)).

**Meridian embedding keeps squared radius.** Proved result. Meridian embedding preserves squared radius. (`norm_planePoint_sq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L303)).

**Square-exterior bound passes to modes.** Proved result. The weak spatial square-exterior estimate implies 2∫r|vξ|²/(r²+z²) ≤ ∫r|Gξ|² on that exterior for each zero angular mode of an admissible positive-period perturbation satisfying the half-turn law. (`modeSquareInverseSquare_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareModes.lean#L312)).

### Breakdown.CertCell.TailSquareSmooth

This file proves the axial and transverse square-exterior inequalities by integrating two multiplier identities over a pair of rectangles. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The axial square-exterior inequality.** Interface. The axial planar exterior condition bounds twice the radius-weighted inverse-square energy by gradient energy for compactly supported C¹ functions vanishing on the horizontal boundary. (`SquareExteriorAxialSmoothStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L13)). Proof route: `Breakdown.CertCell.TailBand.squareExteriorAxialSmoothStatement`.

**Transverse square-exterior inequality.** Interface. The transverse planar exterior condition adds the cylindrical inverse-square energy to the gradient bound for compactly supported C¹ functions vanishing on the axis. (`SquareExteriorTransverseSmoothStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L19)). Proof route: `Breakdown.CertCell.TailBand.squareExteriorTransverseSmoothStatement`.

**Both smooth square-exterior inequalities.** Interface. The smooth square-exterior package requires both the axial and transverse planar inequalities. (`SquareExteriorSmoothStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L25)). Proof route: `Breakdown.CertCell.TailBand.squareExteriorSmoothStatement`.

**First slice derivative is a partial.** Proved result. For a differentiable two-variable function, the derivative of its first-coordinate slice equals its Fréchet derivative applied to (1,0). (`partial_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L28)).

**Second slice derivative is a partial.** Proved result. For a differentiable two-variable function, the derivative of its second-coordinate slice equals its Fréchet derivative applied to (0,1). (`partial_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L34)).

**First-coordinate slices differentiate.** Proved result. If g is differentiable on R², its first-coordinate slice at (x₁,x₂) has derivative Dg(x₁,x₂)[(1,0)]. (`line_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L40)).

**Second-coordinate slices differentiate.** Proved result. If g is differentiable on R², its second-coordinate slice at (x₁,x₂) has derivative Dg(x₁,x₂)[(0,1)]. (`line_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L45)).

**Rectangle divergence boundary integrals.** Proved result. Let g:ℝ²→ℝ be globally C¹ and let W=(W₁,W₂) be C¹ on an open set U containing Q=[a₁,b₁]×[a₂,b₂], where a₁≤b₁ and a₂≤b₂. Then 2g∇g·W+g²div W is integrable on Q, and its integral equals the signed boundary flux of g²W through the four edges. (`box_divergence`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L50)).

**Weighted squares bound the cross term.** Proved result. For ρ > 0 and real g,a,b,W₁,W₂, the cross term 2g(aW₁+bW₂) is at most ρ(a²+b²)+g²(W₁²+W₂²)/ρ. (`quad_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L92)).

**The first axial multiplier derivative.** Proved result. For positive height, the radial derivative of −2r²/(r²+z²) is −4rz²/(r²+z²)². (`axial_deriv_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L101)).

**The second axial multiplier derivative.** Proved result. For positive height, differentiating r(r²−z²)/(z(r²+z²)) gives the axial multiplier's height term used in the rectangle estimate. (`axial_deriv_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L110)).

**First transverse multiplier derivative.** Proved result. Away from the planar origin, the radial derivative of (z²−r²)/(r²+z²) is −4rz²/(r²+z²)². (`cross_deriv_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L122)).

**Second transverse multiplier derivative.** Proved result. Away from the planar origin, the height derivative of −2rz/(r²+z²) is −2r(r²−z²)/(r²+z²)². (`cross_deriv_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L131)).

**Axial multiplier gives a pointwise bound.** Proved result. For r ≥ 0 and z > 0, the multiplier W = (−2r²/(r²+z²), r(r²−z²)/(z(r²+z²))) satisfies 2g(aW₁+bW₂)+g²div W ≤ r(a²+b²)−2rg²/(r²+z²). (`axial_pointwise`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L140)).

**The transverse multiplier bound.** Proved result. The transverse multiplier gives a pointwise bound. (`cross_pointwise`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L160)).

**Plane radius squared is a coordinate sum.** Proved result. For a meridian point (r,z), its squared radius is r²+z². (`sq_planeRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L180)).

**Measurability of truncated exteriors.** Proved result. Truncated exterior regions are measurable. (`measurableSet_exterior`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L183)).

**Zero values beyond compact support.** Proved result. Compact support supplies a threshold beyond which either large positive coordinate forces both the function and its totalized derivative to vanish. (`support_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L190)).

**A height bound from plane vanishing.** Proved result. If g is globally K-Lipschitz and vanishes on z = 0, then |g(r,z)| ≤ K|z| everywhere. (`plane_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L205)).

**A radial bound from axis vanishing.** Proved result. If g is globally K-Lipschitz and vanishes on r = 0, then |g(r,z)| ≤ K|r| everywhere. (`axis_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L211)).

**Integrability on bounded regions.** Proved result. Bounded data on a finite region are integrable. (`integrableOn_bounded`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L217)).

**Truncated exterior splits into two boxes.** Proved result. For 0 ≤ ε < R and an integrable function vanishing when r ≥ L or z ≥ L, its integral over the square exterior with z > ε equals the sum of its integrals over [0,L] × [R,L] and [R,L] × [ε,R]. (`split_exterior`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L232)).

**The interval integral of zero.** Proved result. A zero integrand has zero interval integral. (`iint_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L262)).

**Boundary line integrals are finite.** Proved result. If g is continuous and W is continuous on a set containing a horizontal line segment, the boundary integrand g(t,c)²W(t,c) is integrable along that segment. (`line_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L265)).

**Exterior bounds from two rectangles.** Proved result. Two rectangle identities bound the exterior. (`two_box`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L272)).

**The square exterior is measurable.** Proved result. For every R, the meridian region {r,z > 0 : r > R or z > R} is measurable. (`measurableSet_square`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L314)).

**Weighted gradient energy is integrable.** Proved result. For a C¹ compactly supported function g on R², the radially weighted gradient energy r((∂rg)²+(∂zg)²) is integrable over the plane. (`grad_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L319)).

**Radial inverse-square term is integrable.** Proved result. For a C¹ compactly supported g and a measurable first-quadrant set satisfying r²+z² ≥ R² with R > 0, the function rg²/(r²+z²) is integrable on that set. (`ratio_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L328)).

**Integrability of cylindrical weights.** Proved result. The cylindrical inverse-square term is integrable. (`axis_integrable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L346)).

**From real integrals to lower integrals.** Proved result. The real integral estimate gives a lower integral bound. (`to_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L369)).

**The axial square-exterior inequality.** Proved result. For positive exterior radius, twice the weighted inverse-square integral is bounded by the radial and height derivative energies of a compactly supported C¹ function vanishing on the horizontal boundary. (`axial_main`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L384)).

**Transverse square-exterior inequality.** Proved result. For positive exterior radius, the transverse inverse-square estimate adds the cylindrical inverse-square term to gradient energy for compactly supported C¹ functions vanishing on the axis. (`transverse_main`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L512)).

**The axial exterior estimate.** Proved result. The axial square-exterior inverse-square estimate holds for compactly supported C¹ functions vanishing on the horizontal boundary. (`squareExteriorAxialSmoothStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L589)).

**The transverse exterior estimate.** Proved result. The transverse square-exterior inverse-square estimate holds for compactly supported C¹ functions vanishing on the axis. (`squareExteriorTransverseSmoothStatement`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmooth.lean#L598)).

### Breakdown.CertCell.TailSquareSmoothing

This file constructs a radial unit-mass smoothing kernel that preserves rotations and reflection, together with the energy and cutoff bounds needed for weak limits. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The scalar bump profile.** Definition. The scalar bump profile has inner radius one and outer radius four before composition with squared spatial radius. (`profile`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L17)).

**A radial smooth bump from squared radius.** Definition. The radial bump evaluates the scalar bump profile at the squared spatial norm. (`roundBump`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L19)).

**The radial bump is infinitely smooth.** Proved result. The radial bump used for smoothing is smooth on all of R³. (`roundBump_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L21)).

**The radial bump is nonnegative.** Proved result. The radial bump is nonnegative at every spatial point. (`roundBump_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L24)).

**The radial bump is at most one.** Proved result. The radial bump is bounded above by one at every spatial point. (`roundBump_le_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L26)).

**The radial bump equals one inside.** Proved result. The radial bump equals one throughout the closed unit ball. (`roundBump_eq_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L28)).

**The radial bump vanishes outside.** Proved result. The radial bump vanishes at every point with |y| ≥ 2. (`roundBump_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L34)).

**The radial bump has compact support.** Proved result. The radial bump has compact closed support in R³. (`roundBump_hasCompactSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L40)).

**The radial bump at scale s.** Definition. The scaled radial bump evaluates the unscaled bump at the position divided by s. (`scaledBump`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L44)).

**The scaled bump is infinitely smooth.** Proved result. For every real s, the rescaled radial bump is smooth as a function of y ∈ R³. (`scaledBump_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L46)).

**Linear isometries keep the scaled bump.** Proved result. Linear isometries preserve the scaled bump. (`scaledBump_isometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L49)).

**The scaled bump equals one inside.** Proved result. For positive scale s, the scaled bump equals one throughout the closed ball of radius s. (`scaledBump_eq_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L53)).

**The scaled bump vanishes outside.** Proved result. For s > 0, the rescaled bump vanishes wherever |y| ≥ 2s. (`scaledBump_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L59)).

**The scaled bump has compact support.** Proved result. For every positive scale s, the rescaled bump has compact support in R³. (`scaledBump_hasCompactSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L65)).

**The total mass of the radial bump.** Definition. The bump mass is the spatial integral of the unscaled radial bump. (`bumpMass`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L69)).

**The radial bump has positive mass.** Proved result. The integral of the unscaled radial bump over R³ is strictly positive. (`bumpMass_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L71)).

**The normalized radial smoothing kernel.** Definition. The normalized smoothing kernel divides the scaled radial bump by s cubed times the unscaled bump mass. (`roundKernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L75)).

**Smoothing kernel is infinitely smooth.** Proved result. For every real scale s, the normalized radial smoothing kernel is smooth on R³. (`roundKernel_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L77)).

**The smoothing kernel is nonnegative.** Proved result. At every positive scale, the radial smoothing kernel is nonnegative everywhere. (`roundKernel_nonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L80)).

**The smoothing kernel has compact support.** Proved result. At every positive scale, the radial smoothing kernel has compact support. (`roundKernel_hasCompactSupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L83)).

**Linear isometries preserve the kernel.** Proved result. The radial smoothing kernel is unchanged by every linear isometry of R³, at every scale. (`roundKernel_isometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L87)).

**The smoothing kernel has mass one.** Proved result. At every positive scale s, the radial smoothing kernel has integral one over R³. (`roundKernel_integral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L91)).

**The smoothing kernel bound.** Proved result. For positive scale s, the normalized radial smoothing kernel is at most the reciprocal of s cubed times the unscaled bump mass. (`roundKernel_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L99)).

**Nonzero kernel values lie in radius 2s.** Proved result. Nonzero kernel values lie within radius 2s. (`norm_lt_of_roundKernel_ne`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L103)).

**Smoothing converges almost everywhere.** Proved result. For a locally integrable vector field w, convolution with the radial kernel at scales 1/(n+1) converges to w at almost every spatial point. (`ae_tendsto_roundKernel`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L108)).

**Matrix square energy is nonnegative.** Proved result. The squared Frobenius norm of every real 3 × 3 matrix is nonnegative. (`matSq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L142)).

**Matrix square energy is continuous.** Proved result. The squared Frobenius norm depends continuously on the entries of a real matrix. (`continuous_matSq'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L145)).

**Averages obey the squared-norm bound.** Proved result. For a nonnegative integrable density ρ of mass one, if ρv and ρ|v|² are integrable, then |∫ρv|² ≤ ∫ρ|v|². (`sq_norm_average_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L149)).

**Sixth powers lie above their tangent.** Proved result. For r,a ≥ 0, the tangent-line bound a⁶+6a⁵(r−a) ≤ r⁶ holds. (`sixth_le_tangent'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L170)).

**Averages obey the sixth-power bound.** Proved result. For a nonnegative integrable density ρ of mass one, if ρv and ρ|v|⁶ are integrable, then |∫ρv|⁶ ≤ ∫ρ|v|⁶. (`sixth_norm_average_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L180)).

**Smooth the weak-gradient columns.** Proved result. For a smooth compactly supported kernel, each coordinate derivative of the smoothed field equals convolution with the corresponding weak-gradient column. (`fderiv_smoothing_column`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L210)).

**Smoothing bounds gradient energy.** Proved result. A nonnegative smooth compactly supported kernel of mass one bounds the smoothed weak-gradient energy by the convolution of the original gradient energy. (`matSq_fderiv_smoothing_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L243)).

**Smoothing bounds sixth powers.** Proved result. A nonnegative smooth compactly supported kernel of mass one bounds the sixth power of the smoothed field by the smoothed sixth power when both the field and its sixth power are locally integrable. (`norm_smoothing_sixth_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L279)).

**Smoothing respects linear isometries.** Proved result. Smoothing commutes with linear isometries. (`smoothing_isometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L292)).

**Coordinate signs of point reflection.** Proved result. The spatial reflection fixes the first coordinate and negates the second and third coordinates. (`flipPoint_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L306)).

**Coordinate equalities determine a vector.** Proved result. Two vectors in R³ are equal if their three Cartesian coordinates agree. (`flipPoint_ext`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L310)).

**Point reflection as a linear map.** Definition. The point reflection is packaged as a real linear map. (`flipLinear`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L314)).

**Point reflection is an involution.** Proved result. Applying (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃) twice returns the original vector. (`flipPoint_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L327)).

**Point reflection preserves the norm.** Proved result. The half-turn (y₁,y₂,y₃) ↦ (y₁,−y₂,−y₃) preserves Euclidean norm. (`norm_flipPoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L332)).

**Point reflection as a linear isometry.** Definition. The norm-preserving involutive point reflection is packaged as a linear isometric equivalence. (`flipIsometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L337)).

**Flip isometry matches the point map.** Proved result. The reflection isometry matches the point map. (`flipIsometry_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L341)).

**Axial rotation as a linear isometry.** Proved result. Axial rotation has a linear-isometry model. (`exists_rotationIsometry`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L343)).

**Scaled bumps are rotation invariant.** Proved result. For every scale s and angle ψ, the rescaled radial bump has the same value at Rψy and y. (`scaledBump_axialRot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L346)).

**Scaled bumps are reflection invariant.** Proved result. For every scale s, the rescaled radial bump has the same value at the half-turned point (y₁,−y₂,−y₃) and at y. (`scaledBump_flip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L350)).

**Bump derivatives use inverse scaling.** Proved result. The scaled bump derivative is the original bump derivative at the reciprocally scaled point, precomposed with multiplication by the totalized reciprocal scale. (`fderiv_scaledBump`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L353)).

**The unscaled bump derivative is bounded.** Proved result. The derivative of the unscaled radial bump has a single global finite norm bound. (`exists_fderiv_roundBump_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L360)).

**Scaled bump derivative is bounded by M/s.** Proved result. At positive scale s, a derivative bound M for the unscaled radial bump gives bound M/s for the scaled bump derivative. (`norm_fderiv_scaledBump_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L364)).

**Bump derivative vanishes below its scale.** Proved result. For positive scale s, the scaled bump derivative vanishes at every point of norm strictly less than s. (`fderiv_scaledBump_eq_zero_of_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L378)).

**Bump derivative vanishes beyond 2s.** Proved result. For positive scale s, the scaled bump derivative vanishes at every point of norm strictly greater than twice s. (`fderiv_scaledBump_eq_zero_of_gt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L385)).

**Weighted squares split an error.** Proved result. For δ > 0, the norm of a sum satisfies ‖a+b‖² ≤ (1+δ)‖a‖²+(1+δ⁻¹)‖b‖². (`norm_add_sq_le_split`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L392)).

**A cutoff has a controlled gradient cost.** Proved result. For positive δ, multiplying a C¹ field by the cutoff bounds gradient energy by (1+δ) times the field's gradient energy plus 3(1+1/δ) times cutoff-gradient squared times field-norm squared. (`matSq_fderiv_cutoff_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L403)).

**A linear bound by a shifted cubic.** Proved result. For nonnegative u and positive a, u is at most a plus u cubed divided by a squared. (`le_add_cube_div_sq'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L441)).

**Cutoff gradient error has a tail bound.** Proved result. If |Dχ| ≤ M for the unscaled bump, R,s > 0 and W is C¹ with finite sixth-power integral, then |DχR|²|W|² is integrable and its integral is at most M²[8|B₁|s+s⁻²∫|y|≥R|W|⁶]. (`integral_fderiv_scaledBump_sq_mul_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L452)).

**Cylindrical radius is one-Lipschitz.** Proved result. The cylindrical radius satisfies r(x) ≤ r(t)+|x−t|, where r(y) = √(y₁²+y₂²). (`axialRadius_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L520)).

**Distance bounds coordinate increases.** Proved result. A coordinate of one point is at most the same coordinate of another point plus the distance between them. (`coord_sub_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L545)).

**Cylindrical radius is continuous.** Proved result. The cylindrical radius y ↦ √(y₁²+y₂²) is continuous on R³. (`continuous_axialRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L551)).

**Coordinate projection is continuous.** Proved result. Every Cartesian coordinate projection y ↦ yⱼ is continuous on R³. (`continuous_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L554)).

**Coordinate planes have zero volume.** Proved result. Each coordinate plane {y : yⱼ = 0} has three-dimensional Lebesgue measure zero. (`volume_coord_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareSmoothing.lean#L557)).

### Breakdown.CertCell.TailSquareTransfer

This file lifts the planar axial and transverse inequalities to three-dimensional fields using cylindrical integration and the symmetry-imposed boundary zeros. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Axial rotation as a bounded linear map.** Definition. The axial rotation is packaged as a continuous linear map through its linear isometry. (`rotL`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L25)).

**Linear rotation matches point rotation.** Proved result. The linear map representing axial rotation through θ acts on every vector exactly as the spatial rotation Rθ. (`rotL_apply`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L27)).

**Negative rotation is a left inverse.** Proved result. For every θ and y, rotating by θ and then by −θ returns y. (`rot_neg_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L29)).

**Negative rotation is a right inverse.** Proved result. For every θ and y, rotating by −θ and then by θ returns y. (`rot_rot_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L32)).

**The meridian embedding as a linear map.** Definition. The meridian embedding sends a planar pair to radius times the first unit vector plus height times the third. (`planeL`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L35)).

**The meridian embedding is linear.** Proved result. The meridian embedding (r,z) ↦ (r,0,z) agrees with its linear-map representation. (`planePoint_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L39)).

**The first meridian coordinate is radius.** Proved result. The first Cartesian coordinate of the meridian embedding (r,0,z) is r. (`planePoint_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L43)).

**The second spatial coordinate is zero.** Proved result. The second Cartesian coordinate of every embedded meridian point is zero. (`planePoint_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L46)).

**The third meridian coordinate is height.** Proved result. The third Cartesian coordinate of the meridian embedding (r,0,z) is z. (`planePoint_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L49)).

**The radial plane basis embeds as e₀.** Proved result. The radial coordinate direction (1,0) in the meridian plane maps to the first Cartesian unit vector e₁. (`planeL_fst`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L52)).

**The height plane basis embeds as e₂.** Proved result. The height direction (0,1) in the meridian plane maps to the third Cartesian unit vector e₃. (`planeL_snd`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L55)).

**The plane square exterior is measurable.** Proved result. For any R, the square exterior {r,z > 0 : r > R or z > R} is a measurable meridian set. (`measurableSet_planeSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L58)).

**Spatial square exterior is measurable.** Proved result. The spatial preimage of the meridian square exterior under y ↦ (√(y₁²+y₂²),y₃) is measurable. (`measurableSet_spaceSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L65)).

**The square exterior has positive radius.** Proved result. Every point of the meridian square exterior has strictly positive radial coordinate. (`planeSquare_sub`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L69)).

**Rotations preserve the spatial exterior.** Proved result. A spatial point lies in the lifted square exterior exactly when any axial rotation of it lies there. (`mem_spaceSquare_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L72)).

**Meridian embedding of exterior regions.** Proved result. Meridian embedding preserves exterior membership. (`planePoint_mem`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L79)).

**Cylindrical reduction by axisymmetry.** Proved result. Axisymmetric integrals reduce cylindrically. (`lintegral_cyl_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L84)).

**Rotation preserves meridian projection.** Proved result. Rotating a point about the axis leaves its meridian projection (√(y₁²+y₂²),y₃) unchanged. (`pointPlane_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L106)).

**Projecting positive meridian points back.** Proved result. Positive-radius meridian points project back. (`pointPlane_planePoint`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L112)).

**Meridian projection is measurable.** Proved result. The map from a spatial point to its cylindrical radius and height is measurable. (`measurable_pointPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L116)).

**Point angle reconstructs a spatial point.** Proved result. Embedding a point's meridian projection and rotating it through its horizontal polar angle reconstructs the original spatial point, including points on the axis. (`rot_pointAngle`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L120)).

**The axis has zero planar measure.** Proved result. Almost every planar point has nonzero first coordinate. (`ae_ne_line`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L139)).

**Lifting a.e. plane facts to space.** Proved result. A property holding almost everywhere in the positive-radius plane holds almost everywhere after cylindrical projection from space. (`ae_pointPlane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L145)).

**Rotation-invariant spatial facts descend.** Proved result. An axial-rotation-invariant property holding almost everywhere in space holds almost everywhere on the positive-radius meridian section. (`ae_planePoint_of_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L174)).

**Reducing exterior integrals to the plane.** Proved result. Exterior spatial integrals reduce to the plane. (`lintegral_spaceSquare_ae`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L187)).

**Matrix square energy is continuous.** Proved result. The squared Frobenius norm is continuous as a function of a real linear map R³ → R³. (`continuous_matSq_map`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L214)).

**The meridian radius is continuous.** Proved result. The meridian radius √(r²+z²) is continuous in r and z. (`continuous_planeRadius`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L217)).

**Vector square norm is a coordinate sum.** Proved result. For v ∈ R³, its squared norm is v₁²+v₂²+v₃². (`norm_sq_coord`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L221)).

**Matrix energy as a sum over columns.** Proved result. Matrix square energy is a sum over columns. (`matSq_three`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L225)).

**Rotating the first unit vector backward.** Proved result. Rotation by minus θ sends the first basis vector to cos θ times the first basis vector minus sin θ times the second. (`rot_neg_e0`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L229)).

**Rotating the second unit vector backward.** Proved result. Rotation by minus θ sends the second basis vector to sin θ times the first basis vector plus cos θ times the second. (`rot_neg_e1`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L234)).

**Inverse rotation fixes e₂.** Proved result. Rotation through −θ about the third coordinate axis fixes the axial unit vector e₃. (`rot_neg_e2`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L239)).

**Rotation conjugacy keeps matrix energy.** Proved result. Rotation conjugacy preserves matrix energy. (`matSq_conj`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L243)).

**Rotation covariance transports gradients.** Proved result. If w is differentiable and satisfies w(Rθy) = Rθw(y), then Dw(Rθy) = RθDw(y)R₋θ. (`fderiv_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L255)).

**Rotation has its angular tangent.** Proved result. At angle zero, differentiating axial rotation of (y₀,y₁,y₂) gives the vector (-y₁,y₀,0). (`hasDerivAt_rot`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L267)).

**Covariance from angular differentiation.** Proved result. Angular field differentiation gives covariance. (`fderiv_perp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L279)).

**Angular gradient energy on the meridian.** Proved result. For a differentiable rotation-covariant field at nonzero meridian radius, the angular derivative's squared norm is the sum of the first two component squares divided by radius squared. (`col_one`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L292)).

**Plane restriction is linear composition.** Proved result. Restricting component a of w to the meridian plane equals composing w with the linear embedding (r,z) ↦ (r,0,z) and then taking component a. (`plane_comp`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L306)).

**Differentiate a meridian restriction.** Proved result. Restricting a differentiable field to the meridian plane differentiates it in the embedded direction (q₁,0,q₂) and then takes the selected output component. (`fderiv_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L312)).

**Plane restrictions of C¹ fields are C¹.** Proved result. If w is C¹ on R³, each Cartesian component of its restriction w(r,0,z) is C¹ on R². (`contDiff_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L320)).

**Plane restrictions keep compact support.** Proved result. Plane restrictions preserve compact support. (`compact_plane`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L325)).

**Reflection reverses the third coordinate.** Proved result. The third Cartesian component of the half-turn of v is −v₃. (`flipPoint_two`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L335)).

**Axial fields vanish on the flip plane.** Proved result. Axial fields vanish on the reflection plane. (`axial_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L338)).

**Half-turns fix points on the axis.** Proved result. Rotation through π about the third coordinate axis fixes every point (0,0,z). (`rot_pi_axis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L348)).

**Transverse components vanish on the axis.** Proved result. If a vector field is covariant under every axial rotation, its first two Cartesian components vanish at every point of the rotation axis. (`trans_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L352)).

**Weighted square integrand is measurable.** Proved result. For continuous f on the meridian plane, the nonnegative part of rf(r,z)²/(r²+z²) is measurable. (`measurable_square_term`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L361)).

**Three coordinate inequalities sum.** Proved result. For nonnegative possibly infinite quantities, the three inequalities 2aⱼ ≤ bⱼ imply 2c(a₁+a₂+a₃) ≤ c(b₁+b₂+b₃). (`three_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L366)).

**Spatial bounds from planar estimates.** Proved result. The axial and transverse planar inverse-square estimates combine through cylindrical integration to bound twice the spatial square-exterior inverse-square energy by gradient energy. (`squareExteriorSpaceSmooth_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailSquareTransfer.lean#L376)).

### Breakdown.CertCell.TailStatements

This file states the tail absorption, angular, coefficient, off-mode and exterior contracts used to control the unresolved part of the cell form. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The tail budget remainder.** Definition. The tail remainder subtracts absorbed gradient, curl, velocity, potential, and leakage charges from the Hessian and curl-gradient tail gains. (`remainder`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L23)).

**Absorption of unresolved-mode tails.** Proposition definition. This proposition requires certified tail gains and nonnegative tail energies to bound the remainder below by the negative low-mode velocity charge. (`TailAbsorption`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L30)).

**The five-energy quadratic form.** Definition. The point quadratic combines five squared energy variables and subtracts the gradient-velocity cross term. (`quad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L42)).

**Coefficient bounds with cross terms.** Proposition definition. Coefficient domination means lower bounds for all five square coefficients and an upper bound for the subtracted cross coefficient. (`Dominates`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L46)).

**Pointwise quadratic nonnegativity test.** Proposition definition. This proposition requires passing pointwise coefficient tests and angular relations to make the five-energy quadratic nonnegative at positive radius. (`PointwiseQuadraticTest`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L56)).

**Pointwise coefficients from modes.** Definition. Mode coefficients become pointwise coefficients by matching the five energy terms and setting the cross coefficient to zero. (`ofMode`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L60)).

**Point coefficients for a labeled mode.** Definition. The point coefficients of a labeled mode are the coefficients obtained from the piece weights, harmonic bounds, scalar weight, and azimuthal order. (`modeCoef`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L68)).

**The quadratic density of a labeled mode.** Definition. The labeled quadratic evaluates the point quadratic on square roots of mode Hessian, curl-gradient, gradient, curl, and velocity energies. (`labelQuad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L72)).

**Mode density as a labeled quadratic.** Proved result. Mode density equals the labeled quadratic. (`modeTerm_eq_labelQuad`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L86)).

**Angular mode bounds on the half-plane.** Proposition definition. This proposition requires angular mode relations to hold almost everywhere on the half-plane for perturbations of positive period. (`AngularModeBounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L96)).

**Finite weighted label-gradient energy.** Proposition definition. This proposition requires every labeled mode gradient to have finite cylindrical-weighted square energy on the half-plane. (`LabelGradFinite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L103)).

**Uniform coefficient lower bounds.** Proposition definition. This proposition requires admissible weights and valid set-piece bounds to give coefficient domination throughout the specified mode set and region. (`UniformCoefficientBounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L114)).

**Soundness of off-mode conditions.** Proposition definition. This proposition requires certified off-mode conditions to make their charged densities nonnegative almost everywhere in the certified region. (`OffModeConditionSound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L122)).

**Reflection parity of a labeled velocity.** Proposition definition. Label reflection parity relates reflected-height velocity modes to the flipped harmonic label with the coordinate frame signs, almost everywhere on the half-plane. (`IsFlipEven`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L131)).

**Symmetry gives label reflection parity.** Interface. This proposition requires inclusion of the prescribed reflection symmetry to give almost-everywhere label reflection parity for positive-period perturbations. (`LabelFlipEvenHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L135)). Proof route: `Breakdown.CertCell.TailBand.labelFlipEvenHolds`.

**The ray-exterior inverse-square estimate.** Proposition definition. This proposition bounds cylindrical-weighted inverse-square velocity energy in a ray exterior by gradient energy, with a constant depending on angular frequency. (`ModeRayInverseSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L139)).

**Square-exterior inverse-square estimate.** Proposition definition. This proposition bounds twice the cylindrical-weighted inverse-square energy on a square exterior by gradient energy for zero-angular-frequency modes with reflection parity. (`ModeSquareInverseSquare`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L146)).

**Soundness of exterior conditions.** Proposition definition. This proposition requires certified exterior conditions, including reflection parity in the zero-frequency square case, to bound the negative density integral by the positive one. (`ExteriorConditionSound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L153)).

**Soundness from angular coefficient data.** Proved result. Angular mode inequalities, the pointwise quadratic test, and uniform coefficient domination imply nonnegative charged off-mode densities almost everywhere in their certified regions. (`offModeConditionSound_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TailStatements.lean#L164)).

### Breakdown.CertCell.ThreeHalves

This file combines line estimates in three coordinate directions and the three-slice inequality to prove the scalar three-halves gradient bound. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**A spatial point from three coordinates.** Definition. The coordinate constructor makes the three-dimensional Euclidean vector with the supplied first, second, and third coordinates. (`pt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L9)).

**The coordinate map preserves volume.** Proved result. The Cartesian coordinate map (x,y,z) ↦ xe₁+ye₂+ze₃ preserves three-dimensional Lebesgue measure. (`pt_preserving`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L11)).

**Coordinate substitution is measurable.** Proved result. If three real coordinate functions are measurable, the vector-valued function formed from those coordinates is measurable. (`measurable_pt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L26)).

**First-axis translation changes x only.** Proved result. Translating the vector (x,y,z) by te₁ changes its coordinates to (x+t,y,z). (`pt_add_first`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L31)).

**Second-axis translation changes y only.** Proved result. Translating the vector (x,y,z) by te₂ changes its coordinates to (x,y+t,z). (`pt_add_second`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L35)).

**Third-axis translation changes z only.** Proved result. Translating the vector (x,y,z) by te₃ changes its coordinates to (x,y,z+t). (`pt_add_third`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L39)).

**Spatial points are coordinate basis sums.** Proved result. Every vector with coordinates (x,y,z) equals xe₁+ye₂+ze₃. (`pt_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L43)).

**Spatial integration is a triple integral.** Proved result. For every nonnegative measurable function F on R³, its spatial integral equals the iterated integral ∫∫∫F(x,y,z)dz dy dx, allowing the value +∞. (`lintegral_space_eq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L48)).

**The two inner integrals may be swapped.** Proved result. For a nonnegative jointly measurable function of three real variables, the two inner integrations can be interchanged without changing the triple integral. (`swap_inner`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L58)).

**The two outer integrals may be swapped.** Proved result. For a nonnegative jointly measurable function of three real variables, the two outer integrations can be interchanged without changing the triple integral. (`swap_outer`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L65)).

**Real and lower integrals of positives.** Proved result. For a nonnegative real function, its real integral embedded into the nonnegative extended reals is at most its lower integral. (`ofReal_integral_le_lintegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L73)).

**Coordinate sum is bounded by the norm.** Proved result. The sum of the absolute values of a linear functional on the three unit coordinate vectors is at most the square root of three times its operator norm. (`sum_abs_apply_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L80)).

**Three-halves gradient estimate is proved.** Proved result. The three-slice and coordinate-line estimates bound the L to the power 3/2 norm of a compactly supported C¹ scalar function by its derivative L1 norm divided by 2√3. (`threeHalvesGradientBound_of`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/ThreeHalves.lean#L106)).

### Breakdown.CertCell.TopStatements

This file assembles the signed half-plane form, exterior terms, row and pair shares, normalized pressure and gauge-fixed tree state into the final cell-layer coercivity clause. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**The scalar terms in the coercive form.** Definition. The scalar form combines the weighted multiplier square and subtracts actuator pairings, row energy, and pin energy. (`formScalarWith`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L34)).

**Half-plane bound with separate constants.** Proposition definition. The half-plane condition requires a finite negative form part and the signed integral inequality with separate form and multiplier coercivity constants. (`HalfPlaneFormBoundWith`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L47)).

**The half-plane coercivity bound.** Proposition definition. The chosen half-plane bound uses the layer's coercivity for both the form and multiplier constants. (`HalfPlaneFormBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L59)).

**The real value of the signed form.** Definition. The real signed form value is the positive part minus the negative part minus the scalar form divided by 4π. (`formValueWith`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L62)).

**Finiteness of the negative form part.** Proposition definition. Negative-form finiteness requires the negative part to be finite for every admissible parameter and perturbation. (`FormNegFinite`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L68)).

**Nonnegativity of the signed form value.** Proposition definition. Form nonnegativity requires a nonnegative real signed value for admissible forcing whenever the positive form part is finite. (`FormValueNonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L72)).

**The form value of an admissible tuple.** Definition. An admissible tuple's value evaluates the signed form on its velocity, derivatives, multipliers, and forcing. (`value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L80)).

**Uniform mode-coefficient lower bounds.** Proposition definition. The coefficient lower-bound condition uses one constant for all modes and points, with the velocity coefficient multiplied by radius squared. (`CoefficientLowerBounds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L84)).

**Coefficient bounds give finite negatives.** Interface. This proposition requires coefficient lower bounds and a weak Hessian model to make the negative form finite when the azimuthal order is at least one. (`FormNegFiniteHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L97)). Proof route: `Breakdown.CertCell.formNegFinite`.

**A signed bound from form nonnegativity.** Proved result. Finite negative form and nonnegative real form value imply the signed half-plane inequality, including the case of an infinite positive part. (`halfPlaneFormBoundWith_of_value`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L102)).

**The actuator-multiplier pairing identity.** Interface. This proposition equates the period pairing of an actuator and multiplier field with the corresponding multiplier right-hand expression under admissibility and actuator assumptions. (`ActuatorPairingHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L128)). Proof route: `Breakdown.CertCell.actuatorPairing_of_solenoidal_and_gradient`, `Breakdown.CertCell.actuatorPairing_holds`.

**The positive exterior contribution.** Definition. The positive exterior contribution sums positive labeled densities and the positive averaged stretching density over the half-plane exterior. (`extPos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L137)).

**The negative exterior contribution.** Definition. The negative exterior contribution sums negative labeled densities and the negative averaged stretching density over the half-plane exterior. (`extNeg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L142)).

**Averaging the forcing with its flip.** Definition. Reflection averaging takes half the sum of the forcing and its reflected input-and-output field. (`flipAverage`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L147)).

**Zero off-mode negative cell terms.** Proposition definition. The off-mode condition requires every cell's negative off-mode contribution to be zero for admissible parameters and perturbations. (`OffModesVanish`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L159)).

**A finite nonnegative exterior term.** Proposition definition. Exterior nonnegativity requires the negative exterior contribution to be finite and at most the positive contribution. (`ExteriorNonneg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L163)).

**Row shares recover the global row term.** Proposition definition. Row-share matching identifies the sum of cell row shares with the coercivity-weighted global row square divided by 4π. (`RowSharesMatch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L167)).

**Pair shares are at most global pairing.** Proposition definition. Pair-share control bounds the cell pairings by actuator and pin pairings, a multiplier error budget, and strain slack. (`PairSharesBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L171)).

**Credit leaves are at most cell credits.** Proposition definition. Credit-leaf control bounds twice the sum of credit quadratic forms by the cell credit shares. (`CreditLeavesBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L178)).

**Recovery of a periodic pressure gradient.** Proposition definition. Pressure recovery requires the reflected forcing residual after subtracting the perturbation, diffusion, coupling, and actuator terms to be a periodic pressure gradient. (`PressureRecovered`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L183)).

**Initial state bounds from cell estimates.** Interface. This proposition combines cell form bounds, exterior and off-mode control, shares, credits, and the multiplier error budget into the initial state bound. (`InitialStateHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L195)). Proof route: `Breakdown.CertCell.Assembly.initialStateHolds_of_split`, `Breakdown.CertCell.Assembly.initialStateHolds_of_formSplit`, `Breakdown.CertCell.initialState_closed`.

**Tree reduction gives form nonnegativity.** Proposition definition. Tree reduction is the implication from pressure recovery and the initial state bound to nonnegativity of the real signed form. (`TreeReduction`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L205)).

**Row shares from instance rows.** Interface. This proposition requires the instance row-class theorem, a valid instance entry, and a mode-class symmetry to imply global row-share matching. (`RowSharesOfInstanceHolds`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L208)). Proof route: `Breakdown.CertCell.Internal.RowShares.rowSharesOfInstance_of_regular`, `Breakdown.CertCell.rowSharesOfInstance`.

**The chosen pressure-gradient field.** Definition. The chosen pressure field is the reflection-averaged forcing minus the perturbation, diffusion, model coupling, and actuator residual. (`chosenPressure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L213)).

**A potential normalized by its ball mean.** Definition. The head potential subtracts the average of the selected potential over the unit ball. (`headPotential`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L218)).

**The normalized potential's pressure mode.** Definition. The head pressure mode takes the layout's pressure Fourier mode of the mean-normalized potential. (`headPressure`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L221)).

**Cell-head data with normalized pressure.** Definition. Head data replace pressure-segment moments with moments of the mean-normalized pressure potential and retain the other true layout data. (`headData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L224)).

**Complex head data from real harmonics.** Definition. Complex harmonic head data add the cosine-tuple data to i times the sine-tuple data. (`headHarmonic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L229)).

**Values of all skeleton keys.** Definition. Skeleton values evaluate velocity, gradient, pressure, corner, and stream moments, with the private placeholder assigned zero. (`keyValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L233)).

**Complex harmonic skeleton-key values.** Definition. Complex harmonic skeleton values add the cosine-tuple value to i times the sine-tuple value. (`keyHarmonic`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L250)).

**The matrix of deleted-key gauge values.** Definition. The gauge matrix evaluates each gauge direction on each deleted skeleton key. (`gaugeMatrix`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L259)).

**Gauge coefficients by matrix inversion.** Definition. Gauge coefficients are the negative inverse-matrix contraction of the deleted-key harmonic values. (`fieldGauge`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L262)).

**Gauge coefficients of admissible tuples.** Definition. An admissible tuple's gauge coefficients use its velocity and derivatives together with the chosen pressure residual. (`gaugeValue`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L267)).

**The head vector for a cell.** Definition. A cell head vector inserts harmonic head data and multiplier coordinates and assigns zero to the other index branches. (`fieldHead`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L270)).

**The gauge-shifted cell-head vector.** Definition. The shifted cell-head vector adds the gauge coefficients times the corresponding gauge directions. (`fieldShifted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L276)).

**The gauge-shifted skeleton-key value.** Definition. The shifted skeleton value adds the gauge coefficients times their skeleton-key directions to the harmonic key value. (`fieldKey`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L281)).

**Real values of selected tree data.** Definition. Tree data select a real or imaginary shifted cell value, a multiplier coordinate, or a shifted skeleton value, and default to zero when none applies. (`fieldData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L286)).

**Cell-head state of an admissible tuple.** Definition. The head state evaluates the cell-head vector on an admissible tuple and its chosen pressure field. (`headState`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L300)).

**The shifted state of an admissible tuple.** Definition. The shifted state evaluates the gauge-shifted cell-head vector on an admissible tuple and its chosen pressure field. (`shiftedState`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L304)).

**The actual real data in the tree.** Definition. The true tree data evaluate the selected real tree coordinates on an admissible tuple. (`trueData`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L308)).

**The signed-state tree certificate.** Definition. The signed-state certificate combines the tree's slaved and free coordinates, base point, true data, free map, and quadratic tree. (`certificate`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L311)).

**A valid tree state from initial bounds.** Proposition definition. This proposition requires pressure recovery and the initial bound to produce a nonpositive base value and a valid signed state for every tree front. (`TreeStateFromInitial`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L324)).

**Form nonnegativity from the tree state.** Proved result. A certified tree satisfying the tree conditions and the initial-to-state implication turns recovered pressure and the initial bound into nonnegative signed form value. (`treeReduction_of_tree`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L333)).

**The cell-level assembly junctions.** Proposition structure. The cell junction package requires vanishing off-modes, a nonnegative exterior, pressure recovery, cell residual bounds, and a tree state from the initial bound. (`CellJunctions`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L342)).

**Coefficient bounds from entry conditions.** Proved result. Certified coefficient entries, matching coercivity, and uniform weak admissibility yield one uniform lower bound for all mode coefficients, weighting the velocity coefficient by radius squared. (`coefficientLowerBounds_of_entries`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L350)).

**Junction facts for a whole cell layer.** Proposition structure. The layer junction package records admissibility, reflection, actuator shapes, and a reflection-invariant weak Hessian model. (`LayerJunctionFacts`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L383)).

**Instance consequences of cell hypotheses.** Proved result. Cell hypotheses give instance consequences. (`instanceConsequences_of_hypothesis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L391)).

**Uniform admissibility from cell data.** Proved result. Cell hypotheses give uniform admissibility. (`admissible_of_hypothesis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L396)).

**The pair-share error budget.** Proved result. Cell hypotheses give a pair-share error budget. (`pairSharesBound_of_hypothesis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L406)).

**Cell hypotheses bound the credit leaves.** Proved result. Assuming the credit-leaf estimate, the cell hypotheses imply that twice the sum of the credit quadratic forms is bounded by the sum of the cell credit shares, for every admissible perturbation and auxiliary credit data. (`creditLeavesBound_of_hypothesis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L419)).

**Cell hypotheses identify the density.** Proved result. Assuming the mode-density identity, realization estimates and chart bounds, the cell hypotheses and junction conditions identify the positive and negative space-time density integrals separately as 4π times their meridian form integrals. (`densityIdentity_of_hypothesis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L485)).

**Cell hypotheses give all layer junctions.** Proved result. Assuming the ordinary and scaled jet construction results, the cell hypotheses and shape-value identities give the shape admissibility and reflection laws, actuator shape properties, model half-turn symmetry and a decaying weak model Hessian. (`layerJunctionFacts_of_hypothesis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L500)).

**The row-rest clause from cell data.** Proved result. The cell hypothesis gives the row-rest clause. (`rowRestClause_of_cellHypothesis`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L509)).

**The cell layer gives extended coercivity.** Proved result. Suppose cell feasibility, matching, matrix-tree positivity and error budgets hold on a valid mesh with azimuthal order ≥3, spatial weight 39/50, coercivity c = 3/50, pin weight p = 1000 and maximum row weight 400(1+2⁻¹⁸), with parameter-independent model, coefficient data and harmonic bounds apart from permitted frame changes, uniform weak admissibility with bounds ε, ε′, ρ and lower weight w₀, profile and derivative enclosures, finite negative-part density integrals, cell-to-density identities, row bounds, nonnegative adjoint radii, an upper weight bound, and measurable periodic actuators satisfying their L² and pairing bounds. If C₂ ≥ √((1+ε+ε′/√w₀)²/c+ρ/cμ)/√c and Cpin ≥ √(p/c), every admissible perturbation v, multiplier κ and measurable periodic L² forcing F satisfying the extended linearized weak equation at any allowed parameter obeys √(E(v)+m²|κ|²) ≤ C₂‖F‖L²([0,1]×ℝ³)+rows(F)+Cpin|pins(∇v)|, where E(v)=∫₀¹∫(|Δv|²+(39/50)|∇v|²), derivatives are weak, cμ is the piece multiplier coefficient, m is the certificate multiplier weight, and measurability is understood up to null sets. (`extendedCoerciveClause_of_cellLayer`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TopStatements.lean#L526)).

### Breakdown.CertCell.TraceFlip

This file derives reflection of weak traces from the established trace-matching contract. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Weak traces respect reflection.** Proved result. For arbitrary complex-valued f,g and scalar s, the upper trace expression formed from sf(−z) and −sg(−z) equals s times the lower trace expression formed from f and g. (`traceFlip`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceFlip.lean#L11)).

### Breakdown.CertCell.TraceHeight

This file represents a weak height derivative by an absolutely continuous primitive and shows that the trace formula recovers its integration constant. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Linear components keep the weak identity.** Proved result. Linear components preserve the weak identity. (`weak_identity_component`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceHeight.lean#L15)).

**Interior intervals inherit integrability.** Proved result. If f is integrable on (l,r) and l ≤ a ≤ b < r, then f is integrable over the oriented interval from a to b. (`interval_integrable_inside`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceHeight.lean#L48)).

**Primitives for weak derivatives a.e..** Proved result. Weak height derivatives have primitives almost everywhere. (`weak_primitive_representative`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceHeight.lean#L54)).

**Primitive integral has a linear weight.** Proved result. For h > 0 and integrable g on (0,h], the primitive identity ∫₀ʰ∫₀ᶻg(s)ds dz = ∫₀ʰ(h−s)g(s)ds holds. (`integral_primitive_eq_weighted`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceHeight.lean#L76)).

**Primitive constants from upper traces.** Proved result. The upper trace recovers the primitive constant. (`upperTrace_primitive`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceHeight.lean#L114)).

**Weak height traces from primitives.** Proved result. A weak height derivative recovers the height-trace relation through its almost-everywhere primitive. (`traceHeight`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceHeight.lean#L143)).

### Breakdown.CertCell.TraceMatch

This file approximates a symmetric hat function by smooth tests to show that weak traces taken from opposite sides agree. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Smooth approximation to positive parts.** Definition. The ramp profile multiplies its argument by the smooth transition from zero to one. (`rampProfile`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L14)).

**The ramp profile is infinitely smooth.** Proved result. The smooth ramp used to approximate the trace test has derivatives of every order on R. (`rampProfile_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L16)).

**The ramp profile is zero below zero.** Proved result. The smooth ramp vanishes for every x ≤ 0. (`rampProfile_of_nonpos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L19)).

**The ramp profile equals z above one.** Proved result. The smooth ramp equals x for every x ≥ 1. (`rampProfile_of_one_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L22)).

**The ramp derivative is zero below zero.** Proved result. The derivative of the smooth ramp is zero for x < 0. (`deriv_rampProfile_of_neg`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L25)).

**The ramp derivative is one above one.** Proved result. The derivative of the smooth ramp is one for x > 1. (`deriv_rampProfile_of_one_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L31)).

**The ramp derivative is globally bounded.** Proved result. The absolute derivative of the ramp profile has one finite bound valid on the whole real line. (`deriv_rampProfile_bound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L37)).

**The rescaled smooth ramp.** Definition. The smooth ramp at width ε is ε times the base ramp evaluated at the argument divided by ε. (`rampAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L51)).

**The rescaled ramp is infinitely smooth.** Proved result. For every real scale ε, the rescaled ramp is smooth on R. (`rampAt_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L53)).

**Differentiating the rescaled ramp.** Proved result. For positive smoothing width, the rescaled ramp derivative is the profile derivative at the argument divided by that width. (`rampAt_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L56)).

**The rescaled ramp is zero below zero.** Proved result. For ε > 0, the rescaled ramp vanishes on z ≤ 0. (`rampAt_of_nonpos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L68)).

**Rescaled ramp equals z beyond its width.** Proved result. For ε > 0, the rescaled ramp equals z whenever z ≥ ε. (`rampAt_of_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L71)).

**The rescaled ramp is bounded by |z|.** Proved result. For positive smoothing width, the absolute value of the rescaled ramp is at most the absolute value of its argument. (`abs_rampAt_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L76)).

**The step function at zero.** Definition. The step function is one for positive arguments and zero otherwise. (`stepFn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L84)).

**The step function is monotone.** Proved result. The step function that is zero for z ≤ 0 and one for z > 0 is nondecreasing. (`stepFn_monotone`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L86)).

**The smooth symmetric hat approximation.** Definition. The smooth symmetric hat takes the second centered difference of the smooth ramp and divides by the hat width. (`hatApprox`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L95)).

**The piecewise linear symmetric hat.** Definition. The piecewise linear hat takes the second centered difference of the positive-part function and divides by the hat width. (`hatFn`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L98)).

**Piecewise constant symmetric hat slope.** Definition. The hat slope takes the second centered difference of the step function and divides by the hat width. (`hatSlope`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L100)).

**The weak pairing with a symmetric hat.** Definition. The weak hat pairing is the function times the hat slope plus its candidate derivative times the hat value. (`hatPairing`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L102)).

**The smooth hat is infinitely smooth.** Proved result. For every real h and ε, the regularized hat function is smooth on R. (`hatApprox_contDiff`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L105)).

**The three-term smooth hat slope.** Proved result. The smooth hat derivative is the difference of three shifted ramp slopes with coefficients one, minus two, and one, divided by the hat width. (`hatApprox_hasDerivAt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L112)).

**The three-term smooth hat derivative.** Proved result. The derivative of the smooth hat equals its three shifted ramp derivatives with coefficients one, minus two, and one, divided by the hat width. (`deriv_hatApprox`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L126)).

**Smooth hat vanishes outside its support.** Proved result. For h,ε > 0, the regularized hat vanishes outside [−h,h+ε]. (`hatApprox_eq_zero`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L131)).

**A support interval for the smooth hat.** Proved result. For positive hat and smoothing widths, the smooth hat's support is contained in [−h,h+ε]. (`hatApprox_tsupport`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L142)).

**Uniform smooth hat derivative bounds.** Proved result. For positive hat and smoothing widths, a global ramp-slope bound M gives smooth-hat derivative bound 4M/h. (`abs_deriv_hatApprox_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L148)).

**The smooth hat has a uniform bound.** Proved result. For h,ε > 0, the regularized hat has absolute value at most 10 throughout −2h < z < 2h. (`abs_hatApprox_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L157)).

**The smoothing scale is positive.** Proved result. For h > 0 and n ≥ 0, the smoothing width h/(n+2) is positive. (`seq_pos`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L169)).

**Smoothing scale is below its upper bound.** Proved result. For h > 0 and n ≥ 0, the smoothing width h/(n+2) is strictly less than h. (`seq_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L171)).

**Smoothing scale eventually becomes small.** Proved result. For every positive w, h/(n+2) < w for all sufficiently large integers n. (`seq_eventually_lt`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L175)).

**Smooth ramps approach the positive part.** Proved result. Smooth ramps eventually match the positive part. (`rampAt_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L185)).

**Ramp derivatives approach the step.** Proved result. Ramp derivatives eventually match the step. (`rampSlope_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L193)).

**Smooth hats approach the hat function.** Proved result. Smooth hats eventually match the hat function. (`hatApprox_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L202)).

**Smooth hat slopes approach the hat slope.** Proved result. Smooth hat slopes eventually match the hat slope. (`deriv_hatApprox_eventually`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L208)).

**The hat pairing vanishes on the left.** Proved result. For h > 0, the weak pairing built from the hat function and its slope vanishes at every z ≤ −h. (`hatPairing_outer_left`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L215)).

**The hat pairing vanishes on the right.** Proved result. For h > 0, the weak pairing built from the hat function and its slope vanishes at every z > h. (`hatPairing_outer_right`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L228)).

**The lower weak hat pairing.** Proved result. On the negative half of a positive-width hat, the pairing is the derivative times 1+z/h plus the value divided by h. (`hatPairing_lower`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L241)).

**The upper weak hat pairing.** Proved result. On the positive half of a positive-width hat, the pairing is the derivative times 1−z/h minus the value divided by h. (`hatPairing_upper`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L257)).

**Absolute bound for the step function.** Proved result. The step function has absolute value at most 1. (`abs_stepFn_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L272)).

**The hat slope has a uniform bound.** Proved result. For h > 0, the piecewise slope of the hat test is bounded in absolute value by 4/h everywhere. (`abs_hatSlope_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L276)).

**The hat function has a uniform bound.** Proved result. For h > 0, the hat test has absolute value at most 10 on −2h < z < 2h. (`abs_hatFn_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L284)).

**The hat slope is measurable.** Proved result. For every real h, the piecewise slope of the hat test is measurable on R. (`hatSlope_measurable`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L290)).

**The hat function is continuous.** Proved result. For every real h, the hat test is continuous on R. (`hatFn_continuous`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L297)).

**Weak upper and lower traces match.** Proved result. If h > 0 and f has weak derivative f′ on (−2h,2h), the upper and lower weak traces at zero computed using width h agree. (`traceMatch`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TraceMatch.lean#L301)).

### Breakdown.CertCell.TripleSlice

This file proves the three-slice product estimate by repeated Cauchy-Schwarz for nonnegative integrals. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Cauchy-Schwarz for square-root products.** Proved result. For almost-everywhere measurable nonnegative extended-valued functions, the integral of their square-root product is at most the product of the square roots of their integrals. (`lintegral_sqrt_mul_sqrt_le`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TripleSlice.lean#L9)).

**The three-slice product bound is proved.** Proved result. For three nonnegative measurable functions depending on the coordinate pairs, the triple integral of their square-root product is at most the square root of the product of their three planar integrals. (`tripleSliceBound`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/TripleSlice.lean#L20)).

### Breakdown.CertCell.VelocitySixthIntegral

This file converts the weak sixth-power Sobolev bound into time integrability of the velocity L6 norm. Appendix B, weak cell calculus, exterior estimates, and the cell-to-tree coercivity route; the file is supporting library rather than a separate numbered paper claim.

**Matrix square energy is continuous.** Proved result. The squared Frobenius norm of a real 3 × 3 matrix is continuous in its entries. (`continuous_matSq`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/VelocitySixthIntegral.lean#L15)).

**Matrix square energy is nonnegative.** Proved result. The squared Frobenius norm of a real 3 × 3 matrix is nonnegative. (`matSq_nonneg'`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/VelocitySixthIntegral.lean#L19)).

**A sixth-root bound using a cube root.** Proved result. For every nonnegative extended-real number, its sixth root is at most one plus its cube root. (`rpow_sixth_le_one_add_rpow_third`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/VelocitySixthIntegral.lean#L23)).

**Real and finite positive integrals agree.** Proved result. Finite positive integrals match real integrals. (`ofReal_integral_eq_lintegral_of_lt_top`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/VelocitySixthIntegral.lean#L29)).

**Gradient energy controls the sixth root.** Proved result. The weak sixth-power estimate bounds the spatial L6 norm by one plus the nonnegative part of its constant times total weak-gradient energy when both energies are finite. (`sixth_root_le_of_gradient`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/VelocitySixthIntegral.lean#L35)).

**Finite time-integrated velocity L6 norm.** Proved result. Existence of a weak Sobolev bound ‖v‖₆² ≤ C‖∇v‖₂² implies that every admissible periodic perturbation satisfies ∫₀¹‖v(σ)‖₆dσ < ∞. (`velocitySixthIntegral`; [source](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/VelocitySixthIntegral.lean#L52)).
<!-- /passage:front -->

