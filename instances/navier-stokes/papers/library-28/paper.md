
<!-- passage:front -->
# Library guide 28: Breakdown/Uniqueness, Breakdown/Weak, Solution

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [proof routes](../navier-stokes-routes/paper.md) · [routes in detail](../navier-stokes-route-details/paper.md) · library guide: [1](../navier-stokes-library-01/paper.md) [2](../navier-stokes-library-02/paper.md) [3](../navier-stokes-library-03/paper.md) [4](../navier-stokes-library-04/paper.md) [5](../navier-stokes-library-05/paper.md) [6](../navier-stokes-library-06/paper.md) [7](../navier-stokes-library-07/paper.md) [8](../navier-stokes-library-08/paper.md) [9](../navier-stokes-library-09/paper.md) [10](../navier-stokes-library-10/paper.md) [11](../navier-stokes-library-11/paper.md) [12](../navier-stokes-library-12/paper.md) [13](../navier-stokes-library-13/paper.md) [14](../navier-stokes-library-14/paper.md) [15](../navier-stokes-library-15/paper.md) [16](../navier-stokes-library-16/paper.md) [17](../navier-stokes-library-17/paper.md) [18](../navier-stokes-library-18/paper.md) [19](../navier-stokes-library-19/paper.md) [20](../navier-stokes-library-20/paper.md) [21](../navier-stokes-library-21/paper.md) [22](../navier-stokes-library-22/paper.md) [23](../navier-stokes-library-23/paper.md) [24](../navier-stokes-library-24/paper.md) [25](../navier-stokes-library-25/paper.md) [26](../navier-stokes-library-26/paper.md) [27](../navier-stokes-library-27/paper.md) **28** [29](../navier-stokes-library-29/paper.md) [30](../navier-stokes-library-30/paper.md)

*A plain title and a sentence for each declaration in `Breakdown.Uniqueness.Basic` to `Solution` of Alpöge and Buckmaster's Lean at `ad53419de079eb8f95f60313473374624a348546`, in the authors' file order. Prepared with AI assistance. The authors have not reviewed it.*

Each paragraph names one declaration and says whether it is a definition, a proposition that the library defines (its name usually ends in `Holds` or `Statement`) or a proved result, then what it states. Click a paragraph to open its Lean on the right.
<!-- /passage:front -->

## Breakdown/Uniqueness

<!-- passage:sec-breakdown-uniqueness -->

### Breakdown.Uniqueness.Basic

This file fixes the bounded-energy smooth-solution obstruction and the local velocity-and-gradient bound used to compare physical solutions.

Reading context: §5 and Appendix A.2; the physical regularity and endpoint bridge.

**Source namespace:** Breakdown.

**Six is an admissible Lp exponent.** The exponent six satisfies the lower bound required to form an Lp space. Source: Breakdown.factOneLeSixExponent in Breakdown.Uniqueness.Basic, line 10. [Instance](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L10).

**Bounded velocity and gradient.** This proposition requires one bound for both the velocity and its derivative throughout the closed time interval. Source: Breakdown.GradientBoundedOn in Breakdown.Uniqueness.Basic, line 22. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L22).

**No global bounded-energy solution.** This proposition excludes a smooth solution with the prescribed initial data and one energy bound valid for all time. Source: Breakdown.NoBoundedSmoothSolution in Breakdown.Uniqueness.Basic, line 28. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L28).

**Radial cutoff.** The radial cutoff applies the smooth transition function to `2 - ‖x‖ / r`. Source: Breakdown.radialCutoff in Breakdown.Uniqueness.Basic, line 44. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Basic.lean#L44).

### Breakdown.Uniqueness.CubicTerm

This file estimates the cutoff cubic term by combining the L6 velocity norm with weighted local energy.

Reading context: §5 and Appendix A.2; the local-energy estimate.

**Source namespace:** Breakdown.

**Support from exterior vanishing.** A function that vanishes beyond radius `2r` has compact support. Source: Breakdown.hasCompactSupport_of_vanish_far in Breakdown.Uniqueness.CubicTerm, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CubicTerm.lean#L10).

**Integrable energy density.** A finite-energy field has integrable squared velocity. Source: Breakdown.integrable_sq_of_energy in Breakdown.Uniqueness.CubicTerm, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CubicTerm.lean#L18).

**Energy integral bound.** A field with energy parameter `A` has squared-velocity integral at most `A²`. Source: Breakdown.integral_sq_le_of_energy in Breakdown.Uniqueness.CubicTerm, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CubicTerm.lean#L25).

**Energy in the Hölder exponent.** The power `‖w‖^(3/2)` belongs to L^(4/3) for a finite-energy field. Source: Breakdown.memLp_rpow_norm in Breakdown.Uniqueness.CubicTerm, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CubicTerm.lean#L33).

**Local Hölder factor.** For positive radius, the power `(cutoff² ‖w‖)^(3/2)` belongs to L4. Source: Breakdown.memLp_cutoff_rpow in Breakdown.Uniqueness.CubicTerm, line 43. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CubicTerm.lean#L43).

**Local cubic integral.** The cutoff cubic integral is bounded by the three-halves powers of the local L6 norm and the energy parameter. Source: Breakdown.lpProd_step in Breakdown.Uniqueness.CubicTerm, line 52. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CubicTerm.lean#L52).

**Cubic cutoff flux bound.** For radii at least one, the cubic cutoff flux is bounded by a constant times the local L6 norm to power three-halves times `A^(3/2)/r`. Source: Breakdown.cubic_term_le in Breakdown.Uniqueness.CubicTerm, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CubicTerm.lean#L104).

### Breakdown.Uniqueness.CutoffBounds

This file proves the decay and derivative bounds for the spatial energy cutoff, including the constants needed for weighted integration.

Reading context: §5 and Appendix A.2; cutoff estimates for local energy.

**Source namespace:** Breakdown.

**Cutoff equals one inside the ball.** For positive radius, the radial cutoff equals one wherever `‖x‖ ≤ r`. Source: Breakdown.radialCutoff_eq_one_aux in Breakdown.Uniqueness.CutoffBounds, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L10).

**Smooth radial cutoff.** The radial cutoff is smooth when its radius is positive. Source: Breakdown.contDiff_radialCutoff in Breakdown.Uniqueness.CutoffBounds, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L17).

**Nonnegative radial cutoff.** The radial cutoff is nonnegative at every point. Source: Breakdown.radialCutoff_nonneg in Breakdown.Uniqueness.CutoffBounds, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L30).

**Cutoff bounded by one.** The radial cutoff is at most one at every point. Source: Breakdown.radialCutoff_le_one in Breakdown.Uniqueness.CutoffBounds, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L33).

**Cutoff equals one inside the ball.** For `r > 0`, the radial cutoff is one on the closed ball of radius `r`. Source: Breakdown.radialCutoff_eq_one in Breakdown.Uniqueness.CutoffBounds, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L36).

**Cutoff vanishes outside twice radius.** For positive radius, the radial cutoff vanishes when `2r ≤ ‖x‖`. Source: Breakdown.radialCutoff_eq_zero in Breakdown.Uniqueness.CutoffBounds, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L40).

**Compact cutoff support.** The radial cutoff has compact support for positive radius. Source: Breakdown.hasCompactSupport_radialCutoff in Breakdown.Uniqueness.CutoffBounds, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L47).

**Rescaling the unit cutoff.** The radius-`r` cutoff is the unit cutoff composed with dilation by `r⁻¹`. Source: Breakdown.radialCutoff_scale in Breakdown.Uniqueness.CutoffBounds, line 54. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L54).

**Norm of inverse dilation.** For positive radius, the norm of the linear dilation by `r⁻¹` is at most `r⁻¹`. Source: Breakdown.norm_scaleMap_le in Breakdown.Uniqueness.CutoffBounds, line 61. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L61).

**Differentiable radial cutoff.** A radial cutoff with positive radius is differentiable. Source: Breakdown.differentiable_radialCutoff in Breakdown.Uniqueness.CutoffBounds, line 70. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L70).

**Bounded derivative of unit cutoff.** The derivative of the unit cutoff has one bound valid at every point. Source: Breakdown.fderiv_bound_one in Breakdown.Uniqueness.CutoffBounds, line 74. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L74).

**Cutoff derivative decays with radius.** The cutoff derivative is bounded by a fixed constant divided by the radius. Source: Breakdown.norm_fderiv_radialCutoff_le in Breakdown.Uniqueness.CutoffBounds, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L78).

**Cutoff Lipschitz estimate.** The difference of two cutoff values is bounded by a constant times their distance divided by the radius. Source: Breakdown.abs_radialCutoff_sub_le in Breakdown.Uniqueness.CutoffBounds, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L92).

**Coordinate vector has unit norm.** Every coordinate unit vector has norm one. Source: Breakdown.norm_unitVector in Breakdown.Uniqueness.CutoffBounds, line 103. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L103).

**Gradient versus derivative norm.** The scalar gradient has norm at most three times the derivative norm. Source: Breakdown.norm_gradientAt_le in Breakdown.Uniqueness.CutoffBounds, line 106. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L106).

**Derivative of the fourth-power cutoff.** The derivative of the fourth-power cutoff is four times the cutoff cubed times its derivative. Source: Breakdown.fderiv_cutoffPow in Breakdown.Uniqueness.CutoffBounds, line 116. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L116).

**Fourth-power cutoff gradient bound.** The gradient of the fourth-power cutoff is bounded by `C/r` times the cutoff cubed. Source: Breakdown.norm_gradient_cutoffPow_le in Breakdown.Uniqueness.CutoffBounds, line 124. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L124).

**Laplacian versus Hessian norm.** The absolute scalar Laplacian is at most three times the second derivative norm. Source: Breakdown.abs_scalarSumSecondPartials_le in Breakdown.Uniqueness.CutoffBounds, line 138. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L138).

**Rescaling the fourth-power cutoff.** The radius-`r` fourth-power cutoff is obtained from the unit one by inverse dilation. Source: Breakdown.cutoffPow_scale in Breakdown.Uniqueness.CutoffBounds, line 151. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L151).

**Smooth fourth-power cutoff.** The fourth power of a positive-radius cutoff is smooth. Source: Breakdown.contDiff_cutoffPow in Breakdown.Uniqueness.CutoffBounds, line 157. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L157).

**Compact fourth-power support.** The fourth-power cutoff has compact support for positive radius. Source: Breakdown.hasCompactSupport_cutoffPow in Breakdown.Uniqueness.CutoffBounds, line 160. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L160).

**Cutoff Laplacian bound.** The absolute Laplacian of the fourth-power cutoff is bounded by a constant divided by `r²`. Source: Breakdown.abs_scalarSumSecondPartials_cutoffPow_le in Breakdown.Uniqueness.CutoffBounds, line 168. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffBounds.lean#L168).

### Breakdown.Uniqueness.CutoffHs

This file bounds the L6 norm of the cutoff velocity by the square root of cutoff dissipation plus a radius-dependent energy error.

Reading context: §5 and Appendix A.2; admissible cutoff tests.

**Source namespace:** Breakdown.

**Dimension of physical space.** The real dimension of physical space is three. Source: Breakdown.finrank_space in Breakdown.Uniqueness.CutoffHs, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L10).

**Compact Sobolev inequality.** A compactly supported C1 vector field has L6 norm bounded by a fixed multiple of its derivative's L2 norm. Source: Breakdown.hs_space in Breakdown.Uniqueness.CutoffHs, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L12).

**Operator norm from coordinate images.** A linear map's norm is at most the square root of the sum of squared norms of its coordinate images. Source: Breakdown.opNorm_le_sqrt_sum in Breakdown.Uniqueness.CutoffHs, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L20).

**Derivative of a cutoff field.** The derivative of `cutoff² w` is bounded by the cutoff gradient energy density plus `2c‖w‖/r`. Source: Breakdown.norm_fderiv_cutoffSq_smul_le in Breakdown.Uniqueness.CutoffHs, line 34. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L34).

**Integral formula for an Lp norm.** For a nonnegative continuous compactly supported function, the integer Lp norm is the corresponding integral root. Source: Breakdown.eLpNorm_nat_eq in Breakdown.Uniqueness.CutoffHs, line 64. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L64).

**L2 norm from the energy parameter.** The L2 norm of the velocity magnitude is at most the finite-energy parameter `A`. Source: Breakdown.eLpNorm_norm_le_of_energy in Breakdown.Uniqueness.CutoffHs, line 82. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L82).

**Radius outside the closed ball.** A point outside the closed ball of radius `2r` satisfies `2r ≤ ‖x‖`. Source: Breakdown.outside_ball in Breakdown.Uniqueness.CutoffHs, line 98. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L98).

**Local Sobolev estimate.** For radii at least one, the local L6 norm is bounded by the square root of cutoff dissipation plus a constant times `A/r`. Source: Breakdown.cutoffSixthNorm_le in Breakdown.Uniqueness.CutoffHs, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/CutoffHs.lean#L103).

### Breakdown.Uniqueness.DifferenceEstimate

This file turns the weighted difference-energy identity into the estimate used to compare two smooth Navier-Stokes solutions.

Reading context: §5 and Appendix A.2; smooth physical uniqueness.

**Source namespace:** Breakdown.

**Difference-energy error bound.** For admissible difference data, the energy derivative expression is at most `2U₁` times local energy plus an error of order `1/r`. Source: Breakdown.differenceRHS_le in Breakdown.Uniqueness.DifferenceEstimate, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimate.lean#L15).

### Breakdown.Uniqueness.DifferenceEstimateAux

This file bounds the linear, cubic and pressure contributions to the difference-energy identity.

Reading context: §5 and Appendix A.2; the component estimates for physical uniqueness.

**Source namespace:** Breakdown.

**Absorbing a cubic product.** Nonnegative `M`, `x`, and `z` satisfy `M x³ z ≤ x⁴ + M⁴ z⁴`. Source: Breakdown.cube_mul_le_fourth in Breakdown.Uniqueness.DifferenceEstimateAux, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L10).

**Cubic energy power bound.** Every real `A` satisfies `A³ ≤ A² + A⁶`. Source: Breakdown.pow_three_le_sum in Breakdown.Uniqueness.DifferenceEstimateAux, line 17. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L17).

**Quartic energy power bound.** Every real `A` satisfies `A⁴ ≤ A² + A⁶`. Source: Breakdown.pow_four_le_sum in Breakdown.Uniqueness.DifferenceEstimateAux, line 21. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L21).

**Three-halves power as a cube.** For a nonnegative real number, its three-halves power is the cube of its square root. Source: Breakdown.rpow_three_halves_eq in Breakdown.Uniqueness.DifferenceEstimateAux, line 24. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L24).

**Absorbing the cubic flux.** The local Sobolev estimate allows the cubic flux to consume half of the dissipation and leave an explicit `1/r` error. Source: Breakdown.cubic_part_le in Breakdown.Uniqueness.DifferenceEstimateAux, line 28. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L28).

**Absorbing the quadratic flux.** The local Sobolev estimate allows the quadratic flux to consume one quarter of the dissipation and leave an explicit `1/r` error. Source: Breakdown.quadratic_part_le in Breakdown.Uniqueness.DifferenceEstimateAux, line 80. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L80).

**Integrable cutoff transport.** The transport integrand with the cutoff gradient is integrable for continuous velocity fields and positive radius. Source: Breakdown.integrable_transport in Breakdown.Uniqueness.DifferenceEstimateAux, line 106. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L106).

**Combining the energy errors.** The stated seven scalar estimates combine into the difference-energy bound with an explicit constant multiplying `(1+U₀)(A²+A⁶)/r`. Source: Breakdown.combine_bounds in Breakdown.Uniqueness.DifferenceEstimateAux, line 122. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L122).

**Assembling the difference estimate.** The Sobolev, Laplacian, transport, stretching, cubic, mixed-stress and self-stress bounds imply the difference-energy estimate. Source: Breakdown.differenceRHS_le_of_bounds in Breakdown.Uniqueness.DifferenceEstimateAux, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/DifferenceEstimateAux.lean#L204).

### Breakdown.Uniqueness.EnergyDefs

This file defines the cutoff-weighted energy, its spatial density and the local integrability bounds used throughout the physical uniqueness argument.

Reading context: §5 and Appendix A.2; weighted energy bookkeeping.

**Source namespace:** Breakdown.

**Fourth-power cutoff.** The energy cutoff is the fourth power of the radial cutoff. Source: Breakdown.cutoffPow in Breakdown.Uniqueness.EnergyDefs, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L10).

**Local kinetic energy.** Local kinetic energy is one half of the integral of the fourth-power cutoff times squared velocity. Source: Breakdown.cutoffEnergy in Breakdown.Uniqueness.EnergyDefs, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L12).

**Local dissipation.** Local dissipation integrates the fourth-power cutoff against the sum of squared coordinate derivatives. Source: Breakdown.cutoffDissipation in Breakdown.Uniqueness.EnergyDefs, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L14).

**Local L6 norm.** The local L6 norm is the sixth root of the integral of `(cutoff² ‖w‖)^6`. Source: Breakdown.cutoffSixthNorm in Breakdown.Uniqueness.EnergyDefs, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L17).

**Flux through the cutoff.** The cutoff flux is the derivative of the radial cutoff in the velocity direction. Source: Breakdown.cutoffFlux in Breakdown.Uniqueness.EnergyDefs, line 20. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L20).

**Cutoff divergence source.** The cutoff source is the divergence of the vector field obtained by multiplying velocity by the fourth-power cutoff. Source: Breakdown.cutoffSource in Breakdown.Uniqueness.EnergyDefs, line 22. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L22).

**Stress paired with a Hessian.** The stress pairing integrates the tensor product of two fields against a scalar Hessian. Source: Breakdown.stressPairing in Breakdown.Uniqueness.EnergyDefs, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L25).

**Pressure representation defect.** The pressure defect subtracts the Newtonian stress representation from the pressure-gradient pairing. Source: Breakdown.pressureDefect in Breakdown.Uniqueness.EnergyDefs, line 28. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L28).

**Difference-energy derivative terms.** The difference-energy expression combines dissipation, cutoff diffusion, transport, stretching and three pressure-stress terms. Source: Breakdown.differenceRHS in Breakdown.Uniqueness.EnergyDefs, line 32. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L32).

**Finite-energy smooth field.** This proposition bundles smoothness, zero divergence, nonnegative `A`, and an energy integral bounded by `A²`. Source: Breakdown.IsFiniteEnergyField in Breakdown.Uniqueness.EnergyDefs, line 41. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L41).

**Data for the difference estimate.** This proposition adds a smooth divergence-free comparison field with velocity and derivative bounds to a finite-energy difference field. Source: Breakdown.IsDifferenceData in Breakdown.Uniqueness.EnergyDefs, line 47. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/EnergyDefs.lean#L47).

### Breakdown.Uniqueness.FundSolByParts

This file proves integration by parts for the three-dimensional Newtonian potential with compactly supported smooth data.

Reading context: §5 and Appendix A.2; the pressure-potential representation.

**Source namespace:** Breakdown.FundSol.

**Smooth second derivatives.** Second partial derivatives of a smooth scalar function are smooth. Source: Breakdown.FundSol.contDiff_secondPartial in Breakdown.Uniqueness.FundSolByParts, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L12).

**Support of second derivatives.** A second partial derivative has compact support when the original function does. Source: Breakdown.FundSol.hasCompactSupport_secondPartial in Breakdown.Uniqueness.FundSolByParts, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L18).

**Potential commutes with Laplacian.** For smooth compactly supported data, taking the Laplacian commutes with taking the Newtonian potential. Source: Breakdown.FundSol.scalarSumSecondPartials_potential_eq_potential in Breakdown.Uniqueness.FundSolByParts, line 24. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L24).

**Harmonic where the source vanishes.** The potential has zero Laplacian at a point where its smooth compactly supported source is zero. Source: Breakdown.FundSol.scalarSumSecondPartials_potential_of_eq_zero in Breakdown.Uniqueness.FundSolByParts, line 38. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L38).

**Linearity of the scalar Laplacian.** The scalar Laplacian distributes over a sum and a real scalar multiple of smooth functions. Source: Breakdown.FundSol.scalarSumSecondPartials_add_smul in Breakdown.Uniqueness.FundSolByParts, line 49. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L49).

**Normalising the bump potential.** The potential of the centered bump's Laplacian equals one at its center. Source: Breakdown.FundSol.potential_scalarSumSecondPartials_centeredBump in Breakdown.Uniqueness.FundSolByParts, line 58. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L58).

**Laplacian recovers the source.** The Laplacian of the potential of smooth compactly supported data equals that data. Source: Breakdown.FundSol.scalarSumSecondPartials_potential_eq_self in Breakdown.Uniqueness.FundSolByParts, line 69. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L69).

**Potential inverts the Laplacian.** The potential of a smooth compactly supported function's Laplacian equals the original function. Source: Breakdown.FundSol.potential_scalarSumSecondPartials in Breakdown.Uniqueness.FundSolByParts, line 86. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L86).

**Potential solves the Poisson equation.** For smooth compactly supported source `g`, the potential satisfies `Δ potential(g) = g`. Source: Breakdown.FundSol.scalarSumSecondPartials_potential in Breakdown.Uniqueness.FundSolByParts, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByParts.lean#L90).

### Breakdown.Uniqueness.FundSolByPartsRadial

This file constructs a centered radial bump and computes the normalization integral that identifies the Newtonian fundamental solution.

Reading context: §5 and Appendix A.2; the singular-kernel integration step.

**Source namespace:** Breakdown.FundSol.

**Radial bump profile.** The one-dimensional bump profile is the smooth transition evaluated at `1-u`. Source: Breakdown.FundSol.bumpRadius in Breakdown.Uniqueness.FundSolByPartsRadial, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L10).

**Bump centered at a point.** The centered bump evaluates its radial profile at squared distance from the center. Source: Breakdown.FundSol.centeredBump in Breakdown.Uniqueness.FundSolByPartsRadial, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L12).

**Radial bump Laplacian profile.** The radial Laplacian profile is `6b′(u) + 4u b″(u)`. Source: Breakdown.FundSol.bumpSumSecondPartialsProfile in Breakdown.Uniqueness.FundSolByPartsRadial, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L14).

**Smooth bump profile.** The radial bump profile is smooth. Source: Breakdown.FundSol.contDiff_bumpRadius in Breakdown.Uniqueness.FundSolByPartsRadial, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L17).

**Smooth first bump derivative.** The derivative of the radial bump profile is smooth. Source: Breakdown.FundSol.contDiff_deriv_bumpRadius in Breakdown.Uniqueness.FundSolByPartsRadial, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L20).

**Smooth second bump derivative.** The second derivative of the radial bump profile is smooth. Source: Breakdown.FundSol.contDiff_deriv_deriv_bumpRadius in Breakdown.Uniqueness.FundSolByPartsRadial, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L23).

**Differentiable bump profile.** The radial bump profile is differentiable. Source: Breakdown.FundSol.differentiable_bumpRadius in Breakdown.Uniqueness.FundSolByPartsRadial, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L26).

**Differentiable bump derivative.** The first derivative of the bump profile is differentiable. Source: Breakdown.FundSol.differentiable_deriv_bumpRadius in Breakdown.Uniqueness.FundSolByPartsRadial, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L29).

**Bump vanishes beyond one.** The radial bump profile vanishes for `u ≥ 1`. Source: Breakdown.FundSol.bumpRadius_eq_zero in Breakdown.Uniqueness.FundSolByPartsRadial, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L32).

**First derivative vanishes outside.** The first bump derivative vanishes for `u > 1`. Source: Breakdown.FundSol.deriv_bumpRadius_eq_zero in Breakdown.Uniqueness.FundSolByPartsRadial, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L35).

**Second derivative vanishes outside.** The second bump derivative vanishes for `u > 1`. Source: Breakdown.FundSol.deriv_deriv_bumpRadius_eq_zero in Breakdown.Uniqueness.FundSolByPartsRadial, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L42).

**Laplacian profile vanishes outside.** The bump's radial Laplacian profile vanishes for `u > 1`. Source: Breakdown.FundSol.bumpSumSecondPartialsProfile_eq_zero in Breakdown.Uniqueness.FundSolByPartsRadial, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L49).

**Continuous Laplacian profile.** The radial Laplacian profile is continuous. Source: Breakdown.FundSol.continuous_bumpSumSecondPartialsProfile in Breakdown.Uniqueness.FundSolByPartsRadial, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L52).

**Radial integration antiderivative.** The derivative of `b(r²)+2r²b′(r²)` is `r` times the radial Laplacian profile at `r²`. Source: Breakdown.FundSol.hasDerivAt_radial_antiderivative in Breakdown.Uniqueness.FundSolByPartsRadial, line 58. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L58).

**Radial normalisation integral.** The integral of `r` times the radial Laplacian profile over positive radii equals minus one. Source: Breakdown.FundSol.integral_Ioi_radial in Breakdown.Uniqueness.FundSolByPartsRadial, line 73. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L73).

**Kernel normalisation integral.** Integrating the radial Laplacian profile against the Newtonian kernel gives one. Source: Breakdown.FundSol.integral_bumpSumSecondPartialsProfile_mul_kernel in Breakdown.Uniqueness.FundSolByPartsRadial, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L98).

**Smooth centered bump.** A centered bump is smooth in its spatial argument. Source: Breakdown.FundSol.contDiff_centeredBump in Breakdown.Uniqueness.FundSolByPartsRadial, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L119).

**Compact centered bump support.** A centered bump has compact support. Source: Breakdown.FundSol.hasCompactSupport_centeredBump in Breakdown.Uniqueness.FundSolByPartsRadial, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L122).

**Bump value at its center.** The centered bump equals one at its center. Source: Breakdown.FundSol.centeredBump_self in Breakdown.Uniqueness.FundSolByPartsRadial, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L128).

**Derivative of squared distance.** The derivative of squared distance from `x` at `z` is twice inner product with `z-x`. Source: Breakdown.FundSol.hasFDerivAt_normSq_sub in Breakdown.Uniqueness.FundSolByPartsRadial, line 131. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L131).

**Derivative of a centered bump.** The derivative of a centered bump is twice its radial derivative times inner product with displacement from the center. Source: Breakdown.FundSol.hasFDerivAt_centeredBump in Breakdown.Uniqueness.FundSolByPartsRadial, line 136. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L136).

**Laplacian of a centered bump.** The centered bump's Laplacian is its radial Laplacian profile evaluated at squared distance. Source: Breakdown.FundSol.scalarSumSecondPartials_centeredBump in Breakdown.Uniqueness.FundSolByPartsRadial, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolByPartsRadial.lean#L148).

### Breakdown.Uniqueness.FundSolDecay

This file establishes decay of the Newtonian kernel and its derivatives away from compactly supported source data.

Reading context: §5 and Appendix A.2; exterior pressure-potential bounds.

**Source namespace:** Breakdown.FundSol.

**Differentiating scalar convolution.** For a continuous scalar factor and a smooth compactly supported vector factor, differentiation passes through their convolution. Source: Breakdown.FundSol.fderiv_smulConv in Breakdown.Uniqueness.FundSolDecay, line 11. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDecay.lean#L11).

**Derivative bound for convolution.** Each derivative norm of the convolution is bounded by convolution with the corresponding derivative norm of the compact factor. Source: Breakdown.FundSol.norm_iteratedFDeriv_smulConv_le in Breakdown.Uniqueness.FundSolDecay, line 24. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDecay.lean#L24).

**Smooth truncated Newtonian kernel.** For outer radius greater than one, a smooth compactly supported function agrees with the Newtonian kernel on the stated annulus. Source: Breakdown.FundSol.exists_cutoff_kernel in Breakdown.Uniqueness.FundSolDecay, line 41. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDecay.lean#L41).

**Decay at each derivative order.** Each derivative of the potential of smooth compactly supported data decays as `(1+‖x‖)^(-k-1)` with an order-dependent constant. Source: Breakdown.FundSol.decay_each in Breakdown.Uniqueness.FundSolDecay, line 63. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDecay.lean#L63).

**Uniform decay through third order.** One constant controls potential derivatives of orders zero through three by `(1+‖x‖)^(-k-1)`. Source: Breakdown.FundSol.potential_decay in Breakdown.Uniqueness.FundSolDecay, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDecay.lean#L150).

### Breakdown.Uniqueness.FundSolDefs

This file defines the Newtonian kernel, its gradient and Hessian, with the negative inverse-distance normalization used by the pressure equation.

Reading context: §5 and Appendix A.2; the Newtonian pressure kernel.

**Source namespace:** Breakdown.FundSol.

**Newtonian kernel.** The Newtonian kernel is `-1/(4π‖z‖)` with Lean's total inverse at zero. Source: Breakdown.FundSol.kernel in Breakdown.Uniqueness.FundSolDefs, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L10).

**Gradient of the Newtonian kernel.** The kernel-gradient formula is `z/(4π‖z‖³)`. Source: Breakdown.FundSol.kernelGrad in Breakdown.Uniqueness.FundSolDefs, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L12).

**Hessian of the Newtonian kernel.** The kernel Hessian combines the diagonal `‖z‖⁻³` term with `-3zᵢzⱼ‖z‖⁻⁵`, scaled by `1/(4π)`. Source: Breakdown.FundSol.kernelSecondDeriv in Breakdown.Uniqueness.FundSolDefs, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L14).

**Newtonian potential.** The Newtonian potential convolves the source with the Newtonian kernel. Source: Breakdown.FundSol.potential in Breakdown.Uniqueness.FundSolDefs, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L17).

**Coordinate second partial.** A coordinate second partial evaluates the second Fréchet derivative on two coordinate unit vectors. Source: Breakdown.FundSol.secondPartial in Breakdown.Uniqueness.FundSolDefs, line 20. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L20).

**Scalar Laplacian.** The scalar Laplacian is the sum of the three diagonal second partial derivatives. Source: Breakdown.FundSol.scalarSumSecondPartials in Breakdown.Uniqueness.FundSolDefs, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L23).

**Mollifier bump profile.** The mollifier's bump profile applies the smooth transition to `1-2‖x‖²`. Source: Breakdown.FundSol.bumpProfile in Breakdown.Uniqueness.FundSolDefs, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L25).

**Normalised mollifier.** The mollifier rescales the bump by `ρ⁻¹` and divides by `ρ³` times the bump integral. Source: Breakdown.FundSol.mollifier in Breakdown.Uniqueness.FundSolDefs, line 27. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L27).

**Mollification of a vector field.** Mollification convolves a vector field with the normalised scalar mollifier. Source: Breakdown.FundSol.mollify in Breakdown.Uniqueness.FundSolDefs, line 29. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolDefs.lean#L29).

### Breakdown.Uniqueness.FundSolEnergy

This file derives the L2 Hessian estimate for a Newtonian potential from its Laplacian identity and integration by parts.

Reading context: §5 and Appendix A.2; the near-field pressure estimate.

**Source namespace:** Breakdown.FundSol.

**Mixed-derivative energy identity.** With the stated smoothness and decay, the integral of a squared mixed derivative equals the integral of the product of diagonal derivatives. Source: Breakdown.FundSol.integral_sq_dirDeriv_two in Breakdown.Uniqueness.FundSolEnergy, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L14).

**Integrable Hessian products.** The stated decay through order three makes products of second directional derivatives integrable. Source: Breakdown.FundSol.integrable_sq_dirDeriv_two in Breakdown.Uniqueness.FundSolEnergy, line 81. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L81).

**Integrable potential Hessian energy.** For smooth compactly supported data, the sum of squared potential Hessian entries is integrable. Source: Breakdown.FundSol.integrable_sum_sq_secondPartial in Breakdown.Uniqueness.FundSolEnergy, line 91. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L91).

**Hessian energy equals source energy.** The potential's total squared Hessian integral equals the squared L2 integral of its smooth compactly supported source. Source: Breakdown.FundSol.integral_sum_sq_secondPartial in Breakdown.Uniqueness.FundSolEnergy, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L101).

**Gradient energy in coordinates.** The squared gradient norm equals the sum of squared coordinate directional derivatives. Source: Breakdown.FundSol.norm_sq_gradientAt in Breakdown.Uniqueness.FundSolEnergy, line 137. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L137).

**Euclidean norm in coordinates.** The squared norm of a spatial vector is the sum of its squared coordinates. Source: Breakdown.FundSol.norm_sq_eq_sum in Breakdown.Uniqueness.FundSolEnergy, line 143. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L143).

**Gradient energy from divergence data.** For the stated Poisson equation and decay assumptions, the potential's gradient energy is at most the source vector field's energy. Source: Breakdown.FundSol.gradient_energy_bound in Breakdown.Uniqueness.FundSolEnergy, line 146. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L146).

**Derivative commutes with coordinates.** Differentiation of a smooth vector field commutes with selecting a coordinate. Source: Breakdown.FundSol.fderiv_component in Breakdown.Uniqueness.FundSolEnergy, line 229. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L229).

**Potential of a three-term sum.** The potential distributes over three smooth compactly supported scalar sources. Source: Breakdown.FundSol.potential_sum_three in Breakdown.Uniqueness.FundSolEnergy, line 239. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L239).

**L2 bound for the gradient potential.** The gradient of the potential of a compactly supported smooth field's divergence has L2 energy no greater than that field's energy. Source: Breakdown.FundSol.integral_sq_gradient_potential_div_le in Breakdown.Uniqueness.FundSolEnergy, line 249. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergy.lean#L249).

### Breakdown.Uniqueness.FundSolEnergyAux

This file supplies the derivative, cutoff and boundary-decay estimates that justify the Hessian energy calculation.

Reading context: §5 and Appendix A.2; analytic justification of the potential energy estimate.

**Source namespace:** Breakdown.FundSol.Internal.

**Directional derivative.** A directional derivative evaluates the Fréchet derivative on the chosen direction. Source: Breakdown.FundSol.Internal.dirDeriv in Breakdown.Uniqueness.FundSolEnergyAux, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L10).

**Smooth derivative map.** The derivative map of a smooth scalar function is smooth. Source: Breakdown.FundSol.Internal.contDiff_fderiv_of_smooth in Breakdown.Uniqueness.FundSolEnergyAux, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L12).

**Smooth directional derivative.** A fixed directional derivative of a smooth scalar function is smooth. Source: Breakdown.FundSol.Internal.contDiff_dirDeriv in Breakdown.Uniqueness.FundSolEnergyAux, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L16).

**Smoothness implies differentiability.** A smooth scalar function is differentiable. Source: Breakdown.FundSol.Internal.differentiable_of_contDiff_infty in Breakdown.Uniqueness.FundSolEnergyAux, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L20).

**Derivative bound in a direction.** An order-`n` derivative of a directional derivative is bounded by the direction norm times the order-`n+1` derivative norm. Source: Breakdown.FundSol.Internal.norm_iteratedFDeriv_dirDeriv_le in Breakdown.Uniqueness.FundSolEnergyAux, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L24).

**Coordinate direction has unit norm.** Every coordinate unit vector has norm one. Source: Breakdown.FundSol.Internal.norm_unitVector in Breakdown.Uniqueness.FundSolEnergyAux, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L32).

**Unit-direction derivative bound.** A derivative along a coordinate unit vector is bounded by the next full derivative norm. Source: Breakdown.FundSol.Internal.norm_iteratedFDeriv_dirDeriv_unit_le in Breakdown.Uniqueness.FundSolEnergyAux, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L35).

**First directional derivative bound.** The absolute first coordinate derivative is bounded by the first Fréchet derivative norm. Source: Breakdown.FundSol.Internal.abs_dirDeriv_le in Breakdown.Uniqueness.FundSolEnergyAux, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L40).

**Second directional derivative bound.** The absolute second coordinate directional derivative is bounded by the second derivative norm. Source: Breakdown.FundSol.Internal.abs_dirDeriv_two_le in Breakdown.Uniqueness.FundSolEnergyAux, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L45).

**Third directional derivative bound.** The absolute third coordinate directional derivative is bounded by the third derivative norm. Source: Breakdown.FundSol.Internal.abs_dirDeriv_three_le in Breakdown.Uniqueness.FundSolEnergyAux, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L50).

**Iterated directional derivative.** Two directional derivatives agree with evaluation of the iterated Fréchet derivative. Source: Breakdown.FundSol.Internal.dirDeriv_dirDeriv_apply in Breakdown.Uniqueness.FundSolEnergyAux, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L56).

**Directional derivatives commute.** Two fixed directional derivatives commute on smooth scalar functions. Source: Breakdown.FundSol.Internal.dirDeriv_comm in Breakdown.Uniqueness.FundSolEnergyAux, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L64).

**Second partial as two directions.** A coordinate second partial equals two successive coordinate directional derivatives. Source: Breakdown.FundSol.Internal.secondPartial_eq_dirDeriv in Breakdown.Uniqueness.FundSolEnergyAux, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L72).

**Directional integration by parts.** With smooth inputs and the stated three integrability hypotheses, moving a directional derivative across an integral changes its sign. Source: Breakdown.FundSol.Internal.integral_mul_dirDeriv in Breakdown.Uniqueness.FundSolEnergyAux, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L78).

**Comparison of integrable decay rates.** Decay of integer order at least four is bounded by decay of order four. Source: Breakdown.FundSol.Internal.inv_one_add_norm_pow_le in Breakdown.Uniqueness.FundSolEnergyAux, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L85).

**Integrability from spatial decay.** A continuous scalar function bounded by `(1+‖x‖)^(-m)` is integrable when `m ≥ 4`. Source: Breakdown.FundSol.Internal.integrable_of_abs_le_decay in Breakdown.Uniqueness.FundSolEnergyAux, line 92. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L92).

**Integrability of decaying products.** Two continuous functions have integrable product when their stated decay orders sum to at least four. Source: Breakdown.FundSol.Internal.integrable_mul_of_decay in Breakdown.Uniqueness.FundSolEnergyAux, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolEnergyAux.lean#L101).

### Breakdown.Uniqueness.FundSolKernel

This file differentiates the Newtonian kernel and records its harmonicity and quantitative derivative bounds away from the origin.

Reading context: §5 and Appendix A.2; differential identities for the pressure kernel.

**Source namespace:** Breakdown.FundSol.

**Derivative of the norm off zero.** Away from zero, the derivative of the spatial norm is the normalised radial inner product. Source: Breakdown.FundSol.hasFDerivAt_norm_of_ne in Breakdown.Uniqueness.FundSolKernel, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L10).

**Derivative of inverse radius.** Away from zero, the derivative of inverse radius is minus the radial inner product divided by the radius cubed. Source: Breakdown.FundSol.hasFDerivAt_inv_norm in Breakdown.Uniqueness.FundSolKernel, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L23).

**Derivative of the Newtonian kernel.** Away from zero, the derivative of the kernel is inner product with its kernel-gradient formula. Source: Breakdown.FundSol.hasFDerivAt_kernel in Breakdown.Uniqueness.FundSolKernel, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L32).

**Smooth kernel away from zero.** The Newtonian kernel is smooth on the complement of the origin. Source: Breakdown.FundSol.contDiffOn_kernel in Breakdown.Uniqueness.FundSolKernel, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L43).

**Kernel Hessian formula off zero.** Away from the origin, the kernel's coordinate second partial equals the explicit kernel Hessian formula. Source: Breakdown.FundSol.secondPartial_kernel in Breakdown.Uniqueness.FundSolKernel, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L50).

**Norm of the kernel gradient.** The kernel gradient has norm `1/(4π‖z‖²)`. Source: Breakdown.FundSol.norm_kernelGrad in Breakdown.Uniqueness.FundSolKernel, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L75).

**Kernel Hessian bound.** Every kernel Hessian entry has absolute value at most `‖z‖⁻³`. Source: Breakdown.FundSol.abs_kernelSecondDeriv_le in Breakdown.Uniqueness.FundSolKernel, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L81).

**Kernel is harmonic off zero.** The trace of the Newtonian kernel Hessian vanishes away from the origin. Source: Breakdown.FundSol.sum_kernelSecondDeriv_diag in Breakdown.Uniqueness.FundSolKernel, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L115).

**Homogeneity of kernel derivatives.** Under positive dilation, the order-`k` kernel derivative norm scales with degree `-k-1`. Source: Breakdown.FundSol.iteratedFDeriv_kernel_smul in Breakdown.Uniqueness.FundSolKernel, line 123. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L123).

**Bounds for every kernel derivative.** Each order-`k` kernel derivative is bounded off zero by a constant times `‖z‖^(-k-1)`. Source: Breakdown.FundSol.norm_iteratedFDeriv_kernel_le in Breakdown.Uniqueness.FundSolKernel, line 159. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L159).

**Locally integrable Newtonian kernel.** The Newtonian kernel is locally integrable in three dimensions. Source: Breakdown.FundSol.locallyIntegrable_kernel in Breakdown.Uniqueness.FundSolKernel, line 192. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L192).

**Locally integrable kernel gradient.** The gradient of the Newtonian kernel is locally integrable. Source: Breakdown.FundSol.locallyIntegrable_kernelGrad in Breakdown.Uniqueness.FundSolKernel, line 202. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolKernel.lean#L202).

### Breakdown.Uniqueness.FundSolMeanValue

This file develops the mean-value and mollifier identities that identify harmonic functions from their local averages.

Reading context: §5 and Appendix A.2; eliminating the harmonic pressure defect.

**Source namespace:** Breakdown.FundSol.

**Smooth mollifier bump.** The mollifier's unscaled bump profile is smooth. Source: Breakdown.FundSol.contDiff_bumpProfile in Breakdown.Uniqueness.FundSolMeanValue, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L12).

**Nonnegative mollifier bump.** The unscaled mollifier bump is nonnegative. Source: Breakdown.FundSol.bumpProfile_nonneg in Breakdown.Uniqueness.FundSolMeanValue, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L16).

**Mollifier bump bounded by one.** The unscaled mollifier bump is at most one. Source: Breakdown.FundSol.bumpProfile_le_one in Breakdown.Uniqueness.FundSolMeanValue, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L18).

**Mollifier bump support radius.** The unscaled bump vanishes wherever `‖x‖² ≥ 1/2`. Source: Breakdown.FundSol.bumpProfile_eq_zero in Breakdown.Uniqueness.FundSolMeanValue, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L20).

**Bump value at the origin.** The unscaled mollifier bump equals one at the origin. Source: Breakdown.FundSol.bumpProfile_zero in Breakdown.Uniqueness.FundSolMeanValue, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L23).

**Compact mollifier bump support.** The unscaled mollifier bump has compact support. Source: Breakdown.FundSol.hasCompactSupport_bumpProfile in Breakdown.Uniqueness.FundSolMeanValue, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L26).

**Positive bump integral.** The integral of the unscaled mollifier bump is positive. Source: Breakdown.FundSol.integral_bumpProfile_pos in Breakdown.Uniqueness.FundSolMeanValue, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L33).

**Smooth mollifier.** The mollifier is smooth for every value of its scale parameter. Source: Breakdown.FundSol.contDiff_mollifier in Breakdown.Uniqueness.FundSolMeanValue, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L38).

**Nonnegative mollifier.** A mollifier with positive scale is nonnegative. Source: Breakdown.FundSol.mollifier_nonneg in Breakdown.Uniqueness.FundSolMeanValue, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L42).

**Mollifier's sharper support bound.** A positive-scale mollifier vanishes wherever `‖x‖² ≥ ρ²/2`. Source: Breakdown.FundSol.mollifier_eq_zero_of_sq in Breakdown.Uniqueness.FundSolMeanValue, line 47. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L47).

**Mollifier vanishes outside its radius.** A positive-scale mollifier vanishes wherever `ρ ≤ ‖x‖`. Source: Breakdown.FundSol.mollifier_eq_zero in Breakdown.Uniqueness.FundSolMeanValue, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L55).

**Mollifier has unit integral.** A mollifier with positive scale has integral one. Source: Breakdown.FundSol.integral_mollifier in Breakdown.Uniqueness.FundSolMeanValue, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L60).

**Size of the mollifier.** The mollifier is bounded by a fixed constant times `ρ⁻³` for positive scale. Source: Breakdown.FundSol.mollifier_le in Breakdown.Uniqueness.FundSolMeanValue, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L67).

**All mollifier derivative bounds.** The order-`k` mollifier derivative norm is bounded by a constant times `ρ^(-3-k)`. Source: Breakdown.FundSol.norm_iteratedFDeriv_mollifier_le in Breakdown.Uniqueness.FundSolMeanValue, line 75. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L75).

**First mollifier derivative bound.** The mollifier derivative norm is bounded by a constant times `ρ⁻⁴`. Source: Breakdown.FundSol.norm_fderiv_mollifier_le in Breakdown.Uniqueness.FundSolMeanValue, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L102).

**Second mollifier derivative bound.** The mollifier's second derivative norm is bounded by a constant times `ρ⁻⁵`. Source: Breakdown.FundSol.norm_iteratedFDeriv_two_mollifier_le in Breakdown.Uniqueness.FundSolMeanValue, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L107).

**Compact mollifier support.** A mollifier with positive scale has compact support. Source: Breakdown.FundSol.hasCompactSupport_mollifier in Breakdown.Uniqueness.FundSolMeanValue, line 112. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L112).

**Integral formula for the potential.** The potential at `x` is the integral of the source times the kernel at `x-y`. Source: Breakdown.FundSol.potential_eq_integral in Breakdown.Uniqueness.FundSolMeanValue, line 118. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L118).

**Rotational symmetry of the potential.** The potential of the radial mollifier is invariant under linear isometries. Source: Breakdown.FundSol.potential_mollifier_map in Breakdown.Uniqueness.FundSolMeanValue, line 123. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L123).

**Radial reduction of the potential.** The mollifier potential at any point equals its value at the corresponding radius on the first coordinate axis. Source: Breakdown.FundSol.potential_mollifier_radial in Breakdown.Uniqueness.FundSolMeanValue, line 136. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L136).

**Exterior approximation by the kernel.** Outside radius `2ρ`, the mollifier potential differs from the Newtonian kernel by at most `2ρ/(4π‖x‖²)`. Source: Breakdown.FundSol.abs_potential_mollifier_sub_kernel_le in Breakdown.Uniqueness.FundSolMeanValue, line 144. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L144).

**Positive regularised radius.** The regularised squared radius blends `δ²/2` with the original squared radius using a smooth transition. Source: Breakdown.FundSol.kernelFloor in Breakdown.Uniqueness.FundSolMeanValue, line 210. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L210).

**Smoothed Newtonian kernel.** The smooth kernel replaces squared radius in the Newtonian formula with its positive regularisation. Source: Breakdown.FundSol.smoothKernel in Breakdown.Uniqueness.FundSolMeanValue, line 213. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L213).

**Smooth radius regularisation.** The regularised squared-radius function is smooth. Source: Breakdown.FundSol.contDiff_kernelFloor in Breakdown.Uniqueness.FundSolMeanValue, line 215. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L215).

**Strictly positive regularised radius.** The regularised squared radius is positive whenever `δ > 0`. Source: Breakdown.FundSol.kernelFloor_pos in Breakdown.Uniqueness.FundSolMeanValue, line 220. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L220).

**Radius unchanged beyond the cutoff.** For `δ > 0` and `s ≥ δ²`, the regularised squared radius equals `s`. Source: Breakdown.FundSol.kernelFloor_eq in Breakdown.Uniqueness.FundSolMeanValue, line 233. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L233).

**Smooth regularised kernel.** The regularised Newtonian kernel is smooth when `δ > 0`. Source: Breakdown.FundSol.contDiff_smoothKernel in Breakdown.Uniqueness.FundSolMeanValue, line 242. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L242).

**Kernel unchanged outside the cutoff.** At radius at least `δ > 0`, the regularised kernel equals the original Newtonian kernel. Source: Breakdown.FundSol.smoothKernel_eq in Breakdown.Uniqueness.FundSolMeanValue, line 251. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L251).

**Local equality preserves second jets.** Two functions equal near a point have equal coordinate second partial derivatives there. Source: Breakdown.FundSol.secondPartial_congr_nhds in Breakdown.Uniqueness.FundSolMeanValue, line 256. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L256).

**Harmonic mollifier potential outside.** The mollifier potential has zero Laplacian wherever `‖y‖² > ρ²/2` for positive `ρ`. Source: Breakdown.FundSol.scalarSumSecondPartials_potential_mollifier_far in Breakdown.Uniqueness.FundSolMeanValue, line 260. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L260).

**Exact exterior Newtonian potential.** For positive scale, the mollifier potential equals the Newtonian kernel outside the ball of radius `ρ`. Source: Breakdown.FundSol.potential_mollifier_eq_kernel in Breakdown.Uniqueness.FundSolMeanValue, line 322. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValue.lean#L322).

### Breakdown.Uniqueness.FundSolMeanValueAux

This file proves the radial auxiliary identities used in the harmonic mean-value argument.

Reading context: §5 and Appendix A.2; radial support for pressure averaging.

**Source namespace:** Breakdown.FundSol.Internal.

**Local equality preserves Laplacians.** Two scalar functions equal near a point have the same Laplacian at that point. Source: Breakdown.FundSol.Internal.scalarSumSecondPartials_congr_nhds in Breakdown.Uniqueness.FundSolMeanValueAux, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValueAux.lean#L10).

**Laplacian of a squared-radius profile.** Under the stated differentiability assumptions, `Δ φ(‖x‖²) = 6φ′(‖x‖²)+4‖x‖²φ″(‖x‖²)`. Source: Breakdown.FundSol.Internal.scalarSumSecondPartials_comp_norm_sq in Breakdown.Uniqueness.FundSolMeanValueAux, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValueAux.lean#L14).

**Radial harmonic profile formula.** A twice differentiable solution of the radial harmonic equation on `s > a ≥ 0` has the form `A+B/√s`. Source: Breakdown.FundSol.Internal.eq_add_div_sqrt_of_radial_ode in Breakdown.Uniqueness.FundSolMeanValueAux, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValueAux.lean#L56).

**Faster decay kills both coefficients.** If `A+B/√s` is bounded in absolute value by `C/s` for all sufficiently large `s`, both coefficients vanish. Source: Breakdown.FundSol.Internal.eq_zero_of_abs_add_div_sqrt_le in Breakdown.Uniqueness.FundSolMeanValueAux, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolMeanValueAux.lean#L106).

### Breakdown.Uniqueness.FundSolPointwise

This file represents the Hessian of a Newtonian potential by an ordinary integral when the source vanishes at the evaluation point.

Reading context: §5 and Appendix A.2; the pointwise pressure-source formula.

**Source namespace:** Breakdown.FundSol.

**Integrable singular Hessian pairing.** If a smooth compactly supported source vanishes at `x₀`, its product with the shifted kernel Hessian is integrable. Source: Breakdown.FundSol.integrable_kernelSecondDeriv_mul in Breakdown.Uniqueness.FundSolPointwise, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwise.lean#L10).

**Hessian potential at a source zero.** At a zero of the source, the potential Hessian equals the ordinary integral against the shifted kernel Hessian. Source: Breakdown.FundSol.secondPartial_potential_eq_integral in Breakdown.Uniqueness.FundSolPointwise, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwise.lean#L15).

### Breakdown.Uniqueness.FundSolPointwiseAux

This file controls the integrable singularity produced by a source that vanishes at the evaluation point.

Reading context: §5 and Appendix A.2; local cancellation in the Hessian kernel.

**Source namespace:** Breakdown.FundSol.Internal.

**Truncated inverse radial power.** The truncated radial power equals `t⁻ⁿ` below radius `r` and zero otherwise. Source: Breakdown.FundSol.Internal.radialCut in Breakdown.Uniqueness.FundSolPointwiseAux, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L10).

**Inverse power inside a ball.** The ball power applies the truncated inverse radial power to the spatial norm. Source: Breakdown.FundSol.Internal.ballPow in Breakdown.Uniqueness.FundSolPointwiseAux, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L12).

**Nonnegative truncated inverse power.** The truncated inverse power on a ball is nonnegative. Source: Breakdown.FundSol.Internal.ballPow_nonneg in Breakdown.Uniqueness.FundSolPointwiseAux, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L14).

**Inverse power inside the radius.** Inside radius `r`, the ball power equals `‖z‖⁻ⁿ`. Source: Breakdown.FundSol.Internal.ballPow_of_lt in Breakdown.Uniqueness.FundSolPointwiseAux, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L18).

**Zero outside the radius.** At or outside radius `r`, the ball power vanishes. Source: Breakdown.FundSol.Internal.ballPow_of_le in Breakdown.Uniqueness.FundSolPointwiseAux, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L21).

**Radial integral reduction.** For exponents at most two, the radial integrand equals the cutoff power `y^(2-n)` on positive radii. Source: Breakdown.FundSol.Internal.radial_eqOn in Breakdown.Uniqueness.FundSolPointwiseAux, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L24).

**Integrable inverse powers on a ball.** The truncated inverse power is integrable in three dimensions for exponents at most two. Source: Breakdown.FundSol.Internal.integrable_ballPow in Breakdown.Uniqueness.FundSolPointwiseAux, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L35).

**Integral of a truncated inverse power.** For positive radius and exponent at most two, radial integration gives the explicit ball-power integral. Source: Breakdown.FundSol.Internal.integral_ballPow in Breakdown.Uniqueness.FundSolPointwiseAux, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L49).

**Volume of a radius-r ball.** The integral of the zeroth ball power is unit-ball volume times `r³`. Source: Breakdown.FundSol.Internal.integral_ballPow_zero in Breakdown.Uniqueness.FundSolPointwiseAux, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L59).

**Integral of inverse radius.** The integral of inverse radius over its truncated ball is `3/2` times unit-ball volume times `r²`. Source: Breakdown.FundSol.Internal.integral_ballPow_one in Breakdown.Uniqueness.FundSolPointwiseAux, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L65).

**Integral of inverse radius squared.** The integral of inverse radius squared over its truncated ball is three times unit-ball volume times `r`. Source: Breakdown.FundSol.Internal.integral_ballPow_two in Breakdown.Uniqueness.FundSolPointwiseAux, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L71).

**Cancelling one inverse-radius factor.** The identity `t⁻³ t = t⁻²` holds with Lean's total inverse. Source: Breakdown.FundSol.Internal.inv_pow_three_mul in Breakdown.Uniqueness.FundSolPointwiseAux, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux.lean#L76).

### Breakdown.Uniqueness.FundSolPointwiseAux2

This file justifies the cutoff and limiting operations used to extract a pointwise Hessian formula.

Reading context: §5 and Appendix A.2; approximation of the singular potential integral.

**Source namespace:** Breakdown.FundSol.Internal.

**Potential as a kernel integral.** The potential equals the integral of source values times the translated Newtonian kernel. Source: Breakdown.FundSol.Internal.potential_apply in Breakdown.Uniqueness.FundSolPointwiseAux2, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L10).

**Absolute Newtonian kernel.** The absolute value of the kernel is `1/(4π‖w‖)`. Source: Breakdown.FundSol.Internal.abs_kernel in Breakdown.Uniqueness.FundSolPointwiseAux2, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L14).

**Interior potential bound.** A source bounded by `A` and supported within radius `ρ` has its interior potential bounded by a truncated inverse-radius integral. Source: Breakdown.FundSol.Internal.abs_potential_le in Breakdown.Uniqueness.FundSolPointwiseAux2, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L18).

**Smooth fixed directional derivative.** A fixed directional derivative of a smooth scalar function is smooth. Source: Breakdown.FundSol.Internal.smooth_dir in Breakdown.Uniqueness.FundSolPointwiseAux2, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L39).

**Differentiability from smoothness.** A smooth scalar function is differentiable. Source: Breakdown.FundSol.Internal.differentiable_of_smooth in Breakdown.Uniqueness.FundSolPointwiseAux2, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L43).

**Second partial as nested derivatives.** For a smooth scalar function, the coordinate second partial equals the corresponding nested directional derivative. Source: Breakdown.FundSol.Internal.secondPartial_eq_dir in Breakdown.Uniqueness.FundSolPointwiseAux2, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L46).

**Derivative under reflection.** Differentiating `φ(x₀-y)` contributes the negative derivative of `φ` at `x₀-y`. Source: Breakdown.FundSol.Internal.fderiv_reflect in Breakdown.Uniqueness.FundSolPointwiseAux2, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L55).

**Integrability of a compact product.** The product of two continuous scalar functions is integrable if either factor has compact support. Source: Breakdown.FundSol.Internal.integrable_mul_of_cpt in Breakdown.Uniqueness.FundSolPointwiseAux2, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L63).

**Moving two derivatives to the kernel.** Two integrations by parts move the source's second partial onto the translated smooth kernel with reversed derivative indices. Source: Breakdown.FundSol.Internal.integral_secondPartial_mul in Breakdown.Uniqueness.FundSolPointwiseAux2, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L67).

**Second derivatives depend locally.** Scalar functions that agree near a point have the same coordinate second partial there. Source: Breakdown.FundSol.Internal.secondPartial_congr in Breakdown.Uniqueness.FundSolPointwiseAux2, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L109).

**Second partial bounded by Hessian.** A coordinate second partial is bounded in absolute value by the full second derivative norm. Source: Breakdown.FundSol.Internal.abs_secondPartial_le in Breakdown.Uniqueness.FundSolPointwiseAux2, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux2.lean#L114).

### Breakdown.Uniqueness.FundSolPointwiseAux3

This file computes derivatives and bounds for the localized Newtonian-potential terms.

Reading context: §5 and Appendix A.2; differentiation of the localized pressure potential.

**Source namespace:** Breakdown.FundSol.Internal.

**Measurable Newtonian kernel.** The Newtonian kernel is measurable. Source: Breakdown.FundSol.Internal.measurable_kernel in Breakdown.Uniqueness.FundSolPointwiseAux3, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L11).

**Measurable kernel Hessian.** Every coordinate entry of the explicit kernel Hessian is measurable. Source: Breakdown.FundSol.Internal.measurable_kernelSecondDeriv in Breakdown.Uniqueness.FundSolPointwiseAux3, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L15).

**Symmetric kernel Hessian.** Exchanging the coordinate indices leaves the kernel Hessian unchanged. Source: Breakdown.FundSol.Internal.kernelSecondDeriv_symm in Breakdown.Uniqueness.FundSolPointwiseAux3, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L22).

**Linear bound at a source zero.** A smooth compactly supported function vanishing at `x₀` is bounded by a constant times distance from `x₀`. Source: Breakdown.FundSol.Internal.exists_slope_bound in Breakdown.Uniqueness.FundSolPointwiseAux3, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L28).

**Second partial as a function.** The second partial of a smooth scalar function agrees as a function with the nested directional derivative. Source: Breakdown.FundSol.Internal.secondPartial_eq_fun in Breakdown.Uniqueness.FundSolPointwiseAux3, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L38).

**Continuous second partial.** A second partial derivative of a smooth scalar function is continuous. Source: Breakdown.FundSol.Internal.continuous_secondPartial in Breakdown.Uniqueness.FundSolPointwiseAux3, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L42).

**Uniform second-partial bound.** A smooth compactly supported function has a globally bounded coordinate second partial. Source: Breakdown.FundSol.Internal.exists_secondPartial_bound in Breakdown.Uniqueness.FundSolPointwiseAux3, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L47).

**Cancel one singular kernel power.** A source vanishing linearly at `x₀` makes the Hessian integrand bounded by a constant times `‖x₀-y‖⁻²`. Source: Breakdown.FundSol.Internal.abs_kernelSecondDeriv_mul_le in Breakdown.Uniqueness.FundSolPointwiseAux3, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L55).

**Integrable cancelled singularity.** For a smooth compactly supported source vanishing at the evaluation point, the kernel-Hessian product is integrable. Source: Breakdown.FundSol.Internal.integrable_kernelSecondDeriv_mul_aux in Breakdown.Uniqueness.FundSolPointwiseAux3, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux3.lean#L63).

### Breakdown.Uniqueness.FundSolPointwiseAux4

This file passes the localized formulas to the limit and controls the remaining kernel errors.

Reading context: §5 and Appendix A.2; completion of the Hessian representation.

**Source namespace:** Breakdown.FundSol.Internal.

**Compact mollifier support.** A positive-scale mollifier has compact support. Source: Breakdown.FundSol.Internal.hasCompactSupport_mollifier in Breakdown.Uniqueness.FundSolPointwiseAux4, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L10).

**Open exterior region.** The set of points whose norm exceeds a fixed radius is open. Source: Breakdown.FundSol.Internal.isOpen_norm_gt in Breakdown.Uniqueness.FundSolPointwiseAux4, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L14).

**Mollifier Hessian vanishes outside.** Every second partial of a positive-scale mollifier vanishes strictly outside its radius. Source: Breakdown.FundSol.Internal.secondPartial_mollifier_eq_zero in Breakdown.Uniqueness.FundSolPointwiseAux4, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L17).

**Exterior Hessian equals kernel Hessian.** Strictly outside the mollifier radius, the Hessian of its potential equals the Newtonian kernel Hessian. Source: Breakdown.FundSol.Internal.secondPartial_potential_mollifier_far in Breakdown.Uniqueness.FundSolPointwiseAux4, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L25).

**Interior mollifier potential bound.** Inside its radius, the positive-scale mollifier potential is bounded by a constant times `ρ⁻¹`. Source: Breakdown.FundSol.Internal.exists_abs_potential_mollifier_le in Breakdown.Uniqueness.FundSolPointwiseAux4, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L35).

**Interior mollifier Hessian bound.** Inside its radius, the mollifier potential Hessian is bounded by a constant times `ρ⁻³`. Source: Breakdown.FundSol.Internal.exists_abs_secondPartial_potential_mollifier_le in Breakdown.Uniqueness.FundSolPointwiseAux4, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L47).

**Compact second-partial support.** A coordinate second partial of a smooth compactly supported function has compact support. Source: Breakdown.FundSol.Internal.hasCompactSupport_secondPartial in Breakdown.Uniqueness.FundSolPointwiseAux4, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L60).

**Near-kernel replacement error.** Replacing the kernel inside radius `ρ` by the stated regularised kernel changes the source-derivative integral by the displayed terms of order `ρ²`. Source: Breakdown.FundSol.Internal.near_estimate in Breakdown.Uniqueness.FundSolPointwiseAux4, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L65).

**Far-Hessian replacement error.** For a source vanishing linearly at the evaluation point, replacing the kernel Hessian inside radius `ρ` produces the stated error of order `ρ`. Source: Breakdown.FundSol.Internal.far_estimate in Breakdown.Uniqueness.FundSolPointwiseAux4, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L116).

**Vanishing error forces equality.** If `|a-b| ≤ Pρ²+Qρ` for every positive `ρ`, then `a=b`. Source: Breakdown.FundSol.Internal.eq_of_abs_sub_le in Breakdown.Uniqueness.FundSolPointwiseAux4, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPointwiseAux4.lean#L158).

### Breakdown.Uniqueness.FundSolPotential

This file defines convolution with the Newtonian kernel and proves its smoothness and Laplacian identity for smooth compactly supported data.

Reading context: §5 and Appendix A.2; construction of the pressure potential.

**Source namespace:** Breakdown.FundSol.

**Differentiating a C1 potential.** For a C1 compactly supported source, a directional derivative passes through the Newtonian potential. Source: Breakdown.FundSol.fderiv_potential_of_contDiff_one in Breakdown.Uniqueness.FundSolPotential, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L10).

**Derivative of linear-map evaluation.** Differentiating a family of linear maps after evaluation at a fixed vector gives the evaluated derivative. Source: Breakdown.FundSol.fderiv_apply_const in Breakdown.Uniqueness.FundSolPotential, line 22. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L22).

**Compact directional derivative support.** A directional derivative has compact support when the original scalar function does. Source: Breakdown.FundSol.hasCompactSupport_fderiv_apply in Breakdown.Uniqueness.FundSolPotential, line 28. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L28).

**Smooth directional derivatives.** Fixed directional derivatives of a smooth scalar function are smooth. Source: Breakdown.FundSol.contDiff_fderiv_apply in Breakdown.Uniqueness.FundSolPotential, line 32. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L32).

**Smooth potential from smooth data.** The potential of a smooth compactly supported source is smooth. Source: Breakdown.FundSol.contDiff_potential in Breakdown.Uniqueness.FundSolPotential, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L36).

**Potential commutes with derivatives.** For smooth compactly supported data, a directional derivative commutes with taking the Newtonian potential. Source: Breakdown.FundSol.fderiv_potential in Breakdown.Uniqueness.FundSolPotential, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L40).

**Potential commutes with second partials.** Taking a coordinate second partial commutes with the potential for smooth compactly supported sources. Source: Breakdown.FundSol.secondPartial_potential in Breakdown.Uniqueness.FundSolPotential, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L44).

**Additivity of the potential.** The potential of a sum of smooth compactly supported sources is the sum of their potentials. Source: Breakdown.FundSol.potential_add in Breakdown.Uniqueness.FundSolPotential, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L65).

**Scalar linearity of the potential.** Multiplying the source by a real scalar multiplies its potential by the same scalar. Source: Breakdown.FundSol.potential_smul in Breakdown.Uniqueness.FundSolPotential, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/FundSolPotential.lean#L72).

### Breakdown.Uniqueness.LocalBlowup

This file transfers the singular behavior of the constructed mild solution to the bounded-energy smooth-solution obstruction.

Reading context: §5 and Appendix A.2; the final physical contradiction.

**Source namespace:** Breakdown.

**Isometries preserve centered balls.** The inverse image of a centered ball under the inverse linear isometry is the same ball. Source: Breakdown.preimage_symm_ball_eq in Breakdown.Uniqueness.LocalBlowup, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalBlowup.lean#L10).

**Local L6 norm under rotation.** Pushing a measurable field forward by a linear isometry preserves its L6 norm on every centered ball. Source: Breakdown.eLpNorm_ball_pushForward in Breakdown.Uniqueness.LocalBlowup, line 15. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalBlowup.lean#L15).

**Local L6 norm of the realised rotation.** A field realization's rotation preserves the physical velocity's L6 norm on a centered ball. Source: Breakdown.eLpNorm_ball_rot in Breakdown.Uniqueness.LocalBlowup, line 32. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalBlowup.lean#L32).

**Nonzero mass in a finite ball.** A measurable field that is not almost everywhere zero has nonzero L6 mass in some integer-radius ball. Source: Breakdown.exists_ball_eLpNorm_ne_zero in Breakdown.Uniqueness.LocalBlowup, line 40. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalBlowup.lean#L40).

**Dilation preserves null-set equality.** Positive dilation preserves almost-everywhere equality of spatial fields. Source: Breakdown.dilateField_ae_congr in Breakdown.Uniqueness.LocalBlowup, line 52. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalBlowup.lean#L52).

**Local bound after dilation.** For dilation parameter at most one, a field bounded by `M` on the closed ball has dilated norm at most `√μ M` on the open ball. Source: Breakdown.norm_dilateField_le in Breakdown.Uniqueness.LocalBlowup, line 61. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalBlowup.lean#L61).

### Breakdown.Uniqueness.LocalEnergy

This file proves continuity and the exact time derivative of the cutoff-weighted energy of the difference of two smooth physical solutions.

Reading context: §5 and Appendix A.2; the local-energy balance.

**Source namespace:** Breakdown.

**Continuity of difference energy.** For two smooth solutions on the same closed time interval, their cutoff difference energy varies continuously in time. Source: Breakdown.continuousOn_cutoffEnergy in Breakdown.Uniqueness.LocalEnergy, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergy.lean#L13).

**Derivative of difference energy.** At interior times, the derivative of cutoff difference energy equals dissipation, cutoff diffusion, transport, stretching and pressure-difference terms. Source: Breakdown.hasDerivAt_cutoffEnergy in Breakdown.Uniqueness.LocalEnergy, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergy.lean#L18).

### Breakdown.Uniqueness.LocalEnergyAuxIbp

This file carries out the spatial integrations by parts behind the weighted local-energy identity.

Reading context: §5 and Appendix A.2; spatial differentiation of weighted energy.

**Source namespace:** Breakdown.

**Compact support from a common cutoff.** A function vanishing outside a compact cutoff's support has compact support. Source: Breakdown.ibp_hasCompactSupport_of_vanish in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L10).

**Integrability from a common cutoff.** A continuous function vanishing outside a compact cutoff's support is integrable. Source: Breakdown.ibp_integrable_of_vanish in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L15).

**Derivatives vanish off support.** Every iterated derivative vanishes outside the support of the original function. Source: Breakdown.ibp_iteratedFDeriv_out in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L20).

**Integral of a compact derivative.** The integral of a directional derivative of a smooth compactly supported scalar function is zero. Source: Breakdown.ibp_integral_fderiv_eq_zero in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L25).

**Smooth evaluated derivative.** Evaluating the derivative of a smooth field on a fixed direction gives a smooth field. Source: Breakdown.ibp_contDiff_fderiv_apply in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 40. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L40).

**Repeated derivative in one direction.** For a smooth field, differentiating twice in one direction equals the second derivative evaluated on that direction twice. Source: Breakdown.ibp_fderiv_fderiv_apply in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 44. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L44).

**Reconstructing a spatial vector.** The sum of each coordinate times its unit vector reconstructs the original vector. Source: Breakdown.ibp_sum_coord in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 51. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L51).

**Diffusion integration-by-parts flux.** The diffusion flux combines `φ⟨w,∂ᵢw⟩` with minus one half of `‖w‖²∂ᵢφ`. Source: Breakdown.sspFlux in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 54. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L54).

**Smooth diffusion flux.** The diffusion flux is smooth when its cutoff and velocity are smooth. Source: Breakdown.ibp_sspFlux_smooth in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 57. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L57).

**Derivative of the diffusion flux.** Differentiating the diffusion flux yields the squared directional derivative, the second velocity derivative and the second cutoff derivative. Source: Breakdown.ibp_sspFlux_deriv in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 62. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L62).

**Divergence of the diffusion flux.** Summing diffusion-flux derivatives gives local gradient energy plus the velocity Laplacian pairing minus the cutoff Laplacian correction. Source: Breakdown.ibp_ssp_pointwise in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 78. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L78).

**Continuous vector Laplacian.** The vector Laplacian of a smooth field is continuous. Source: Breakdown.ibp_continuous_sumSecondPartialsAt in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 86. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L86).

**Continuous scalar Laplacian.** The scalar Laplacian of a smooth function is continuous. Source: Breakdown.ibp_continuous_scalarSumSecondPartials in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 95. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L95).

**Integral of a compact divergence.** The integral of the coordinate divergence of a smooth compactly supported flux is zero. Source: Breakdown.ibp_integral_sum_fderiv_eq_zero in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 104. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L104).

**Local diffusion energy identity.** Integration by parts converts the cutoff velocity-Laplacian pairing into negative cutoff gradient energy plus one half of the cutoff Laplacian term. Source: Breakdown.integral_mul_inner_sumSecondPartialsAt in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 113. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L113).

**Transport integration-by-parts flux.** The transport flux in direction `i` is `φ‖w‖²vᵢ`. Source: Breakdown.transFlux in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 138. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L138).

**Smooth transport flux.** The transport flux is smooth when all its input fields are smooth. Source: Breakdown.ibp_transFlux_smooth in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 141. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L141).

**Derivative of the transport flux.** The transport flux derivative separates derivatives of the advecting field, the velocity magnitude and the cutoff. Source: Breakdown.ibp_transFlux_deriv in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 146. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L146).

**Divergence of the transport flux.** The transport-flux divergence equals the velocity-divergence term plus twice the transport pairing and the cutoff-gradient term. Source: Breakdown.ibp_trans_pointwise in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 161. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L161).

**Local transport integration by parts.** For a divergence-free advecting field, the cutoff transport pairing equals minus one half of the cutoff-gradient flux. Source: Breakdown.integral_mul_inner_fderiv_transport in Breakdown.Uniqueness.LocalEnergyAuxIbp, line 177. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxIbp.lean#L177).

### Breakdown.Uniqueness.LocalEnergyAuxTime

This file justifies time differentiation and time integration of the cutoff-weighted energy.

Reading context: §5 and Appendix A.2; the time-dependent local-energy calculation.

**Source namespace:** Breakdown.Internal.CutoffEnergy.

**Smooth energy cutoff.** The fourth-power cutoff is smooth for positive radius. Source: Breakdown.Internal.CutoffEnergy.contDiff_cutoffPow in Breakdown.Uniqueness.LocalEnergyAuxTime, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L10).

**Energy cutoff vanishes outside.** The fourth-power cutoff vanishes outside the closed ball of twice its positive radius. Source: Breakdown.Internal.CutoffEnergy.cutoffPow_eq_zero in Breakdown.Uniqueness.LocalEnergyAuxTime, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L14).

**Support controlled by the cutoff.** A function vanishing wherever the energy cutoff vanishes has compact support. Source: Breakdown.Internal.CutoffEnergy.hasCompactSupport_of_cutoffPow in Breakdown.Uniqueness.LocalEnergyAuxTime, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L21).

**Compact energy-cutoff support.** The energy cutoff has compact support for positive radius. Source: Breakdown.Internal.CutoffEnergy.hasCompactSupport_cutoffPow in Breakdown.Uniqueness.LocalEnergyAuxTime, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L25).

**Absolute energy cutoff at most one.** The absolute value of the fourth-power cutoff is at most one. Source: Breakdown.Internal.CutoffEnergy.abs_cutoffPow_le_one in Breakdown.Uniqueness.LocalEnergyAuxTime, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L28).

**Integrability after a cutoff.** Multiplying a continuous scalar function by the energy cutoff gives an integrable function. Source: Breakdown.Internal.CutoffEnergy.integrable_cutoffPow_mul in Breakdown.Uniqueness.LocalEnergyAuxTime, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L34).

**Smooth spatial slices.** A spacetime function smooth on the closed time slab has a smooth spatial slice at every time in that slab. Source: Breakdown.Internal.CutoffEnergy.contDiff_slice in Breakdown.Uniqueness.LocalEnergyAuxTime, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L39).

**Time derivative of a slice.** At an interior time, the time derivative of a spacetime slice is its total derivative in direction `(1,0)`. Source: Breakdown.Internal.CutoffEnergy.hasDerivAt_slice_time in Breakdown.Uniqueness.LocalEnergyAuxTime, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L47).

**Continuous time-direction derivative.** The time-direction derivative of a smooth spacetime field is continuous on the open time slab. Source: Breakdown.Internal.CutoffEnergy.continuousOn_fderiv_slice_time in Breakdown.Uniqueness.LocalEnergyAuxTime, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L59).

**Continuous cutoff difference energy.** The cutoff energy of the difference of two solutions is continuous on their closed time interval. Source: Breakdown.Internal.CutoffEnergy.continuousOn_cutoffEnergy_sub in Breakdown.Uniqueness.LocalEnergyAuxTime, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L68).

**Differentiating the energy integral.** At interior times, cutoff difference energy differentiates to the integral pairing the velocity difference with its time derivative. Source: Breakdown.Internal.CutoffEnergy.hasDerivAt_cutoffEnergy_inner in Breakdown.Uniqueness.LocalEnergyAuxTime, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/LocalEnergyAuxTime.lean#L104).

### Breakdown.Uniqueness.MildUnique

This file compares a smooth physical solution with the regular physical reconstruction of the abstract mild solution.

Reading context: §5 and Appendix A.2; matching the two solution descriptions.

**Source namespace:** Breakdown.

**Difference of quadratic bilinear terms.** The norm of `B(x,x)-B(y,y)` is bounded by `‖B‖‖x-y‖(‖x‖+‖y‖)`. Source: Breakdown.bilin_sub_norm_le in Breakdown.Uniqueness.MildUnique, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MildUnique.lean#L10).

**Integral of the mild singular kernel.** The integral of `(t-s)^(-3/4)` from `c` to `t` is `4(t-c)^(1/4)`. Source: Breakdown.integral_sub_rpow_neg_three_quarters in Breakdown.Uniqueness.MildUnique, line 19. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MildUnique.lean#L19).

**Integrable mild singular kernel.** The three-quarter-power singular kernel is interval integrable between any two real endpoints. Source: Breakdown.intervalIntegrable_sub_rpow_neg_three_quarters in Breakdown.Uniqueness.MildUnique, line 28. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MildUnique.lean#L28).

**Short-time mild difference bound.** Two bounded mild solutions already equal up to `c` have their later difference bounded by the stated constant times `(t-c)^(1/4)`. Source: Breakdown.mild_difference_estimate in Breakdown.Uniqueness.MildUnique, line 34. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MildUnique.lean#L34).

**Source namespace:** Breakdown.MildFramework.

**Uniqueness of mild solutions.** For a bilinear kernel bounded by `Cτ^(-3/4)`, mild solutions with equal initial data agree throughout the closed time interval. Source: Breakdown.MildFramework.eq_of_isMildOnIcc in Breakdown.Uniqueness.MildUnique, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MildUnique.lean#L100).

### Breakdown.Uniqueness.MixedStress

This file bounds mixed tensor stresses by Hölder estimates adapted to the cutoff energy and the L6 velocity norm.

Reading context: §5 and Appendix A.2; mixed pressure terms in the uniqueness estimate.

**Source namespace:** Breakdown.

**Young bound for a triple product.** Bounding the first factor of a triple product gives the stated Young inequality with adjustable positive parameter `l`. Source: Breakdown.abs_triple_le in Breakdown.Uniqueness.MixedStress, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L13).

**Young bound with the second factor.** Bounding the second factor gives the symmetric Young inequality for the triple product. Source: Breakdown.abs_triple_le' in Breakdown.Uniqueness.MixedStress, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L25).

**Matrix pairing with a bounded left field.** A tensor-Hessian pairing with bounded left vector is controlled by the right vector's energy and the matrix's squared entries. Source: Breakdown.abs_pairing_le_left in Breakdown.Uniqueness.MixedStress, line 31. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L31).

**Matrix pairing with bounded right input.** A tensor-Hessian pairing with bounded right vector is controlled by the left vector's energy and the matrix's squared entries. Source: Breakdown.abs_pairing_le_right in Breakdown.Uniqueness.MixedStress, line 47. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L47).

**Integral bound by domination.** An integrable pointwise upper bound on `|F|` bounds the absolute integral of `F`. Source: Breakdown.abs_integral_le_of_pointwise in Breakdown.Uniqueness.MixedStress, line 63. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L63).

**Finite-energy integral and bound.** Finite-energy data give both integrability of squared velocity and the bound by `A²`. Source: Breakdown.integrable_and_integral_sq_le in Breakdown.Uniqueness.MixedStress, line 72. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L72).

**Cutoff source in flux form.** For a smooth divergence-free field, the cutoff source is four times the cutoff cubed times the cutoff flux. Source: Breakdown.cutoffSource_fun_eq in Breakdown.Uniqueness.MixedStress, line 85. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L85).

**Smooth cutoff source.** The cutoff source is smooth for a smooth divergence-free field and positive radius. Source: Breakdown.contDiff_cutoffSource in Breakdown.Uniqueness.MixedStress, line 92. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L92).

**Compact cutoff-source support.** The cutoff source has compact support for a smooth divergence-free field and positive radius. Source: Breakdown.hasCompactSupport_cutoffSource in Breakdown.Uniqueness.MixedStress, line 98. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L98).

**Squared cutoff-source bound.** The squared cutoff source is bounded by `16(c/r)²‖w‖²` when the cutoff derivative is bounded by `c/r`. Source: Breakdown.sq_cutoffSource_le in Breakdown.Uniqueness.MixedStress, line 104. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L104).

**Mixed pressure-stress bound.** For admissible difference data and `r ≥ 1`, the sum of the two mixed stresses is bounded by `C U₀ A²/r`. Source: Breakdown.mixed_stress_le in Breakdown.Uniqueness.MixedStress, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/MixedStress.lean#L128).

### Breakdown.Uniqueness.PressureAverage

This file averages the pressure defect with broad mollifiers and proves that the defect vanishes as the averaging radius tends to infinity.

Reading context: §5 and Appendix A.2; identification of the physical pressure gradient.

**Source namespace:** Breakdown.

**Three-term absolute-value bound.** The absolute value of `a+b-c` is at most `|a|+|b|+|c|`. Source: Breakdown.abs_add_sub_le_three in Breakdown.Uniqueness.PressureAverage, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverage.lean#L14).

**Time-integrated pressure defect.** The stated field-pairing and stress bounds control the integrated pressure defect by `2β+δ(t₂-t₁)`. Source: Breakdown.abs_integral_pressureDefect_le in Breakdown.Uniqueness.PressureAverage, line 19. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverage.lean#L19).

**Broad averaging removes pressure error.** The time-integrated pressure defect against a mollified compact test field tends to zero as the mollifier radius tends to infinity. Source: Breakdown.tendsto_integral_pressureDefect_mollify in Breakdown.Uniqueness.PressureAverage, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverage.lean#L84).

### Breakdown.Uniqueness.PressureAverageAuxBound

This file controls the broad-mollifier pressure terms by derivative bounds and weighted stress estimates.

Reading context: §5 and Appendix A.2; bounds for pressure averaging.

**Source namespace:** Breakdown.Internal.

**One energy bound on a closed interval.** A solution with energy bounded on the interval has continuous spatial slices and one real bound for their squared-velocity integrals. Source: Breakdown.Internal.exists_energy_bound in Breakdown.Uniqueness.PressureAverageAuxBound, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L11).

**Cubic scaling of ball volume.** The volume of every nonnegative-radius closed ball is one fixed constant times the radius cubed. Source: Breakdown.Internal.exists_volume_closedBall_eq in Breakdown.Uniqueness.PressureAverageAuxBound, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L28).

**Pairing bound from compact support.** A bounded test field supported in a ball gives the stated energy-volume pairing bound with any positive parameter `ε`. Source: Breakdown.Internal.abs_integral_inner_le_of_support in Breakdown.Uniqueness.PressureAverageAuxBound, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L34).

**Norm of a coordinate direction.** Every coordinate unit vector has norm one. Source: Breakdown.Internal.norm_unitVector_eq in Breakdown.Uniqueness.PressureAverageAuxBound, line 74. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L74).

**Vector Laplacian versus Hessian norm.** The vector Laplacian norm is at most three times the second derivative norm. Source: Breakdown.Internal.norm_sumSecondPartialsAt_le in Breakdown.Uniqueness.PressureAverageAuxBound, line 77. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L77).

**Continuous Laplacian of a test field.** The vector Laplacian of a smooth test field is continuous. Source: Breakdown.Internal.continuous_sumSecondPartialsAt_of in Breakdown.Uniqueness.PressureAverageAuxBound, line 91. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L91).

**Laplacian vanishes beyond support.** A vector field vanishing outside a radius has zero Laplacian strictly beyond that radius. Source: Breakdown.Internal.sumSecondPartialsAt_eq_zero_of in Breakdown.Uniqueness.PressureAverageAuxBound, line 98. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L98).

**Pairing with a test-field Laplacian.** A bound on the test field's second derivative gives the stated energy-volume bound for its Laplacian pairing. Source: Breakdown.Internal.abs_integral_inner_sumSecondPartialsAt_le in Breakdown.Uniqueness.PressureAverageAuxBound, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L114).

**Energy bound for a quadratic stress.** A matrix coefficient bounded by `M` controls the integrated quadratic stress by nine times `M` times velocity energy. Source: Breakdown.Internal.abs_integral_sum_stress_le in Breakdown.Uniqueness.PressureAverageAuxBound, line 123. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L123).

**Stress from a bounded derivative.** A test-field derivative bounded by `M` controls the corresponding quadratic stress integral by nine times `M` times energy. Source: Breakdown.Internal.abs_integral_fderiv_stress_le in Breakdown.Uniqueness.PressureAverageAuxBound, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L154).

**Hessian stress from an energy bound.** A scalar Hessian bounded entrywise by `M` controls its self-stress pairing by nine times `M` times energy. Source: Breakdown.Internal.abs_stressPairing_self_le in Breakdown.Uniqueness.PressureAverageAuxBound, line 167. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxBound.lean#L167).

### Breakdown.Uniqueness.PressureAverageAuxField

This file proves smoothness, compact support and derivative bounds for broadly mollified vector test fields.

Reading context: §5 and Appendix A.2; field identities in the pressure-average argument.

**Source namespace:** Breakdown.Internal.

**Compact support of a positive mollifier.** The mollifier has compact support for positive radius. Source: Breakdown.Internal.field_mollifier_compact in Breakdown.Uniqueness.PressureAverageAuxField, line 11. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L11).

**Mollification is convolution.** Vector-field mollification is exactly scalar multiplication convolution with the mollifier. Source: Breakdown.Internal.field_mollify_eq in Breakdown.Uniqueness.PressureAverageAuxField, line 17. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L17).

**Smooth mollified test field.** Mollifying a smooth compactly supported field gives a smooth field. Source: Breakdown.Internal.contDiff_mollify_field in Breakdown.Uniqueness.PressureAverageAuxField, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L20).

**Compact mollified field support.** Mollifying a smooth compactly supported field with a positive-radius mollifier preserves compact support. Source: Breakdown.Internal.hasCompactSupport_mollify_field in Breakdown.Uniqueness.PressureAverageAuxField, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L26).

**Convolution bound from a uniform factor.** Convolving a uniformly bounded factor with an integrable factor is bounded by the bilinear operator norm times the uniform bound and L1 norm. Source: Breakdown.Internal.field_norm_convolution_le in Breakdown.Uniqueness.PressureAverageAuxField, line 31. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L31).

**A radius containing compact support.** A compactly supported vector field vanishes outside some nonnegative radius. Source: Breakdown.Internal.field_support_radius in Breakdown.Uniqueness.PressureAverageAuxField, line 46. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L46).

**Support radius after mollification.** Mollifying a field supported within radius `R` by a radius-`ρ` mollifier gives zero outside radius `R+ρ`. Source: Breakdown.Internal.field_mollify_eq_zero in Breakdown.Uniqueness.PressureAverageAuxField, line 53. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L53).

**Bounds for a broadened test field.** For radii at least one, the mollified field and its first two derivatives obey the stated `ρ⁻³`, `ρ⁻⁴`, and `ρ⁻⁵` bounds. Source: Breakdown.Internal.mollify_field_bounds in Breakdown.Uniqueness.PressureAverageAuxField, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxField.lean#L67).

### Breakdown.Uniqueness.PressureAverageAuxIdentity

This file establishes the convolution and differentiation identities that express the averaged pressure defect.

Reading context: §5 and Appendix A.2; the pressure-average identity.

**Source namespace:** Breakdown.Internal.

**Smooth directional derivative field.** The derivative of a smooth field evaluated on a fixed direction is smooth. Source: Breakdown.Internal.idt_contDiff_fderiv_apply in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 11. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L11).

**Differentiability of a smooth field.** A smooth field is differentiable. Source: Breakdown.Internal.idt_differentiable in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L16).

**Second derivative along one direction.** The second derivative evaluated twice on a direction equals the corresponding nested directional derivative. Source: Breakdown.Internal.idt_iteratedFDeriv_two in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L20).

**Vector Laplacian as repeated derivatives.** The vector Laplacian is the sum of the three repeated coordinate directional derivatives. Source: Breakdown.Internal.idt_sumSecondPartialsAt_eq in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 28. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L28).

**Coordinate expansion of a vector.** Summing the coordinate multiples of unit vectors gives the original vector. Source: Breakdown.Internal.idt_sum_coord in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L33).

**Integrability under compact support.** A continuous scalar function supported inside a compactly supported test field's support is integrable. Source: Breakdown.Internal.idt_integrable in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 37. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L37).

**Integral of a directional derivative.** A smooth compactly supported scalar function has zero integral of each directional derivative. Source: Breakdown.Internal.idt_integral_fderiv_eq_zero in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 41. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L41).

**Integral of coordinate divergence.** A smooth compactly supported coordinate flux has zero integral of its summed directional derivatives. Source: Breakdown.Internal.idt_integral_sum_fderiv_eq_zero in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 46. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L46).

**Vanishing jets outside support.** A field, its first derivative and its second derivative all vanish outside its support. Source: Breakdown.Internal.idt_vanish in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 53. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L53).

**Moving the vector Laplacian.** For smooth fields and a compactly supported test field, the Laplacian can be moved between the two factors of the integral pairing. Source: Breakdown.Internal.idt_sumSecondPartials_identity in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 58. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L58).

**Advection as a stress divergence.** Pairing advection of a divergence-free smooth field with a compact test field equals the negative stress pairing with the test derivative. Source: Breakdown.Internal.idt_advection_identity in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 107. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L107).

**Pressure-defect evolution identity.** At interior times, the velocity-pairing derivative plus the pressure defect equals the test Laplacian, derivative stress and Newtonian stress terms. Source: Breakdown.Internal.integral_time_derivative_add_pressureDefect in Breakdown.Uniqueness.PressureAverageAuxIdentity, line 176. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxIdentity.lean#L176).

### Breakdown.Uniqueness.PressureAverageAuxStress

This file differentiates the stress-generated pressure source and bounds it by derivatives of the test kernel.

Reading context: §5 and Appendix A.2; stress terms in the averaged pressure equation.

**Source namespace:** Breakdown.Internal.

**Support inside a closed ball.** Vanishing strictly beyond radius `r` places the topological support inside the closed radius-`r` ball. Source: Breakdown.Internal.tsupport_subset_closedBall_aux in Breakdown.Uniqueness.PressureAverageAuxStress, line 11. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress.lean#L11).

**Second divergence derivatives vanish far.** If a field vanishes beyond radius `r`, the second partials of its divergence vanish strictly beyond that radius. Source: Breakdown.Internal.secondPartial_div_eq_zero_aux in Breakdown.Uniqueness.PressureAverageAuxStress, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress.lean#L18).

**Third derivatives bound the source.** A second partial of a field's divergence is bounded by the divergence operator norm times the field's third derivative norm. Source: Breakdown.Internal.abs_secondPartial_div_le_aux in Breakdown.Uniqueness.PressureAverageAuxStress, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress.lean#L33).

**Third derivative of a mollified field.** The third derivative of a mollified compact smooth field is bounded by a nonnegative constant times `ρ⁻⁶`. Source: Breakdown.Internal.norm_iteratedFDeriv_three_mollify_le_aux in Breakdown.Uniqueness.PressureAverageAuxStress, line 46. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress.lean#L46).

**Mollified pressure Hessian bound.** For mollifier radii at least one, the Hessian of the divergence potential is bounded by a constant times `ρ⁻³`. Source: Breakdown.Internal.abs_secondPartial_potential_div_mollify_le in Breakdown.Uniqueness.PressureAverageAuxStress, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress.lean#L60).

### Breakdown.Uniqueness.PressureAverageAuxStress2

This file controls the tensor contractions and convolutions used to estimate the averaged stress contribution.

Reading context: §5 and Appendix A.2; quantitative stress bounds for broad averaging.

**Source namespace:** Breakdown.Internal.

**Derivative bound for convolution.** An order-`k` bound on the smooth convolution factor bounds the convolved derivative by the bilinear norm and the other factor's L1 norm. Source: Breakdown.Internal.norm_iteratedFDeriv_convolution_field_le in Breakdown.Uniqueness.PressureAverageAuxStress2, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L11).

**Smooth unscaled pressure bump.** The unscaled mollifier bump used in the pressure estimates is smooth. Source: Breakdown.Internal.contDiff_bump_aux in Breakdown.Uniqueness.PressureAverageAuxStress2, line 47. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L47).

**Bump vanishes beyond unit radius.** The unscaled mollifier bump vanishes when the norm exceeds one. Source: Breakdown.Internal.bump_eq_zero_aux in Breakdown.Uniqueness.PressureAverageAuxStress2, line 52. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L52).

**Compact pressure bump support.** The unscaled pressure mollifier bump has compact support. Source: Breakdown.Internal.hasCompactSupport_bump_aux in Breakdown.Uniqueness.PressureAverageAuxStress2, line 57. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L57).

**Mollifier as a scaled bump.** The mollifier is a rescaled bump multiplied by the reciprocal of `ρ³` times its normalising integral. Source: Breakdown.Internal.mollifier_eq_aux in Breakdown.Uniqueness.PressureAverageAuxStress2, line 62. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L62).

**Smooth rescaled mollifier.** The rescaled mollifier is smooth for every real scale. Source: Breakdown.Internal.contDiff_mollifier_aux in Breakdown.Uniqueness.PressureAverageAuxStress2, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L68).

**Support of a rescaled mollifier.** The rescaled mollifier has compact support for positive scale. Source: Breakdown.Internal.hasCompactSupport_mollifier_aux in Breakdown.Uniqueness.PressureAverageAuxStress2, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L73).

**Derivative scaling of the mollifier.** The order-`k` derivative of the mollifier has a nonnegative uniform bound proportional to `ρ^(-k-3)`. Source: Breakdown.Internal.norm_iteratedFDeriv_mollifier_aux in Breakdown.Uniqueness.PressureAverageAuxStress2, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L82).

**Global potential bound from support.** A scalar source bounded by `A` and supported in a positive-radius ball has potential bounded everywhere by `AKr²`. Source: Breakdown.Internal.abs_potential_le_of_support in Breakdown.Uniqueness.PressureAverageAuxStress2, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxStress2.lean#L112).

### Breakdown.Uniqueness.PressureAverageAuxTime

This file supplies time-continuity and integrability facts for the pressure-average identity.

Reading context: §5 and Appendix A.2; the time-dependent pressure comparison.

**Source namespace:** Breakdown.Internal.

**Pairing vanishes off test support.** The inner product with a test field vanishes at every point outside that field's support. Source: Breakdown.Internal.inner_field_eq_zero in Breakdown.Uniqueness.PressureAverageAuxTime, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxTime.lean#L10).

**Time continuity of test pairings.** A smooth spacetime field paired with a continuous compactly supported test field gives a continuous function of time on the closed interval. Source: Breakdown.Internal.continuousOn_integral_inner_field in Breakdown.Uniqueness.PressureAverageAuxTime, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxTime.lean#L14).

**Differentiating a time test pairing.** At an interior time, the derivative of a compact spatial test pairing is the integral pairing with the velocity's time derivative. Source: Breakdown.Internal.hasDerivAt_integral_inner_field in Breakdown.Uniqueness.PressureAverageAuxTime, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureAverageAuxTime.lean#L26).

### Breakdown.Uniqueness.PressureContinuity

This file proves continuity of the pressure expressions obtained from the Newtonian kernel and the evolving velocity.

Reading context: §5 and Appendix A.2; regularity of reconstructed pressure.

**Source namespace:** Breakdown.

**Smooth divergence of a field.** The divergence of a smooth vector field is smooth. Source: Breakdown.contDiff_divergence_field in Breakdown.Uniqueness.PressureContinuity, line 12. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L12).

**Compact divergence support.** The divergence of a compactly supported field has compact support. Source: Breakdown.hasCompactSupport_divergence_field in Breakdown.Uniqueness.PressureContinuity, line 22. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L22).

**Spatial derivative on a closed slab.** A spatial slice derivative agrees with the spacetime derivative within the closed slab in direction `(0,w)`. Source: Breakdown.fderiv_slice_eq_fderivWithin in Breakdown.Uniqueness.PressureContinuity, line 28. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L28).

**Continuous pressure-gradient pairing.** A smooth pressure on a positive closed time interval has continuous gradient pairings against compactly supported continuous fields. Source: Breakdown.continuousOn_integral_inner_gradient in Breakdown.Uniqueness.PressureContinuity, line 43. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L43).

**Quadratic pressure-stress density.** The quadratic stress density contracts two velocity factors with the scalar Hessian. Source: Breakdown.quadraticStress in Breakdown.Uniqueness.PressureContinuity, line 64. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L64).

**Quadratic-form coefficient bound.** A matrix bounded entrywise by `K` gives an absolute quadratic form bounded by `9K‖a‖²`. Source: Breakdown.abs_quadratic_form_le in Breakdown.Uniqueness.PressureContinuity, line 67. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L67).

**Weakening the Hessian decay bound.** A cubic spatial decay bound on the Hessian yields the stated inverse-radius bound on each second partial. Source: Breakdown.abs_secondPartial_le_decay in Breakdown.Uniqueness.PressureContinuity, line 89. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L89).

**Continuity of a smooth second partial.** Each coordinate second partial of a smooth scalar function is continuous. Source: Breakdown.continuous_secondPartial_of_smooth in Breakdown.Uniqueness.PressureContinuity, line 104. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L104).

**Time continuity of self-stress.** Continuous velocity with a uniform energy bound has continuous self-stress against the stated decaying smooth Hessian. Source: Breakdown.continuousOn_stressPairing_self in Breakdown.Uniqueness.PressureContinuity, line 109. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L109).

**Continuous pressure defect.** For a solution with energy bounded on the closed interval, the pressure defect against a compact smooth test field is continuous in time. Source: Breakdown.continuousOn_pressureDefect in Breakdown.Uniqueness.PressureContinuity, line 212. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureContinuity.lean#L212).

### Breakdown.Uniqueness.PressureIdentity

This file identifies the physical pressure contribution with the stress-generated Newtonian potential.

Reading context: §5 and Appendix A.2; the pressure formula used in physical uniqueness.

**Source namespace:** Breakdown.

**Zero integrated pressure defect.** The pressure defect against a smooth compact test field integrates to zero on every subinterval of the solution interval. Source: Breakdown.integral_pressureDefect_eq_zero in Breakdown.Uniqueness.PressureIdentity, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureIdentity.lean#L12).

**Pressure defect is zero.** For an energy-bounded solution, the pressure defect against every smooth compact test field vanishes at each interior time. Source: Breakdown.pressureDefect_eq_zero in Breakdown.Uniqueness.PressureIdentity, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureIdentity.lean#L34).

### Breakdown.Uniqueness.PressureMollify

This file relates mollified pressure to the pressure potential of the mollified stress and isolates the harmonic defect.

Reading context: §5 and Appendix A.2; mollification of the pressure equation.

**Source namespace:** Breakdown.

**Interchanging integral and matrix sum.** For integrable entries, the integral of a double three-coordinate sum equals the double sum of integrals. Source: Breakdown.integral_sum_sum in Breakdown.Uniqueness.PressureMollify, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollify.lean#L14).

**Scalar Laplacian integration by parts.** A scalar Laplacian can be moved between smooth factors in an integral when the differentiated test factor is compactly supported. Source: Breakdown.integral_mul_scalarSumSecondPartials in Breakdown.Uniqueness.PressureMollify, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollify.lean#L20).

**Stress from the pressure equation.** For the stated pressure Poisson equation, the difference of two Hessian stress pairings equals the negative pressure pairing with their Laplacian difference. Source: Breakdown.stress_difference in Breakdown.Uniqueness.PressureMollify, line 38. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollify.lean#L38).

**Pressure under compact replacement.** Replacing a compact test field preserves the pressure defect when the difference of its divergence potentials is compactly supported. Source: Breakdown.pressureDefect_eq_of_hasCompactSupport in Breakdown.Uniqueness.PressureMollify, line 100. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollify.lean#L100).

**Mollification preserves the defect.** At interior times, mollifying a compact smooth test field by any positive radius leaves its pressure defect unchanged. Source: Breakdown.pressureDefect_mollify in Breakdown.Uniqueness.PressureMollify, line 139. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollify.lean#L139).

### Breakdown.Uniqueness.PressureMollifyAux

This file proves the convolution, differentiation and Poisson identities required to mollify the pressure equation.

Reading context: §5 and Appendix A.2; technical identities for pressure mollification.

**Source namespace:** Breakdown.Internal.PressureMollify.

**Infinite regularity is nonzero.** The infinite smoothness index differs from zero. Source: Breakdown.Internal.PressureMollify.infty_ne_zero in Breakdown.Uniqueness.PressureMollifyAux, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L10).

**Infinite regularity includes order two.** The infinite smoothness index is at least two. Source: Breakdown.Internal.PressureMollify.two_le_infty in Breakdown.Uniqueness.PressureMollifyAux, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L12).

**Smooth directional derivatives.** A fixed directional derivative of a smooth scalar function is smooth. Source: Breakdown.Internal.PressureMollify.contDiff_fderiv_apply in Breakdown.Uniqueness.PressureMollifyAux, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L15).

**Compact derivative support.** A fixed directional derivative preserves compact support. Source: Breakdown.Internal.PressureMollify.hasCompactSupport_fderiv_apply in Breakdown.Uniqueness.PressureMollifyAux, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L19).

**Directional integration by parts.** Moving a derivative from a smooth compactly supported factor to the other smooth factor changes the sign of the integral. Source: Breakdown.Internal.PressureMollify.integral_mul_fderiv in Breakdown.Uniqueness.PressureMollifyAux, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L23).

**Coordinate Hessian as nested derivatives.** The coordinate Hessian entry equals successive derivatives along the two coordinate directions. Source: Breakdown.Internal.PressureMollify.secondPartial_eq in Breakdown.Uniqueness.PressureMollifyAux, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L38).

**Second-partial integration by parts.** Moving two coordinate derivatives from a compactly supported factor reverses their order and preserves the integral's sign. Source: Breakdown.Internal.PressureMollify.integral_mul_secondPartial in Breakdown.Uniqueness.PressureMollifyAux, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L46).

**Divergence as a linear operator.** The divergence operator on derivative matrices sums their coordinate diagonal entries. Source: Breakdown.Internal.PressureMollify.divergenceMap in Breakdown.Uniqueness.PressureMollifyAux, line 61. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L61).

**Evaluating the divergence operator.** Applying the divergence operator to a linear map gives the sum of its three diagonal coordinate evaluations. Source: Breakdown.Internal.PressureMollify.divergenceMap_apply in Breakdown.Uniqueness.PressureMollifyAux, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L65).

**Divergence from the derivative.** The divergence of a vector field is the divergence linear operator composed with its derivative map. Source: Breakdown.Internal.PressureMollify.divergenceAt_eq_comp in Breakdown.Uniqueness.PressureMollifyAux, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L69).

**Smooth divergence.** The divergence of a smooth vector field is smooth. Source: Breakdown.Internal.PressureMollify.contDiff_divergenceAt in Breakdown.Uniqueness.PressureMollifyAux, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L73).

**Support of the divergence.** The divergence of a compactly supported vector field has compact support. Source: Breakdown.Internal.PressureMollify.hasCompactSupport_divergenceAt in Breakdown.Uniqueness.PressureMollifyAux, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L77).

**Gradient pairing in coordinates.** Pairing a scalar gradient with a vector equals the sum of coordinate derivatives times vector coordinates. Source: Breakdown.Internal.PressureMollify.inner_gradientAt in Breakdown.Uniqueness.PressureMollifyAux, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L81).

**Coordinate derivative formula.** Selecting a coordinate commutes with differentiating a smooth vector field. Source: Breakdown.Internal.PressureMollify.fderiv_component in Breakdown.Uniqueness.PressureMollifyAux, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L85).

**Smooth coordinate functions.** Each coordinate function of a smooth vector field is smooth. Source: Breakdown.Internal.PressureMollify.contDiff_component in Breakdown.Uniqueness.PressureMollifyAux, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L94).

**Continuous coordinate functions.** Each coordinate function of a continuous vector field is continuous. Source: Breakdown.Internal.PressureMollify.continuous_component in Breakdown.Uniqueness.PressureMollifyAux, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L98).

**Compact support of coordinates.** Each coordinate of a compactly supported vector field has compact support. Source: Breakdown.Internal.PressureMollify.hasCompactSupport_component in Breakdown.Uniqueness.PressureMollifyAux, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L102).

**Gradient-divergence integration by parts.** The integral pairing of a smooth scalar gradient with a compact smooth field equals minus the scalar pairing with its divergence. Source: Breakdown.Internal.PressureMollify.integral_inner_gradientAt in Breakdown.Uniqueness.PressureMollifyAux, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L106).

**Integrability from finite energy.** A continuous field with finite squared-norm lower integral has integrable squared norm. Source: Breakdown.Internal.PressureMollify.integrable_norm_sq in Breakdown.Uniqueness.PressureMollifyAux, line 131. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L131).

**Hessian entry bound.** Each second partial is bounded in absolute value by the full second derivative norm. Source: Breakdown.Internal.PressureMollify.abs_secondPartial_le in Breakdown.Uniqueness.PressureMollifyAux, line 138. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L138).

**Smooth coordinate Hessian.** Every coordinate second partial of a smooth scalar function is smooth. Source: Breakdown.Internal.PressureMollify.contDiff_secondPartial in Breakdown.Uniqueness.PressureMollifyAux, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L143).

**Compact coordinate Hessian support.** A second partial of a smooth compactly supported function has compact support. Source: Breakdown.Internal.PressureMollify.hasCompactSupport_secondPartial in Breakdown.Uniqueness.PressureMollifyAux, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L150).

**Integrable pressure-stress entries.** Finite velocity energy and a globally bounded smooth Hessian make each quadratic stress entry integrable. Source: Breakdown.Internal.PressureMollify.integrable_stress in Breakdown.Uniqueness.PressureMollifyAux, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L158).

**Bounded potential Hessian.** The potential of a smooth compactly supported source has a globally bounded second derivative. Source: Breakdown.Internal.PressureMollify.bound_iteratedFDeriv_two_potential in Breakdown.Uniqueness.PressureMollifyAux, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L172).

**Second partials preserve subtraction.** Taking a coordinate second partial distributes over subtraction of smooth functions. Source: Breakdown.Internal.PressureMollify.secondPartial_sub in Breakdown.Uniqueness.PressureMollifyAux, line 185. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux.lean#L185).

### Breakdown.Uniqueness.PressureMollifyAux2

This file controls the exterior potential and the limiting terms in the mollified pressure representation.

Reading context: §5 and Appendix A.2; exterior estimates for pressure mollification.

**Source namespace:** Breakdown.Internal.PressureMollify.

**Compact mollifier support.** Every positive-radius mollifier has compact support. Source: Breakdown.Internal.PressureMollify.hasCompactSupport_mollifier in Breakdown.Uniqueness.PressureMollifyAux2, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L11).

**Smooth mollification.** Mollification of a smooth compactly supported field is smooth. Source: Breakdown.Internal.PressureMollify.contDiff_mollify in Breakdown.Uniqueness.PressureMollifyAux2, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L17).

**Compact support after mollification.** Mollifying a compactly supported field with positive radius preserves compact support. Source: Breakdown.Internal.PressureMollify.hasCompactSupport_mollify in Breakdown.Uniqueness.PressureMollifyAux2, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L22).

**Symmetry of scalar multiplication.** Flipping the two arguments of real scalar multiplication leaves the bilinear map unchanged. Source: Breakdown.Internal.PressureMollify.lsmul_flip in Breakdown.Uniqueness.PressureMollifyAux2, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L26).

**Divergence commutes with mollification.** At each point, divergence of a mollified smooth compact field equals convolution of its divergence with the mollifier. Source: Breakdown.Internal.PressureMollify.divergenceAt_mollify_apply in Breakdown.Uniqueness.PressureMollifyAux2, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L30).

**Convolution formula for divergence.** The divergence of a mollified smooth compact field is its divergence convolved with the mollifier. Source: Breakdown.Internal.PressureMollify.divergenceAt_mollify in Breakdown.Uniqueness.PressureMollifyAux2, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L48).

**Measurable Newtonian kernel.** The Newtonian kernel is measurable. Source: Breakdown.Internal.PressureMollify.measurable_kernel in Breakdown.Uniqueness.PressureMollifyAux2, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L55).

**Associating potential and mollification.** The potential of a source convolved with a mollifier equals the source convolved with the mollifier's potential. Source: Breakdown.Internal.PressureMollify.potential_convolution_mollifier in Breakdown.Uniqueness.PressureMollifyAux2, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L58).

**Mollifying the exterior potential.** At points at least one mollifier radius from the source support, mollification leaves the potential unchanged. Source: Breakdown.Internal.PressureMollify.potential_mollified_eq in Breakdown.Uniqueness.PressureMollifyAux2, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L80).

**Compact potential difference.** The difference between the potentials of a smooth compact source and its positive-radius mollification has compact support. Source: Breakdown.Internal.PressureMollify.hasCompactSupport_potential_sub in Breakdown.Uniqueness.PressureMollifyAux2, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureMollifyAux2.lean#L93).

### Breakdown.Uniqueness.PressureReplace

This file compares the pressure source before and after replacing a velocity by a compactly supported field.

Reading context: §5 and Appendix A.2; localization of the pressure stress.

**Source namespace:** Breakdown.

**Bilinear stress density.** The bilinear stress density contracts two vector fields with a scalar Hessian. Source: Breakdown.bilinearStress in Breakdown.Uniqueness.PressureReplace, line 11. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L11).

**Smooth divergence of the test field.** The divergence of a smooth vector field is smooth. Source: Breakdown.contDiff_divergenceAt_field in Breakdown.Uniqueness.PressureReplace, line 14. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L14).

**Compact divergence support.** The divergence of a compactly supported vector field has compact support. Source: Breakdown.hasCompactSupport_divergenceAt_field in Breakdown.Uniqueness.PressureReplace, line 25. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L25).

**Continuous gradient of a smooth scalar.** The gradient of a smooth scalar function is continuous. Source: Breakdown.continuous_gradientAt_field in Breakdown.Uniqueness.PressureReplace, line 31. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L31).

**Integrable compact gradient pairing.** Pairing a smooth scalar gradient with a continuous compactly supported field gives an integrable function. Source: Breakdown.integrable_inner_gradientAt in Breakdown.Uniqueness.PressureReplace, line 37. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L37).

**Uniform potential Hessian entries.** The Hessian entries of the potential of smooth compact data share a global bound. Source: Breakdown.abs_secondPartial_potential_le in Breakdown.Uniqueness.PressureReplace, line 47. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L47).

**Integrable squared velocity.** A continuous vector field with the stated finite energy bound has integrable squared norm. Source: Breakdown.integrable_sq_of_lintegral_le in Breakdown.Uniqueness.PressureReplace, line 69. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L69).

**Energy of a field difference.** The difference of two continuous finite-energy fields has integrable squared norm. Source: Breakdown.integrable_sq_sub_field in Breakdown.Uniqueness.PressureReplace, line 76. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L76).

**Integrable bilinear stress.** Two continuous finite-energy fields and a continuous bounded Hessian give an integrable bilinear stress density. Source: Breakdown.integrable_bilinearStress in Breakdown.Uniqueness.PressureReplace, line 88. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L88).

**Expanding a stress difference.** The difference of two self-stress densities splits into the difference-field self-stress and two mixed stresses. Source: Breakdown.bilinearStress_self_sub in Breakdown.Uniqueness.PressureReplace, line 133. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L133).

**Expanding integrated stress differences.** Under the stated integrability and Hessian bounds, the difference of self-stress pairings splits into one self term and two mixed terms. Source: Breakdown.stressPairing_self_sub in Breakdown.Uniqueness.PressureReplace, line 142. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L142).

**Replacing pressure by three stresses.** For two energy-bounded solutions, the cutoff pressure-difference pairing equals the difference-field self-stress plus the two mixed stresses. Source: Breakdown.integral_pressure_difference in Breakdown.Uniqueness.PressureReplace, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureReplace.lean#L163).

### Breakdown.Uniqueness.PressureSumSecondPartials

This file rewrites the pressure Laplacian and stress divergence as finite sums of coordinate second derivatives.

Reading context: §5 and Appendix A.2; coordinate form of the pressure equation.

**Source namespace:** Breakdown.

**Derivative through a linear map.** A continuous linear map commutes with differentiating a composition at a differentiability point. Source: Breakdown.fderiv_clm_comp_apply in Breakdown.Uniqueness.PressureSumSecondPartials, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L10).

**Derivative of a coordinate projection.** Differentiating a coordinate of a vector function gives that coordinate of the derivative. Source: Breakdown.fderiv_component_apply in Breakdown.Uniqueness.PressureSumSecondPartials, line 19. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L19).

**Spatial derivative of a spacetime slice.** The derivative of a spatial slice is the total derivative in the corresponding purely spatial direction. Source: Breakdown.fderiv_slice_right_apply in Breakdown.Uniqueness.PressureSumSecondPartials, line 24. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L24).

**Time derivative of a spacetime slice.** The time derivative of a slice is the total derivative in direction `(1,0)`. Source: Breakdown.hasDerivAt_slice_left in Breakdown.Uniqueness.PressureSumSecondPartials, line 33. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L33).

**Fixed directional partial.** The directional partial evaluates the derivative on one fixed spatial direction. Source: Breakdown.partialAlong in Breakdown.Uniqueness.PressureSumSecondPartials, line 41. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L41).

**Smooth fixed-direction partial.** A fixed-direction partial of a smooth scalar function is smooth. Source: Breakdown.partialAlong_smooth in Breakdown.Uniqueness.PressureSumSecondPartials, line 43. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L43).

**Directional partial of a finite sum.** A directional partial distributes over a three-term sum of smooth functions. Source: Breakdown.partialAlong_sum in Breakdown.Uniqueness.PressureSumSecondPartials, line 47. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L47).

**Directional product rule.** The directional partial of a product is the sum of the two differentiated-factor terms. Source: Breakdown.partialAlong_mul in Breakdown.Uniqueness.PressureSumSecondPartials, line 54. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L54).

**Directional derivative of a constant.** Every fixed-direction partial of a constant function is zero. Source: Breakdown.partialAlong_const in Breakdown.Uniqueness.PressureSumSecondPartials, line 62. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L62).

**Nested directional partials.** Two nested directional partials equal evaluation of the iterated derivative on the two directions. Source: Breakdown.partialAlong_partialAlong in Breakdown.Uniqueness.PressureSumSecondPartials, line 66. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L66).

**Commuting directional partials.** Fixed directional partials commute on smooth scalar functions. Source: Breakdown.partialAlong_comm in Breakdown.Uniqueness.PressureSumSecondPartials, line 73. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L73).

**Hessian entry from directional partials.** A coordinate second partial equals successive partials in its two coordinate directions. Source: Breakdown.secondPartial_eq_partialAlong in Breakdown.Uniqueness.PressureSumSecondPartials, line 79. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L79).

**Smooth field components.** Every coordinate of a smooth vector field is smooth. Source: Breakdown.component_smooth in Breakdown.Uniqueness.PressureSumSecondPartials, line 85. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L85).

**Directional partial of a coordinate.** A coordinate directional partial equals the corresponding coordinate of the vector derivative. Source: Breakdown.partialAlong_component in Breakdown.Uniqueness.PressureSumSecondPartials, line 89. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L89).

**Second partial of a coordinate.** A twice differentiated coordinate equals the corresponding coordinate of the iterated vector derivative. Source: Breakdown.partialAlong_partialAlong_component in Breakdown.Uniqueness.PressureSumSecondPartials, line 93. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L93).

**Divergence as coordinate partials.** The divergence of a smooth vector field is the sum of its diagonal coordinate partials. Source: Breakdown.divergence_eq_sum_partialAlong in Breakdown.Uniqueness.PressureSumSecondPartials, line 106. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L106).

**Componentwise vector Laplacian.** Each component of the vector Laplacian is the sum of the three repeated coordinate partials of that component. Source: Breakdown.sumSecondPartials_component in Breakdown.Uniqueness.PressureSumSecondPartials, line 110. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L110).

**Coordinate expansion in space.** A spatial vector is the sum of its coordinate multiples of the unit vectors. Source: Breakdown.space_eq_sum in Breakdown.Uniqueness.PressureSumSecondPartials, line 117. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L117).

**Coordinate formula for advection.** An advection component is the sum of velocity coordinates times the corresponding directional partials. Source: Breakdown.advection_component in Breakdown.Uniqueness.PressureSumSecondPartials, line 121. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L121).

**Advection in divergence form.** For a smooth divergence-free field, advection is the coordinate divergence of the velocity tensor product. Source: Breakdown.advection_component_eq in Breakdown.Uniqueness.PressureSumSecondPartials, line 127. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L127).

**Divergence of the nonlinear term.** The divergence of advection of a smooth solenoidal field is the sum of second partials of its velocity products. Source: Breakdown.advection_term in Breakdown.Uniqueness.PressureSumSecondPartials, line 138. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L138).

**Divergence of the vector Laplacian.** For a smooth divergence-free field, the divergence of its vector Laplacian is zero. Source: Breakdown.sumSecondPartials_term in Breakdown.Uniqueness.PressureSumSecondPartials, line 148. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L148).

**Pressure Laplacian as divergence.** The scalar Laplacian equals the divergence of its gradient. Source: Breakdown.gradient_term in Breakdown.Uniqueness.PressureSumSecondPartials, line 176. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L176).

**Divergence of the time derivative.** For a smooth divergence-free spacetime field, the time derivative is spatially differentiable and divergence-free at interior times. Source: Breakdown.time_term in Breakdown.Uniqueness.PressureSumSecondPartials, line 185. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L185).

**Directional partial of two differences.** At the stated differentiability point, a directional partial distributes over subtraction of two terms. Source: Breakdown.partialAlong_sub_sub in Breakdown.Uniqueness.PressureSumSecondPartials, line 235. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L235).

**Pressure Poisson equation.** At interior solution times, the pressure Laplacian is minus the sum of second partials of the quadratic velocity products. Source: Breakdown.scalarSumSecondPartials_pressure in Breakdown.Uniqueness.PressureSumSecondPartials, line 243. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/PressureSumSecondPartials.lean#L243).

### Breakdown.Uniqueness.ProductBound

This file proves a three-factor integral estimate and the radial bounds for the near and far Newtonian kernels used in stress estimates.

Reading context: §5 and Appendix A.2; analytic product estimates for regular solutions.

**Source namespace:** Breakdown.

**Splitting a first power.** For nonnegative exponents summing to one, the product of the corresponding powers of a nonnegative extended real equals that number. Source: Breakdown.rpow_split_one in Breakdown.Uniqueness.ProductBound, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L10).

**Three-factor Hölder decomposition.** The product of three nonnegative extended reals splits into the stated factors with powers one half, one third and one sixth. Source: Breakdown.three_factor_split in Breakdown.Uniqueness.ProductBound, line 14. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L14).

**Combining the Hölder powers.** The three paired factors combine into powers `A^(2/3) K^(5/6) B^(1/2)`. Source: Breakdown.three_norm_combine in Breakdown.Uniqueness.ProductBound, line 29. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L29).

**Trilinear convolution bound.** The double convolution integral is bounded by the L^(3/2), L^(6/5), and L2 norms of its three measurable factors. Source: Breakdown.lintegral_productBound_trilinear in Breakdown.Uniqueness.ProductBound, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L44).

**Radial lower-integral formula.** For the stated nonnegative radial profile, the three-dimensional lower integral is `4π` times its radius-squared weighted integral. Source: Breakdown.lintegral_radial_eq in Breakdown.Uniqueness.ProductBound, line 122. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L122).

**Inner-kernel radial exponent.** The radial weight times the L^(6/5) power of inverse-radius-squared simplifies to `y^(-2/5)` for `y > 0`. Source: Breakdown.rpow_inner_kernel in Breakdown.Uniqueness.ProductBound, line 137. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L137).

**Outer-kernel radial exponent.** The radial weight times the square of inverse-radius-cubed simplifies to `y⁻⁴` for `y > 0`. Source: Breakdown.rpow_outer_kernel in Breakdown.Uniqueness.ProductBound, line 144. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L144).

**Inner singular-kernel norm.** The L^(6/5) power integral of inverse-radius-squared inside radius `r > 0` is at most `(20π/3)r^(3/5)`. Source: Breakdown.lintegral_inner_kernel_le in Breakdown.Uniqueness.ProductBound, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L151).

**Outer singular-kernel norm.** The squared integral of inverse-radius-cubed outside radius `r > 0` is at most `(4π/3)r⁻³`. Source: Breakdown.lintegral_outer_kernel_le in Breakdown.Uniqueness.ProductBound, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/ProductBound.lean#L197).

### Breakdown.Uniqueness.RegApriori

This file assembles the a priori Sobolev bounds for a regular solution from the energy and mild-form estimates.

Reading context: §5 and Appendix A.2; regular-solution continuation bounds.

**Source namespace:** Breakdown.SmoothFlow.

**Fourth power cancels a quarter power.** The fourth power of a nonnegative extended real's quarter power is the original number. Source: Breakdown.SmoothFlow.rpow_quarter_pow_four in Breakdown.Uniqueness.RegApriori, line 15. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegApriori.lean#L15).

**Square cancels a half power.** The square of a nonnegative extended real's half power is the original number. Source: Breakdown.SmoothFlow.rpow_half_sq in Breakdown.Uniqueness.RegApriori, line 18. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegApriori.lean#L18).

**Sobolev a priori bound.** For `m ≥ 3`, a common first homogeneous norm bound and initial Hm bound give one Hm bound for every permitted solution interval up to `T`. Source: Breakdown.SmoothFlow.hsNormSq_apriori in Breakdown.Uniqueness.RegApriori, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegApriori.lean#L21).

### Breakdown.Uniqueness.RegAprioriAuxCont

This file proves continuity properties needed to use the regular solution's Sobolev energy in integral estimates.

Reading context: §5 and Appendix A.2; continuity in the a priori argument.

**Source namespace:** Breakdown.SmoothFlow.

**Higher order controls H2.** A Sobolev squared norm of order at least two bounds the squared H2 norm. Source: Breakdown.SmoothFlow.hsNormSq_mono_index in Breakdown.Uniqueness.RegAprioriAuxCont, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxCont.lean#L12).

**Finite Fourier L1 norm.** A finite Sobolev norm of order at least two gives a finite Fourier L1 norm. Source: Breakdown.SmoothFlow.freqL1Norm_lt_top_of_hsNormSq in Breakdown.Uniqueness.RegAprioriAuxCont, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxCont.lean#L20).

**Sobolev norm as weighted L2.** The squared Hm norm is the square of the L2 norm for the measure weighted by the Sobolev weight. Source: Breakdown.SmoothFlow.hsNormSq_eq_eLpNorm_sq in Breakdown.Uniqueness.RegAprioriAuxCont, line 27. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxCont.lean#L27).

**Continuity of norms under Lp convergence.** Lp convergence of measurable differences to zero implies convergence of the norms when the limiting norm is finite and `p ≥ 1`. Source: Breakdown.SmoothFlow.tendsto_eLpNorm_of_tendsto_sub in Breakdown.Uniqueness.RegAprioriAuxCont, line 38. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxCont.lean#L38).

**Continuous real Sobolev energy.** The real-valued squared Sobolev norm of an Hm curve is continuous on its closed time interval. Source: Breakdown.SmoothFlow.continuousOn_hsNormSq_toReal in Breakdown.Uniqueness.RegAprioriAuxCont, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxCont.lean#L62).

**Continuous Fourier L1 norm.** For a Sobolev curve of order at least two, the real Fourier L1 norm is continuous in time. Source: Breakdown.SmoothFlow.continuousOn_freqL1Norm_toReal in Breakdown.Uniqueness.RegAprioriAuxCont, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxCont.lean#L93).

### Breakdown.Uniqueness.RegAprioriAuxEnergy

This file supplies the energy estimate that controls regular solutions in the continuation argument.

Reading context: §5 and Appendix A.2; the regular-solution energy inequality.

**Source namespace:** Breakdown.SmoothFlow.

**Integrated homogeneous H2 bound.** A common first homogeneous norm bound for the stated solenoidal Duhamel flows gives one bound for their time-integrated second homogeneous norm. Source: Breakdown.SmoothFlow.lintegral_homNormSq_two_le in Breakdown.Uniqueness.RegAprioriAuxEnergy, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergy.lean#L14).

### Breakdown.Uniqueness.RegAprioriAuxEnergyPart1

This file develops weighted frequency integrability and the nonlinear pairing estimates used in the regular energy calculation.

Reading context: §5 and Appendix A.2; the first part of the Sobolev-energy estimate.

**Source namespace:** Breakdown.SmoothFlow.

**Monotone Sobolev weights.** Increasing the nonnegative integer Sobolev order increases the pointwise weight. Source: Breakdown.SmoothFlow.hsWeight_le_of_le in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L13).

**Monotone Sobolev norms.** Increasing the Sobolev order increases the squared Sobolev norm. Source: Breakdown.SmoothFlow.hsNormSq_le_hsNormSq_of_le in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L16).

**Homogeneous norm from Sobolev norm.** A Sobolev norm of order `m` controls a homogeneous norm of every order `k ≤ m`. Source: Breakdown.SmoothFlow.homNormSq_le_hsNormSq in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L20).

**Lowering a curve's Sobolev order.** A Sobolev curve of order `m` is also a Sobolev curve of every order `k ≤ m`. Source: Breakdown.SmoothFlow.isHsCurve_of_le in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L28).

**Continuous Fourier projection.** At fixed frequency, the complex divergence-free projection is continuous in its vector argument. Source: Breakdown.SmoothFlow.continuous_divFreeC in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 34. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L34).

**Time continuity of the nonlinearity.** Along an H1 curve, the nonlinear symbol at each fixed frequency is continuous on the closed time interval. Source: Breakdown.SmoothFlow.continuousOn_nonlinSymbol_of_hsCurve in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L38).

**Finite integrated second-order energy.** For a Sobolev curve of order at least two, the time integral of the squared second homogeneous norm is finite. Source: Breakdown.SmoothFlow.setLIntegral_homNormSq_two_lt_top in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L43).

**Absorbing a three-quarter power.** For nonnegative `a`, the term `a y^(3/4)` is bounded by `4π²y` plus the displayed scalar remainder. Source: Breakdown.SmoothFlow.ofReal_mul_rpow_three_quarters_le in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L55).

**Lower integral on a time interval.** The lower integral of a continuous nonnegative function on `[0,T]` equals the nonnegative-real conversion of its interval integral. Source: Breakdown.SmoothFlow.setLIntegral_ofReal_eq_intervalIntegral in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L89).

**Pointwise Fourier energy inequality.** At each frequency, the Duhamel equation gives the displayed first-order energy inequality with dissipation coefficient `8π²`. Source: Breakdown.SmoothFlow.energy_inequality_apply in Breakdown.Uniqueness.RegAprioriAuxEnergyPart1, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart1.lean#L95).

### Breakdown.Uniqueness.RegAprioriAuxEnergyPart2

This file controls convolution weights and frequency integrals in the regular solution's energy estimate.

Reading context: §5 and Appendix A.2; the weighted nonlinear energy calculation.

**Source namespace:** Breakdown.SmoothFlow.

**Measurability of frequency subtraction.** An almost-everywhere measurable function remains measurable after composing with the difference of two frequency variables. Source: Breakdown.SmoothFlow.aemeasurable_sub_comp in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 13. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L13).

**Measurability under shifted reflection.** An almost-everywhere measurable function remains measurable after `η ↦ ξ-η`. Source: Breakdown.SmoothFlow.aemeasurable_sub_left_comp in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 17. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L17).

**Product of two square roots.** The product of two equal half powers of a nonnegative extended real is the original number. Source: Breakdown.SmoothFlow.half_rpow_mul_self in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 21. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L21).

**Squaring a scaled square root.** The square of `a x^(1/2)` equals `a²x` for nonnegative extended reals. Source: Breakdown.SmoothFlow.mul_half_rpow_sq in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 24. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L24).

**L2-L2-L1 convolution pairing.** The integral pairing with a convolution is bounded by two L2 factors and one L1 factor. Source: Breakdown.SmoothFlow.lintegral_mul_conv_le in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L28).

**Putting weights inside convolution.** The output-frequency norm times a self-convolution is bounded by twice the convolution carrying the input-frequency norm. Source: Breakdown.SmoothFlow.ofReal_norm_mul_lintegral_le in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L76).

**Adding half and quarter exponents.** The product of the half and quarter powers is the three-quarter power. Source: Breakdown.SmoothFlow.rpow_half_mul_quarter in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 99. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L99).

**Nonlinear homogeneous energy bound.** For a measurable solenoidal H3 symbol, the nonlinear energy pairing is bounded by a constant times the three-quarter powers of the first two homogeneous energies. Source: Breakdown.SmoothFlow.lintegral_weight_mul_nonlinSymbol_le in Breakdown.Uniqueness.RegAprioriAuxEnergyPart2, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart2.lean#L102).

### Breakdown.Uniqueness.RegAprioriAuxEnergyPart3

This file finishes the energy bound by combining the preceding frequency estimates.

Reading context: §5 and Appendix A.2; closure of the Sobolev-energy inequality.

**Source namespace:** Breakdown.SmoothFlow.

**Joint measurability from time continuity.** Pointwise time continuity and measurable frequency slices give joint measurability on the product of the time interval and frequency space. Source: Breakdown.SmoothFlow.aestronglyMeasurable_uncurry_of_continuousOn in Breakdown.Uniqueness.RegAprioriAuxEnergyPart3, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart3.lean#L12).

**Measurable norm of the Fourier flow.** For the stated H1 Duhamel flow, the symbol norm is jointly measurable in time and frequency. Source: Breakdown.SmoothFlow.aemeasurable_enorm_apply_of_varConst in Breakdown.Uniqueness.RegAprioriAuxEnergyPart3, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxEnergyPart3.lean#L68).

### Breakdown.Uniqueness.RegAprioriAuxIntegralIneq

This file converts the regular energy estimates into scalar integral inequalities and quantitative bounds.

Reading context: §5 and Appendix A.2; the scalar continuation estimate.

**Source namespace:** Breakdown.SmoothFlow.

**Integral Grönwall estimate.** A continuous function satisfying the stated integral inequality is bounded by its initial constant times the exponential of the coefficient integral. Source: Breakdown.SmoothFlow.integralIneq_cont in Breakdown.Uniqueness.RegAprioriAuxIntegralIneq, line 11. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxIntegralIneq.lean#L11).

**Integral of a two-thirds singularity.** On a nonnegative time interval, the integral of `(t-s)^(-2/3)` is `3t^(1/3)`. Source: Breakdown.SmoothFlow.lintegral_kernel_eq in Breakdown.Uniqueness.RegAprioriAuxIntegralIneq, line 72. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxIntegralIneq.lean#L72).

**Fourth power of a real power.** Raising a nonnegative extended real power to the fourth power multiplies its exponent by four. Source: Breakdown.SmoothFlow.rpow_pow_four in Breakdown.Uniqueness.RegAprioriAuxIntegralIneq, line 94. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxIntegralIneq.lean#L94).

**Hölder bound for a half singularity.** The time integral with kernel `(t-s)^(-1/2)` is bounded by the displayed kernel factor and the L4 norm of the product. Source: Breakdown.SmoothFlow.lpProd_step in Breakdown.Uniqueness.RegAprioriAuxIntegralIneq, line 99. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxIntegralIneq.lean#L99).

**Uniform Volterra integral bound.** The stated square-root-kernel inequality and uniform time L4 bound yield a common bound for the nonnegative continuous function `n`. Source: Breakdown.SmoothFlow.iterIntegral_bound in Breakdown.Uniqueness.RegAprioriAuxIntegralIneq, line 128. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxIntegralIneq.lean#L128).

### Breakdown.Uniqueness.RegAprioriAuxMild

This file obtains a priori control from the regular solution's heat-kernel mild formula.

Reading context: §5 and Appendix A.2; mild-form estimates for continuation.

**Source namespace:** Breakdown.SmoothFlow.

**Factoring a weighted L2 constant.** A finite nonnegative constant factors out of the square root of a weighted squared lower integral. Source: Breakdown.SmoothFlow.lintegral_weighted_const_mul_sq in Breakdown.Uniqueness.RegAprioriAuxMild, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMild.lean#L14).

**Sobolev bound from Duhamel's formula.** For solenoidal Hm flows with `m ≥ 3`, the Sobolev norm is bounded by its initial norm plus the half-singularity convolution with Fourier L1 and Hm norms. Source: Breakdown.SmoothFlow.hsNormSq_sqrt_mild_le in Breakdown.Uniqueness.RegAprioriAuxMild, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMild.lean#L23).

### Breakdown.Uniqueness.RegAprioriAuxMildPart1

This file bounds the heat and nonlinear pieces of the Fourier Duhamel formula in weighted norms.

Reading context: §5 and Appendix A.2; estimates for the regular mild integral.

**Source namespace:** Breakdown.SmoothFlow.

**Sum of component convolution norms.** The convolution-norm sum adds the norms of all nine coordinate self-convolutions. Source: Breakdown.SmoothFlow.convEnormSum in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L12).

**Heat multiplier bounded by one.** At nonnegative time, the heat multiplier is at most one. Source: Breakdown.SmoothFlow.heatSymbol_le_one in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L15).

**Nonnegative heat multiplier.** The heat multiplier is nonnegative for every time and frequency. Source: Breakdown.SmoothFlow.heatSymbol_nonneg' in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L20).

**One heat-smoothed frequency factor.** For positive time, `2π‖ξ‖` times the heat multiplier is at most `τ^(-1/2)`. Source: Breakdown.SmoothFlow.heatSymbol_mul_le in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L23).

**Vector norm from component norms.** The complex vector norm is at most the sum of its coordinate norms. Source: Breakdown.SmoothFlow.norm_sum_le_of_l2 in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 46. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L46).

**Monotone Sobolev energy.** The squared Sobolev norm increases with its integer order. Source: Breakdown.SmoothFlow.hsNormSq_mono in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 54. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L54).

**Coordinates of the frequency vector.** Each complex frequency-vector coordinate is the complex cast of the corresponding real frequency coordinate. Source: Breakdown.SmoothFlow.freqVec_apply' in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 60. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L60).

**Frequency inner product in coordinates.** The complex inner product with the real frequency vector is the coordinate sum `∑ ξᵢwᵢ`. Source: Breakdown.SmoothFlow.inner_freqVec' in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 62. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L62).

**Complex coordinate-square identity.** The sum of the squared complex casts of real frequency coordinates equals the complex cast of squared frequency norm. Source: Breakdown.SmoothFlow.sum_sq_ofReal in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 66. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L66).

**Projected vectors are transverse.** The divergence-free projection is orthogonal to the frequency vector at every frequency. Source: Breakdown.SmoothFlow.inner_freqVec_divFreeC in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 75. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L75).

**Contractive divergence-free projection.** The complex divergence-free projection does not increase vector norm. Source: Breakdown.SmoothFlow.norm_divFreeC_le in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 91. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L91).

**Advection bounded by convolution norms.** For the stated solenoidal integrable symbol, advection is bounded by `2π‖ξ‖` times the sum of component convolution norms. Source: Breakdown.SmoothFlow.enorm_advectionSymbol_le in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 105. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L105).

**Norm bound from Duhamel's identity.** The symbol norm is bounded by its initial norm plus the heat-weighted integral of the nonlinear symbol norm. Source: Breakdown.SmoothFlow.enorm_varConst_le in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 136. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L136).

**Pointwise mild convolution bound.** The stated solenoidal Hm Duhamel flow is bounded pointwise by its initial symbol plus a half-singularity integral of component convolution norms. Source: Breakdown.SmoothFlow.enorm_mild_le in Breakdown.Uniqueness.RegAprioriAuxMildPart1, line 153. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart1.lean#L153).

### Breakdown.Uniqueness.RegAprioriAuxMildPart2

This file proves weighted Minkowski inequalities for lower integrals, allowing the time integral to be bounded outside the squared frequency integral.

Reading context: §5 and Appendix A.2; justification of the mild-integral estimate.

**Source namespace:** Breakdown.SmoothFlow.

**Square cancels a half power.** The square of a nonnegative extended real's half power is the original number. Source: Breakdown.SmoothFlow.rpow_half_sq in Breakdown.Uniqueness.RegAprioriAuxMildPart2, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart2.lean#L10).

**Minkowski inequality for lower integrals.** The squared L2 norm of an integral is bounded by the square of the integral of the L2 norms. Source: Breakdown.SmoothFlow.lintegral_sq_lintegral_le in Breakdown.Uniqueness.RegAprioriAuxMildPart2, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart2.lean#L14).

**Weighted integral triangle inequality.** The weighted L2 norm of a function plus an integral is bounded by its weighted norm plus the integral of the weighted norms. Source: Breakdown.SmoothFlow.lintegral_weighted_add_lintegral_sq_le in Breakdown.Uniqueness.RegAprioriAuxMildPart2, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart2.lean#L102).

### Breakdown.Uniqueness.RegAprioriAuxMildPart3

This file splits polynomial frequency weights across convolution factors to control the nonlinear mild term.

Reading context: §5 and Appendix A.2; weighted frequency splitting in the mild estimate.

**Source namespace:** Breakdown.SmoothFlow.

**Splitting a polynomial weight.** The output weight `(1+‖ξ‖)^m` is bounded by `2^m` times the sum of the two input weights. Source: Breakdown.SmoothFlow.one_add_norm_pow_le in Breakdown.Uniqueness.RegAprioriAuxMildPart3, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart3.lean#L12).

**Sobolev weight below polynomial square.** The Sobolev weight is at most the square of `(1+‖ξ‖)^m`. Source: Breakdown.SmoothFlow.hsWeight_le_sq in Breakdown.Uniqueness.RegAprioriAuxMildPart3, line 32. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart3.lean#L32).

**Polynomial square below Sobolev weight.** The square of `(1+‖ξ‖)^m` is at most `2^m` times the Sobolev weight. Source: Breakdown.SmoothFlow.sq_le_hsWeight in Breakdown.Uniqueness.RegAprioriAuxMildPart3, line 37. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart3.lean#L37).

**Weighted L2 bound for self-convolution.** The weighted squared self-convolution integral is bounded by `8^(m+1)` times the squared L1 mass and the weighted L2 energy. Source: Breakdown.SmoothFlow.lintegral_weight_conv_sq_le in Breakdown.Uniqueness.RegAprioriAuxMildPart3, line 43. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart3.lean#L43).

**Weighted component-convolution estimate.** The weighted L2 norm of the component convolution sum is bounded by a constant times the Fourier L1 norm and the Hm norm. Source: Breakdown.SmoothFlow.convEnormSum_weighted_le in Breakdown.Uniqueness.RegAprioriAuxMildPart3, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart3.lean#L151).

### Breakdown.Uniqueness.RegAprioriAuxMildPart4

This file completes the time-kernel and nonlinear estimates used in the regular solution's mild bound.

Reading context: §5 and Appendix A.2; completion of the a priori mild estimate.

**Source namespace:** Breakdown.SmoothFlow.

**Extended complex L2 norm.** The extended L2 norm is the square root of the lower integral of the squared complex norm. Source: Breakdown.SmoothFlow.l2e in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 12. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L12).

**Measurability of shifted reflection.** Shifted reflection of an almost-everywhere strongly measurable complex function is almost-everywhere strongly measurable. Source: Breakdown.SmoothFlow.aesm_shift in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L14).

**Cauchy-Schwarz for shifted products.** The integral of a shifted product of norms is at most the product of the two extended L2 norms. Source: Breakdown.SmoothFlow.lintegral_prod_shift_le in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L18).

**Convolution bounded by L2 norms.** The pointwise convolution norm is at most the product of the two extended L2 norms. Source: Breakdown.SmoothFlow.enorm_convC_le in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L29).

**Integrable convolution integrand.** Two measurable functions with finite extended L2 norms have an integrable shifted-product integrand. Source: Breakdown.SmoothFlow.integrable_prod_shift in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 36. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L36).

**Three-term convolution difference.** Under the stated L2 hypotheses, the difference of two convolutions splits into one difference-difference term and two mixed terms. Source: Breakdown.SmoothFlow.convC_sub_eq in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 43. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L43).

**Component L2 norm below Sobolev norm.** Every coordinate L2 norm is at most the square root of the squared Hm norm. Source: Breakdown.SmoothFlow.l2e_comp_le in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 66. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L66).

**Measurability of symbol components.** Every coordinate of an almost-everywhere strongly measurable vector symbol is almost-everywhere strongly measurable. Source: Breakdown.SmoothFlow.aesm_comp in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 79. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L79).

**Measurable complex convolution.** The convolution of two almost-everywhere strongly measurable complex functions is measurable. Source: Breakdown.SmoothFlow.measurable_convC in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 83. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L83).

**Continuous component convolution curve.** Coordinate self-convolution along an Hm curve is continuous in time at every fixed frequency. Source: Breakdown.SmoothFlow.continuousOn_convC_curve in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 99. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L99).

**Jointly measurable convolution norms.** For an Hm curve with `m ≥ 3`, the component-convolution norm sum is jointly measurable on the stated open time interval. Source: Breakdown.SmoothFlow.aemeasurable_convEnormSum_curve in Breakdown.Uniqueness.RegAprioriAuxMildPart4, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegAprioriAuxMildPart4.lean#L148).

### Breakdown.Uniqueness.RegBounds

This file records the uniform and pointwise bounds attached to regular Fourier solutions.

Reading context: §5 and Appendix A.2; reusable regularity bounds.

**Source namespace:** Breakdown.SmoothFlow.

**Real part contracts vector norm.** Taking the real part of a complex vector does not increase its norm. Source: Breakdown.SmoothFlow.norm_realVec_le in Breakdown.Uniqueness.RegBounds, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L13).

**Norm of the real-part operator.** The real-part linear operator has norm at most one. Source: Breakdown.SmoothFlow.opNorm_realVec_le in Breakdown.Uniqueness.RegBounds, line 24. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L24).

**Monotone Sobolev weight.** The Sobolev weight increases with its order. Source: Breakdown.SmoothFlow.hsWeight_mono in Breakdown.Uniqueness.RegBounds, line 27. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L27).

**Monotone squared Sobolev norm.** The squared Sobolev norm increases with its order. Source: Breakdown.SmoothFlow.hsNormSq_mono in Breakdown.Uniqueness.RegBounds, line 31. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L31).

**Order-zero Sobolev energy.** The squared order-zero Sobolev norm is the lower integral of the squared symbol norm. Source: Breakdown.SmoothFlow.hsNormSq_zero_eq in Breakdown.Uniqueness.RegBounds, line 37. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L37).

**Fourier L1 finiteness from H2.** Finite H2 energy implies finite Fourier L1 norm. Source: Breakdown.SmoothFlow.freqL1Norm_lt_top in Breakdown.Uniqueness.RegBounds, line 41. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L41).

**First Fourier moment below a weight.** The first frequency moment is bounded by the L1 integral with weight `1+‖ξ‖`. Source: Breakdown.SmoothFlow.gradFreqL1Norm_le_weighted in Breakdown.Uniqueness.RegBounds, line 47. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L47).

**Finite first Fourier moment from H3.** Finite H3 energy gives a finite first frequency moment. Source: Breakdown.SmoothFlow.gradFreqL1Norm_lt_top in Breakdown.Uniqueness.RegBounds, line 54. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L54).

**Integrability from finite Fourier L1.** A measurable symbol with finite Fourier L1 norm is integrable. Source: Breakdown.SmoothFlow.integrable_of_freqL1Norm in Breakdown.Uniqueness.RegBounds, line 61. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L61).

**Squared lower integral and L2 norm.** The squared-norm lower integral equals the square of the extended L2 norm. Source: Breakdown.SmoothFlow.lintegral_sq_eq in Breakdown.Uniqueness.RegBounds, line 65. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L65).

**L2 membership from order-zero energy.** A measurable symbol with finite order-zero Sobolev energy belongs to L2. Source: Breakdown.SmoothFlow.memLp_two_of in Breakdown.Uniqueness.RegBounds, line 71. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L71).

**Physical energy below Fourier energy.** For a measurable solenoidal H2 symbol, the physical velocity energy is at most its order-zero Fourier energy. Source: Breakdown.SmoothFlow.integral_sq_physField_le in Breakdown.Uniqueness.RegBounds, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L77).

**Fourier transform pointwise norm bound.** The Fourier transform norm at each point is at most the integral of the input norm. Source: Breakdown.SmoothFlow.norm_freqTr_le_integral in Breakdown.Uniqueness.RegBounds, line 104. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L104).

**Physical velocity from Fourier L1.** For a measurable H3 symbol, each physical velocity value is bounded by the real Fourier L1 norm. Source: Breakdown.SmoothFlow.norm_physField_le in Breakdown.Uniqueness.RegBounds, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L110).

**Physical gradient from frequency moment.** For a measurable H3 symbol, the physical derivative norm is at most `2π` times the first frequency moment. Source: Breakdown.SmoothFlow.norm_fderiv_physField_le in Breakdown.Uniqueness.RegBounds, line 117. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L117).

**Sobolev energy relative to a reference.** The Sobolev energy of `f` is at most twice the energy of `f-g` plus twice that of the measurable reference `g`. Source: Breakdown.SmoothFlow.hsNormSq_le_two_mul in Breakdown.Uniqueness.RegBounds, line 169. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L169).

**Uniform energy along a Sobolev curve.** A Sobolev curve on a closed interval has a common finite bound for its squared Sobolev norms. Source: Breakdown.SmoothFlow.hsNormSq_boundedOn in Breakdown.Uniqueness.RegBounds, line 202. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L202).

**Physical energy bounded on the interval.** A solenoidal H3 curve gives a physical velocity with energy bounded on its closed time interval. Source: Breakdown.SmoothFlow.energyBoundedOn_physField in Breakdown.Uniqueness.RegBounds, line 221. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L221).

**Velocity and gradient bounded in time.** An H4 curve gives a physical velocity and derivative with one common bound throughout the closed time interval. Source: Breakdown.SmoothFlow.gradientBoundedOn_physField in Breakdown.Uniqueness.RegBounds, line 231. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegBounds.lean#L231).

### Breakdown.Uniqueness.RegConcat

This file concatenates compatible regular solutions and verifies the continuity, Sobolev bounds and mild identity of the joined curve.

Reading context: §5 and Appendix A.2; continuation by joining regular solutions.

**Source namespace:** Breakdown.SmoothFlow.

**Squared complex L2 integral.** The squared-L2 quantity is the lower integral of the squared complex norm. Source: Breakdown.SmoothFlow.lintSq in Breakdown.Uniqueness.RegConcat, line 12. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L12).

**Cauchy-Schwarz for complex products.** The lower integral of the norm of a product is bounded by the square roots of the two squared-L2 integrals. Source: Breakdown.SmoothFlow.lintegral_enorm_mul_le in Breakdown.Uniqueness.RegConcat, line 14. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L14).

**Integral pairing bound in L2.** The norm of a complex product integral is bounded by the square roots of the two squared-L2 integrals. Source: Breakdown.SmoothFlow.enorm_integral_mul_le in Breakdown.Uniqueness.RegConcat, line 24. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L24).

**Integrability of an L2 product.** Two measurable complex functions with finite squared-L2 integrals have an integrable product. Source: Breakdown.SmoothFlow.integrable_mul_of_lintSq in Breakdown.Uniqueness.RegConcat, line 29. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L29).

**Square-root convergence at zero.** Taking the half power preserves convergence of nonnegative extended reals to zero. Source: Breakdown.SmoothFlow.tendsto_rpow_half in Breakdown.Uniqueness.RegConcat, line 37. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L37).

**Continuity of an L2 product integral.** Convergence of both factors in L2, with the stated measurability conditions, gives convergence of their product integrals. Source: Breakdown.SmoothFlow.tendsto_integral_mul in Breakdown.Uniqueness.RegConcat, line 42. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L42).

**First Sobolev weight is at least one.** The order-one Sobolev weight is at least one. Source: Breakdown.SmoothFlow.one_le_hsWeight_one in Breakdown.Uniqueness.RegConcat, line 86. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L86).

**Coordinate L2 energy below H1.** The squared-L2 integral of each coordinate is bounded by the H1 energy. Source: Breakdown.SmoothFlow.lintSq_apply_le in Breakdown.Uniqueness.RegConcat, line 90. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L90).

**Coordinate derivative energy bound.** A Fourier coordinate derivative has pointwise squared norm bounded by `4π²` times the H1 energy density. Source: Breakdown.SmoothFlow.enorm_freq_mul_sq_le in Breakdown.Uniqueness.RegConcat, line 100. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L100).

**Shifted derivative L2 bound.** The squared-L2 integral of a shifted coordinate derivative is bounded by `4π²` times H1 energy. Source: Breakdown.SmoothFlow.lintSq_shift_le in Breakdown.Uniqueness.RegConcat, line 119. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L119).

**Measurable coordinate projection.** Taking a coordinate preserves almost-everywhere strong measurability. Source: Breakdown.SmoothFlow.aesm_apply in Breakdown.Uniqueness.RegConcat, line 132. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L132).

**Measurable shifted frequency derivative.** The shifted coordinate derivative multiplier preserves almost-everywhere strong measurability. Source: Breakdown.SmoothFlow.aesm_shift in Breakdown.Uniqueness.RegConcat, line 136. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L136).

**Monotone Sobolev weights.** A lower Sobolev order has a no larger pointwise weight. Source: Breakdown.SmoothFlow.hsWeight_mono in Breakdown.Uniqueness.RegConcat, line 147. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L147).

**Monotone Sobolev energies.** A lower Sobolev order has no larger squared norm. Source: Breakdown.SmoothFlow.hsNormSq_mono in Breakdown.Uniqueness.RegConcat, line 150. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L150).

**Continuous advection convolution in time.** Along an H1 curve, each component convolution with a frequency derivative is continuous at fixed frequency. Source: Breakdown.SmoothFlow.continuousOn_convC in Breakdown.Uniqueness.RegConcat, line 154. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L154).

**Continuous Fourier projection.** At fixed frequency, the complex divergence-free projection is continuous in its vector argument. Source: Breakdown.SmoothFlow.continuous_divFreeC in Breakdown.Uniqueness.RegConcat, line 189. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L189).

**Continuous nonlinear-symbol curve.** The nonlinear symbol of an H1 curve is continuous in time at each frequency. Source: Breakdown.SmoothFlow.continuousOn_nonlinSymbol in Breakdown.Uniqueness.RegConcat, line 193. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L193).

**Continuous time-dependent heat factor.** At fixed terminal time and frequency, the heat multiplier is continuous in its integration-time argument. Source: Breakdown.SmoothFlow.continuous_heatFactor in Breakdown.Uniqueness.RegConcat, line 203. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L203).

**Multiplying successive heat factors.** Heat multipliers over two successive time increments multiply to the heat multiplier over their sum. Source: Breakdown.SmoothFlow.heatSymbol_mul in Breakdown.Uniqueness.RegConcat, line 208. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L208).

**Lower-order Sobolev continuity.** A Sobolev curve of order `m` remains a Sobolev curve at any order `n ≤ m`. Source: Breakdown.SmoothFlow.isHsCurve_mono_aux in Breakdown.Uniqueness.RegConcat, line 217. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L217).

**Gluing Sobolev curves.** Two Sobolev curves that agree at their shared endpoint glue to a Sobolev curve on the combined interval. Source: Breakdown.SmoothFlow.isHsCurve_concat in Breakdown.Uniqueness.RegConcat, line 224. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L224).

**Gluing Duhamel identities.** Two H3 curves satisfying Duhamel's formula and matching at the shared endpoint satisfy it on the combined interval. Source: Breakdown.SmoothFlow.isVarConstSymbol_concat in Breakdown.Uniqueness.RegConcat, line 258. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L258).

**Reducing Sobolev order.** A Sobolev curve of order `m` is a Sobolev curve of every lower order `n`. Source: Breakdown.SmoothFlow.isHsCurve_mono in Breakdown.Uniqueness.RegConcat, line 318. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L318).

**Restricting a Sobolev curve.** Restricting a Sobolev curve to a contained closed time interval preserves its Sobolev-curve property. Source: Breakdown.SmoothFlow.isHsCurve_restrict in Breakdown.Uniqueness.RegConcat, line 322. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L322).

**Restricting the Duhamel endpoint.** The Duhamel identity remains valid when the terminal time is reduced. Source: Breakdown.SmoothFlow.isVarConstSymbol_restrict in Breakdown.Uniqueness.RegConcat, line 329. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegConcat.lean#L329).

### Breakdown.Uniqueness.RegCurve

This file packages frequency functions as curves in weighted L1 spaces and proves their time regularity.

Reading context: §5 and Appendix A.2; Banach-space curves for physical reconstruction.

**Source namespace:** Breakdown.SmoothFlow.

**Polynomially weighted L1 measure.** The weighted L1 measure has density `(1+‖ξ‖)^k` against frequency-space volume. Source: Breakdown.SmoothFlow.weightL1Measure in Breakdown.Uniqueness.RegCurve, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L16).

**Weighted L1 representative or zero.** The weighted-L1 conversion uses the function's L1 representative when it exists and zero otherwise. Source: Breakdown.SmoothFlow.toWeightL1 in Breakdown.Uniqueness.RegCurve, line 20. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L20).

**Fourier time-derivative symbol.** The time-derivative symbol is the Laplacian multiplier `-4π²‖ξ‖²f` plus the projected nonlinearity. Source: Breakdown.SmoothFlow.timeDerivSymbol in Breakdown.Uniqueness.RegCurve, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L23).

**Weighted representative on its domain.** For a function in the weighted L1 space, the conversion equals its ordinary Lp representative. Source: Breakdown.SmoothFlow.toWeightL1_eq_toLp in Breakdown.Uniqueness.RegCurve, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L26).

**All weighted L1 moments along the curve.** A curve with finite Sobolev regularity at every order belongs to every polynomially weighted L1 space at each allowed time. Source: Breakdown.SmoothFlow.memLp_weightL1_of_curve in Breakdown.Uniqueness.RegCurve, line 31. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L31).

**Continuous weighted L1 curve.** A curve continuous in every Sobolev order is continuous in each polynomially weighted L1 space. Source: Breakdown.SmoothFlow.continuousOn_toWeightL1_curve in Breakdown.Uniqueness.RegCurve, line 36. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L36).

**Advection on weighted L1 spaces.** Advection is realized by a continuous bilinear map from two order-`k+1` weighted L1 spaces into order `k`. Source: Breakdown.SmoothFlow.bilin_weightL1 in Breakdown.Uniqueness.RegCurve, line 63. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L63).

**Smooth map for the time derivative.** The time-derivative symbol is represented by a smooth map from weighted L1 orders `k+2` and `k+1` into order `k`. Source: Breakdown.SmoothFlow.timeDeriv_repr in Breakdown.Uniqueness.RegCurve, line 72. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L72).

**Continuity of the complex projection.** At each fixed frequency, the complex divergence-free projection is continuous. Source: Breakdown.SmoothFlow.continuous_divFreeC in Breakdown.Uniqueness.RegCurve, line 100. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L100).

**Differentiating the weighted L1 curve.** A smooth-order solenoidal Duhamel curve has within-interval derivative equal to its time-derivative symbol in every weighted L1 space. Source: Breakdown.SmoothFlow.hasDerivWithinAt_toWeightL1 in Breakdown.Uniqueness.RegCurve, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L104).

**All time derivatives in weighted L1.** The stated solenoidal Duhamel curve is differentiable to every finite order as a weighted L1 curve on the closed time interval. Source: Breakdown.SmoothFlow.contDiffOn_toWeightL1 in Breakdown.Uniqueness.RegCurve, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurve.lean#L142).

### Breakdown.Uniqueness.RegCurveAuxBilin

This file proves weighted integrability and continuity of the convolution bilinear terms along regular curves.

Reading context: §5 and Appendix A.2; nonlinear weighted-L1 curve estimates.

**Source namespace:** Breakdown.SmoothFlow.

**Polynomial frequency weights exceed one.** Every nonnegative integer polynomial frequency weight is at least one. Source: Breakdown.SmoothFlow.bilin_weight_ge_one in Breakdown.Uniqueness.RegCurveAuxBilin, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L12).

**Measurable polynomial frequency weight.** The nonnegative extended-real polynomial frequency weight is measurable. Source: Breakdown.SmoothFlow.bilin_weight_measurable in Breakdown.Uniqueness.RegCurveAuxBilin, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L15).

**Volume follows weighted null sets.** Ordinary volume is absolutely continuous with respect to each polynomially weighted volume. Source: Breakdown.SmoothFlow.bilin_volume_ac in Breakdown.Uniqueness.RegCurveAuxBilin, line 19. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L19).

**Weighted volume absolutely continuous.** Each polynomially weighted volume is absolutely continuous with respect to ordinary volume. Source: Breakdown.SmoothFlow.bilin_weighted_ac in Breakdown.Uniqueness.RegCurveAuxBilin, line 27. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L27).

**Integration against the weighted volume.** Integrating an almost-everywhere measurable function against weighted volume inserts its polynomial density into the ordinary lower integral. Source: Breakdown.SmoothFlow.bilin_lintegral_weighted in Breakdown.Uniqueness.RegCurveAuxBilin, line 30. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L30).

**Weighted L1 membership criterion.** Weighted L1 membership is equivalent to ordinary measurability and finiteness of the weighted norm integral. Source: Breakdown.SmoothFlow.bilin_memLp_iff in Breakdown.Uniqueness.RegCurveAuxBilin, line 35. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L35).

**Norm formula in weighted L1.** The nonnegative-real norm of a weighted L1 element equals the lower integral of its polynomially weighted pointwise norm. Source: Breakdown.SmoothFlow.bilin_ofReal_norm in Breakdown.Uniqueness.RegCurveAuxBilin, line 47. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L47).

**Integrable polynomially weighted norm.** Membership in weighted L1 makes the polynomially weighted ordinary norm integrable. Source: Breakdown.SmoothFlow.bilin_integrable_weight in Breakdown.Uniqueness.RegCurveAuxBilin, line 52. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L52).

**Measurable symbol coordinates.** Coordinate projection preserves almost-everywhere strong measurability of a symbol. Source: Breakdown.SmoothFlow.bilin_comp_aesm in Breakdown.Uniqueness.RegCurveAuxBilin, line 60. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L60).

**Integrable coordinate from weighted L1.** Each coordinate of a weighted L1 symbol is integrable against ordinary volume. Source: Breakdown.SmoothFlow.bilin_integrable_left in Breakdown.Uniqueness.RegCurveAuxBilin, line 64. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L64).

**Integrable differentiated coordinate.** One additional polynomial weight makes a Fourier coordinate derivative integrable. Source: Breakdown.SmoothFlow.bilin_integrable_right in Breakdown.Uniqueness.RegCurveAuxBilin, line 72. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L72).

**Pointwise advection-product bound.** Each advection-product component is bounded by `2π‖a‖‖x‖‖b‖`. Source: Breakdown.SmoothFlow.bilin_integrand_norm_le in Breakdown.Uniqueness.RegCurveAuxBilin, line 89. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L89).

**Vector norm from component norms.** The complex vector norm is at most the sum of its coordinate norms. Source: Breakdown.SmoothFlow.bilin_norm_le_sum in Breakdown.Uniqueness.RegCurveAuxBilin, line 99. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L99).

**Extended norm below coordinate sum.** The extended complex vector norm is at most the sum of its coordinate extended norms. Source: Breakdown.SmoothFlow.bilin_enorm_le_sum in Breakdown.Uniqueness.RegCurveAuxBilin, line 106. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L106).

**Coordinate advection convolution.** A coordinate of bilinear advection is the sum of convolutions of one field with coordinate derivatives of the other. Source: Breakdown.SmoothFlow.bilin_adv_apply in Breakdown.Uniqueness.RegCurveAuxBilin, line 113. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L113).

**Advection convolution norm estimate.** The bilinear advection norm is bounded by nine times `2π` times the convolution of one norm with the other's first frequency moment. Source: Breakdown.SmoothFlow.bilin_adv_enorm_le in Breakdown.Uniqueness.RegCurveAuxBilin, line 117. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L117).

**Distributing the derivative weight.** The output polynomial weight times one input frequency is bounded by the product of the two order-`k+1` input weights. Source: Breakdown.SmoothFlow.bilin_weight_mul_le in Breakdown.Uniqueness.RegCurveAuxBilin, line 137. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L137).

**Total mass of a nonnegative convolution.** The total lower integral of a measurable nonnegative convolution equals the product of the two total masses. Source: Breakdown.SmoothFlow.bilin_lintegral_conv in Breakdown.Uniqueness.RegCurveAuxBilin, line 151. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L151).

**Weighted L1 advection bound.** The weighted L1 norm of advection is bounded by `18π` times the two order-`k+1` weighted L1 norms. Source: Breakdown.SmoothFlow.bilin_lintegral_adv_le in Breakdown.Uniqueness.RegCurveAuxBilin, line 167. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L167).

**Measurable convolution of components.** Convolving two almost-everywhere strongly measurable complex functions preserves that measurability. Source: Breakdown.SmoothFlow.bilin_convC_aesm in Breakdown.Uniqueness.RegCurveAuxBilin, line 206. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L206).

**Measurable bilinear advection.** Bilinear advection of two measurable symbols is almost-everywhere strongly measurable. Source: Breakdown.SmoothFlow.bilin_adv_aesm in Breakdown.Uniqueness.RegCurveAuxBilin, line 210. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L210).

**Advection respects representatives.** Changing either symbol on a null set leaves the bilinear advection function unchanged. Source: Breakdown.SmoothFlow.bilin_adv_congr in Breakdown.Uniqueness.RegCurveAuxBilin, line 229. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L229).

**Weighted L1 closure of advection.** Two symbols in weighted L1 of order `k+1` produce advection in weighted L1 of order `k`. Source: Breakdown.SmoothFlow.bilin_memLp in Breakdown.Uniqueness.RegCurveAuxBilin, line 241. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L241).

**Integrability at a convolution point.** Existence of a convolution at a frequency gives integrability of its shifted-product integrand. Source: Breakdown.SmoothFlow.bilin_integrable_at in Breakdown.Uniqueness.RegCurveAuxBilin, line 251. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L251).

**Advection integrable almost everywhere.** Weighted L1 inputs make every component advection integrand integrable at almost every output frequency. Source: Breakdown.SmoothFlow.bilin_ae_exists in Breakdown.Uniqueness.RegCurveAuxBilin, line 256. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L256).

**Advection adds in its first argument.** Under the weighted L1 hypotheses, bilinear advection distributes over addition in its first input almost everywhere. Source: Breakdown.SmoothFlow.bilin_adv_add_left in Breakdown.Uniqueness.RegCurveAuxBilin, line 267. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L267).

**Advection adds in its second argument.** Under the weighted L1 hypotheses, bilinear advection distributes over addition in its second input almost everywhere. Source: Breakdown.SmoothFlow.bilin_adv_add_right in Breakdown.Uniqueness.RegCurveAuxBilin, line 280. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L280).

**Advection scales in its first argument.** Real scalar multiplication in the first input factors out of bilinear advection. Source: Breakdown.SmoothFlow.bilin_adv_smul_left in Breakdown.Uniqueness.RegCurveAuxBilin, line 293. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L293).

**Advection scales in its second argument.** Real scalar multiplication in the second input factors out of bilinear advection. Source: Breakdown.SmoothFlow.bilin_adv_smul_right in Breakdown.Uniqueness.RegCurveAuxBilin, line 305. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L305).

**Advection on weighted L1 classes.** The Lp advection operation takes the weighted-L1 class of the pointwise bilinear advection. Source: Breakdown.SmoothFlow.advectionLp in Breakdown.Uniqueness.RegCurveAuxBilin, line 317. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L317).

**Representative of Lp advection.** The representative of Lp advection equals pointwise bilinear advection almost everywhere for the output weighted measure. Source: Breakdown.SmoothFlow.advectionLp_coe in Breakdown.Uniqueness.RegCurveAuxBilin, line 321. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L321).

**Lp advection adds on the left.** The weighted-L1 advection operation distributes over addition in its first argument. Source: Breakdown.SmoothFlow.advectionLp_add_left in Breakdown.Uniqueness.RegCurveAuxBilin, line 325. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L325).

**Lp advection adds on the right.** The weighted-L1 advection operation distributes over addition in its second argument. Source: Breakdown.SmoothFlow.advectionLp_add_right in Breakdown.Uniqueness.RegCurveAuxBilin, line 335. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L335).

**Lp advection scales on the left.** The weighted-L1 advection operation is homogeneous over real scalars in its first argument. Source: Breakdown.SmoothFlow.advectionLp_smul_left in Breakdown.Uniqueness.RegCurveAuxBilin, line 345. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L345).

**Lp advection scales on the right.** The weighted-L1 advection operation is homogeneous over real scalars in its second argument. Source: Breakdown.SmoothFlow.advectionLp_smul_right in Breakdown.Uniqueness.RegCurveAuxBilin, line 353. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L353).

**Lp advection norm bound.** The weighted-L1 advection operation has norm at most `18π‖F‖‖G‖`. Source: Breakdown.SmoothFlow.advectionLp_norm_le in Breakdown.Uniqueness.RegCurveAuxBilin, line 361. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L361).

**Continuous bilinear advection operator.** There exists a continuous bilinear weighted-L1 operator that represents the pointwise advection formula on all admissible inputs. Source: Breakdown.SmoothFlow.exists_bilin_advection in Breakdown.Uniqueness.RegCurveAuxBilin, line 380. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxBilin.lean#L380).

### Breakdown.Uniqueness.RegCurveAuxMeasure

This file compares polynomially weighted measures with volume to transfer measurability and almost-everywhere statements.

Reading context: §5 and Appendix A.2; measure changes for weighted-L1 curves.

**Source namespace:** Breakdown.SmoothFlow.

**Weighted frequency volume.** Weighted frequency volume is ordinary volume multiplied by density `(1+‖ξ‖)^k`. Source: Breakdown.SmoothFlow.weightedVolume in Breakdown.Uniqueness.RegCurveAuxMeasure, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMeasure.lean#L12).

**Weighted-volume integral formula.** A lower integral against weighted frequency volume equals the ordinary lower integral with the weight inserted. Source: Breakdown.SmoothFlow.lintegral_weightedVolume in Breakdown.Uniqueness.RegCurveAuxMeasure, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMeasure.lean#L15).

**Sobolev regularity gives weighted L1.** A measurable symbol with finite H^(k+2) energy belongs to polynomially weighted L1 of order `k`. Source: Breakdown.SmoothFlow.memLp_weightedVolume_of_hsNormSq in Breakdown.Uniqueness.RegCurveAuxMeasure, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMeasure.lean#L22).

### Breakdown.Uniqueness.RegCurveAuxMult

This file controls the frequency multipliers that act on the weighted-L1 regularity spaces.

Reading context: §5 and Appendix A.2; multiplier estimates for regular curves.

**Source namespace:** Breakdown.SmoothFlow.Internal.

**Measurability of the weight.** The polynomial frequency weight is measurable. Source: Breakdown.SmoothFlow.Internal.measurable_weight in Breakdown.Uniqueness.RegCurveAuxMult, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L14).

**Frequency weight never vanishes.** The nonnegative polynomial frequency weight is nonzero at every frequency. Source: Breakdown.SmoothFlow.Internal.weight_ne_zero in Breakdown.Uniqueness.RegCurveAuxMult, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L18).

**Density formula for weighted integration.** The weighted lower integral is the ordinary lower integral multiplied by the polynomial density. Source: Breakdown.SmoothFlow.Internal.lintegral_weighted in Breakdown.Uniqueness.RegCurveAuxMult, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L22).

**Equivalent null sets for all weights.** Any two polynomially weighted volumes are related by absolute continuity. Source: Breakdown.SmoothFlow.Internal.ac_weighted in Breakdown.Uniqueness.RegCurveAuxMult, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L27).

**Weighted multiplier estimate.** A measurable multiplier satisfying the stated weighted norm bound maps weighted L1 input into weighted L1 output with the same constant. Source: Breakdown.SmoothFlow.Internal.memLp_mult in Breakdown.Uniqueness.RegCurveAuxMult, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L32).

**Continuous linear multiplier realization.** A measurable real-linear multiplier with the stated weighted bound is realized as a continuous linear map between weighted L1 spaces. Source: Breakdown.SmoothFlow.Internal.exists_clm_mult in Breakdown.Uniqueness.RegCurveAuxMult, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L57).

**Frequency dot-product bound.** The frequency dot product is bounded by `3‖ξ‖‖z‖`. Source: Breakdown.SmoothFlow.Internal.norm_dot_le in Breakdown.Uniqueness.RegCurveAuxMult, line 95. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L95).

**Complexification bounds frequency.** The frequency-vector norm is at most the complexification operator norm times `‖ξ‖`. Source: Breakdown.SmoothFlow.Internal.norm_freqVec_le in Breakdown.Uniqueness.RegCurveAuxMult, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L104).

**Projection bound via complexification.** The divergence-free projection is bounded by `(1+3‖complexifyVec‖)‖z‖`. Source: Breakdown.SmoothFlow.Internal.norm_divFreeC_le in Breakdown.Uniqueness.RegCurveAuxMult, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L107).

**Pressure projection norm bound.** The vector pressure multiplier is bounded by `3‖complexifyVec‖/(2π)` times the input norm. Source: Breakdown.SmoothFlow.Internal.norm_pressure_le in Breakdown.Uniqueness.RegCurveAuxMult, line 127. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L127).

**Source namespace:** Breakdown.SmoothFlow.

**Laplacian multiplier on weighted L1.** The multiplier `-4π²‖ξ‖²` defines a continuous linear map lowering the weighted L1 order by two. Source: Breakdown.SmoothFlow.exists_clm_mulNormSq in Breakdown.Uniqueness.RegCurveAuxMult, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L154).

**Negative Leray projection on weighted L1.** The negative divergence-free projection defines a continuous linear map on each weighted L1 space. Source: Breakdown.SmoothFlow.exists_clm_divFree in Breakdown.Uniqueness.RegCurveAuxMult, line 173. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L173).

**Pressure multiplier on weighted L1.** The pressure-vector multiplier defines a continuous linear map on each weighted L1 space. Source: Breakdown.SmoothFlow.exists_clm_pressureProj in Breakdown.Uniqueness.RegCurveAuxMult, line 199. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxMult.lean#L199).

### Breakdown.Uniqueness.RegCurveAuxPartition

This file subdivides time intervals to apply local weighted-L1 estimates to an entire regular curve.

Reading context: §5 and Appendix A.2; patching local time regularity.

**Source namespace:** Breakdown.SmoothFlow.

**Partition points lie on the segment.** Every stated equally spaced subdivision point lies on the segment joining the two endpoints. Source: Breakdown.SmoothFlow.mem_segment_partition_point in Breakdown.Uniqueness.RegCurveAuxPartition, line 12. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPartition.lean#L12).

**Vanishing derivative partition error.** For a continuously differentiable curve on a segment, the sum of its linearised subdivision errors tends to zero. Source: Breakdown.SmoothFlow.partition_sum_tendsto_zero in Breakdown.Uniqueness.RegCurveAuxPartition, line 21. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPartition.lean#L21).

**Integrated derivative remainder.** The stated uniform bound on derivative differences controls the integrated first-order remainder by interval length times that bound. Source: Breakdown.SmoothFlow.lintegral_enorm_increment_le in Breakdown.Uniqueness.RegCurveAuxPartition, line 94. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPartition.lean#L94).

**From pointwise derivatives to L1.** Pointwise derivatives with the stated L1 continuity and representative conditions give the derivative of the L1-valued curve. Source: Breakdown.SmoothFlow.hasDerivWithinAt_toLp_of_pointwise in Breakdown.Uniqueness.RegCurveAuxPartition, line 175. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPartition.lean#L175).

### Breakdown.Uniqueness.RegCurveAuxPointwise

This file relates weighted-L1 curve statements to pointwise frequency representatives and their time integrals.

Reading context: §5 and Appendix A.2; representatives of regular frequency curves.

**Source namespace:** Breakdown.SmoothFlow.Internal.

**L2 bound from a Sobolev density bound.** A pointwise squared-norm bound by `K` times the H1 density gives the corresponding square-root L2 bound. Source: Breakdown.SmoothFlow.Internal.eLpNorm_two_le_of_pointwise in Breakdown.Uniqueness.RegCurveAuxPointwise, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPointwise.lean#L14).

**Coordinate L2 norm from H1.** Each coordinate L2 norm is bounded by the square root of H1 energy. Source: Breakdown.SmoothFlow.Internal.eLpNorm_component_le in Breakdown.Uniqueness.RegCurveAuxPointwise, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPointwise.lean#L30).

**Derivative-coordinate L2 norm from H1.** Each Fourier coordinate derivative has L2 norm bounded by the square root of `4π²` times H1 energy. Source: Breakdown.SmoothFlow.Internal.eLpNorm_weighted_le in Breakdown.Uniqueness.RegCurveAuxPointwise, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPointwise.lean#L38).

**Convergence of a scaled square root.** Multiplication by a finite nonnegative constant followed by a square root preserves convergence to zero. Source: Breakdown.SmoothFlow.Internal.tendsto_rpow_const_mul in Breakdown.Uniqueness.RegCurveAuxPointwise, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPointwise.lean#L59).

**Continuous L2 product pairing.** Two L2 curves continuous in their L2 distances have a continuous integral product pairing. Source: Breakdown.SmoothFlow.Internal.continuousOn_integral_mul in Breakdown.Uniqueness.RegCurveAuxPointwise, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPointwise.lean#L66).

**Source namespace:** Breakdown.SmoothFlow.

**Continuous advection symbol in time.** The advection symbol of an H1 curve is continuous in time at each fixed frequency. Source: Breakdown.SmoothFlow.continuousOn_advectionSymbol_apply in Breakdown.Uniqueness.RegCurveAuxPointwise, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPointwise.lean#L118).

**Differentiating Duhamel pointwise.** At each frequency, the Duhamel formula and continuous nonlinearity give the time derivative `-4π²‖ξ‖²F+nonlinSymbol(F)` within the interval. Source: Breakdown.SmoothFlow.hasDerivWithinAt_apply_of_varConst in Breakdown.Uniqueness.RegCurveAuxPointwise, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegCurveAuxPointwise.lean#L172).

### Breakdown.Uniqueness.RegDefs

This file defines regular Fourier solutions, their velocity and pressure symbols, and the solenoidal and conjugate-symmetry constraints.

Reading context: §5 and Appendix A.2; the regular Fourier solution framework.

**Source namespace:** Breakdown.SmoothFlow.

**Sobolev frequency weight.** The order-`m` Sobolev weight is `(1+‖ξ‖²)^m`. Source: Breakdown.SmoothFlow.hsWeight in Breakdown.Uniqueness.RegDefs, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L13).

**Squared Sobolev norm.** The squared Sobolev norm is the lower integral of the Sobolev weight times the squared symbol norm. Source: Breakdown.SmoothFlow.hsNormSq in Breakdown.Uniqueness.RegDefs, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L15).

**Squared homogeneous Sobolev norm.** The homogeneous squared norm uses frequency weight `‖ξ‖^(2k)`. Source: Breakdown.SmoothFlow.homNormSq in Breakdown.Uniqueness.RegDefs, line 18. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L18).

**Fourier L1 norm.** The Fourier L1 norm is the lower integral of the symbol norm. Source: Breakdown.SmoothFlow.freqL1Norm in Breakdown.Uniqueness.RegDefs, line 21. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L21).

**First frequency moment.** The first frequency moment integrates `‖ξ‖` times the symbol norm. Source: Breakdown.SmoothFlow.gradFreqL1Norm in Breakdown.Uniqueness.RegDefs, line 23. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L23).

**Heat multiplier.** The heat multiplier is `exp(-4π²t‖ξ‖²)`. Source: Breakdown.SmoothFlow.heatSymbol in Breakdown.Uniqueness.RegDefs, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L25).

**Complex divergence-free projection.** The complex Leray projection subtracts the component parallel to the frequency vector. Source: Breakdown.SmoothFlow.divFreeC in Breakdown.Uniqueness.RegDefs, line 27. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L27).

**Complex convolution.** Complex convolution integrates `f(η)g(ξ-η)` over the input frequency. Source: Breakdown.SmoothFlow.convC in Breakdown.Uniqueness.RegDefs, line 30. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L30).

**Bilinear advection symbol.** The bilinear advection symbol convolves the first vector field's components with Fourier derivatives of the second. Source: Breakdown.SmoothFlow.advectionBilin in Breakdown.Uniqueness.RegDefs, line 32. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L32).

**Quadratic advection symbol.** The advection symbol is bilinear advection with the same symbol in both arguments. Source: Breakdown.SmoothFlow.advectionSymbol in Breakdown.Uniqueness.RegDefs, line 36. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L36).

**Projected nonlinear symbol.** The nonlinear symbol is the negative divergence-free projection of the advection symbol. Source: Breakdown.SmoothFlow.nonlinSymbol in Breakdown.Uniqueness.RegDefs, line 38. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L38).

**Pressure symbol.** The pressure symbol divides the negative frequency contraction of advection by `2πi‖ξ‖²`. Source: Breakdown.SmoothFlow.pressureSymbol in Breakdown.Uniqueness.RegDefs, line 40. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L40).

**Solenoidal real-field symbol.** This proposition requires both zero frequency contraction and conjugate symmetry under frequency negation. Source: Breakdown.SmoothFlow.IsSolenoidalSymbol in Breakdown.Uniqueness.RegDefs, line 43. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L43).

**Symbol of a real vector field.** The symbol of a real field is the Fourier transform of its complexification. Source: Breakdown.SmoothFlow.symbolOf in Breakdown.Uniqueness.RegDefs, line 54. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L54).

**Physical field from a symbol.** The physical field is the real vector part of the inverse Fourier transform. Source: Breakdown.SmoothFlow.physField in Breakdown.Uniqueness.RegDefs, line 56. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L56).

**Physical scalar from a symbol.** The physical scalar is the real part of the inverse Fourier transform. Source: Breakdown.SmoothFlow.physScalar in Breakdown.Uniqueness.RegDefs, line 58. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegDefs.lean#L58).

### Breakdown.Uniqueness.RegEmbed

This file embeds regular solenoidal Fourier symbols into the abstract state space and identifies their physical velocity and gradients.

Reading context: §5 and Appendix A.2; the regular-to-abstract state bridge.

**Source namespace:** Breakdown.SmoothFlow.

**Lp conversion recovers valid input.** For an L2 function, the total Lp conversion agrees with the input almost everywhere. Source: Breakdown.SmoothFlow.toLpOrZero_ae in Breakdown.Uniqueness.RegEmbed, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L14).

**L2 physical derivatives.** A measurable symbol with every Sobolev norm finite gives L2 coordinate derivatives of its physical field. Source: Breakdown.SmoothFlow.memLp_partial in Breakdown.Uniqueness.RegEmbed, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L20).

**Physical field belongs to H1.** A measurable solenoidal symbol with all Sobolev orders finite gives a physical field satisfying the H1 field conditions. Source: Breakdown.SmoothFlow.isH1Field_physField in Breakdown.Uniqueness.RegEmbed, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L26).

**Conjugate symmetry from solenoidality.** The solenoidal-symbol condition includes conjugate symmetry under frequency negation. Source: Breakdown.SmoothFlow.conjSym_of in Breakdown.Uniqueness.RegEmbed, line 41. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L41).

**Fourier form of physical derivatives.** The complexified L2 class of a physical coordinate derivative is the inverse L2 Fourier transform of its derivative-multiplied symbol. Source: Breakdown.SmoothFlow.complexify_partial in Breakdown.Uniqueness.RegEmbed, line 44. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L44).

**Continuous complex multiplication.** Complex scalar multiplication, viewed as a linear-map-valued operation, is continuous. Source: Breakdown.SmoothFlow.continuous_cmul' in Breakdown.Uniqueness.RegEmbed, line 61. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L61).

**Norm of complex scalar multiplication.** The complex scalar multiplication operator has norm at most the scalar's absolute value. Source: Breakdown.SmoothFlow.norm_cmul_le' in Breakdown.Uniqueness.RegEmbed, line 66. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L66).

**Bounded gradient multiplier.** Each normalised gradient multiplier has norm at most one. Source: Breakdown.SmoothFlow.norm_gradSymbol_le' in Breakdown.Uniqueness.RegEmbed, line 71. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L71).

**Realization of the gradient multiplier.** Under the multiplier-realization interface, the gradient field operator is represented almost everywhere by pointwise gradient multiplication. Source: Breakdown.SmoothFlow.gradOp_ae' in Breakdown.Uniqueness.RegEmbed, line 77. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L77).

**Frequency norm in three coordinates.** The squared frequency norm is the sum of its three squared coordinates. Source: Breakdown.SmoothFlow.norm_sq_coords in Breakdown.Uniqueness.RegEmbed, line 84. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L84).

**Combining the three gradient factors.** Under the stated squared-length identity, the three paired gradient factors sum to `2π` times the length. Source: Breakdown.SmoothFlow.scalar_identity in Breakdown.Uniqueness.RegEmbed, line 88. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L88).

**Gradient multipliers give radial weight.** Summing the three gradient multipliers applied to derivative symbols gives `2π‖ξ‖f(ξ)`. Source: Breakdown.SmoothFlow.sum_gradSymbol_dmul in Breakdown.Uniqueness.RegEmbed, line 105. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L105).

**Gradient carrier of a physical field.** For a measurable solenoidal symbol with every Sobolev norm finite, the realized gradient carrier of its physical field equals `2π‖ξ‖f(ξ)` almost everywhere. Source: Breakdown.SmoothFlow.ofGrad_physField_ae in Breakdown.Uniqueness.RegEmbed, line 112. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L112).

**Null-set equality under negation.** Almost-everywhere equality is preserved by negating the frequency argument. Source: Breakdown.SmoothFlow.ae_comp_neg' in Breakdown.Uniqueness.RegEmbed, line 134. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L134).

**Coordinate form of the frequency pairing.** The inner product with the frequency vector equals the sum of frequency-coordinate products. Source: Breakdown.SmoothFlow.inner_freqVec in Breakdown.Uniqueness.RegEmbed, line 138. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L138).

**Frequency complexification is isometric.** The complex frequency vector has the same norm as the real frequency. Source: Breakdown.SmoothFlow.norm_freqVec' in Breakdown.Uniqueness.RegEmbed, line 143. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L143).

**Contractive longitudinal projection.** The longitudinal projection has operator norm at most one. Source: Breakdown.SmoothFlow.norm_longitudinal_le' in Breakdown.Uniqueness.RegEmbed, line 146. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L146).

**Measurable longitudinal projection.** The longitudinal projection is almost-everywhere strongly measurable as an operator-valued function. Source: Breakdown.SmoothFlow.aesm_longitudinal' in Breakdown.Uniqueness.RegEmbed, line 160. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L160).

**The gradient meets the constraints.** The physical field's gradient carrier lies in the constrained Fourier subspace under the stated solenoidal realization hypotheses. Source: Breakdown.SmoothFlow.ofGrad_physField_mem in Breakdown.Uniqueness.RegEmbed, line 171. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L171).

**Embedding equals the radial multiplier.** For a measurable solenoidal symbol with every Sobolev norm finite, the realized Hilbert-space embedding of its physical field is represented almost everywhere by `2π‖ξ‖f(ξ)`. Source: Breakdown.SmoothFlow.coe_embedX_physField in Breakdown.Uniqueness.RegEmbed, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L201).

**Embedding norm equals gradient energy.** The squared embedding norm equals `4π²` times the real value of the first homogeneous Fourier energy. Source: Breakdown.SmoothFlow.norm_embedX_physField_sq in Breakdown.Uniqueness.RegEmbed, line 210. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbed.lean#L210).

### Breakdown.Uniqueness.RegEmbedAux

This file proves the Fourier multiplier, integrability and constraint identities needed for the regular-state embedding.

Reading context: §5 and Appendix A.2; analytic support for the embedding.

**Source namespace:** Breakdown.SmoothFlow.Internal.RegEmbed.

**Coordinate derivative multiplier.** The coordinate derivative multiplier multiplies the symbol by `2πiξ_k`. Source: Breakdown.SmoothFlow.Internal.RegEmbed.dmul in Breakdown.Uniqueness.RegEmbedAux, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L14).

**Frequency coordinate bounded by norm.** Each absolute frequency coordinate is at most the full frequency norm. Source: Breakdown.SmoothFlow.Internal.RegEmbed.abs_coord_le in Breakdown.Uniqueness.RegEmbedAux, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L17).

**Derivative multiplier norm bound.** The coordinate derivative multiplier has norm at most `2π‖ξ‖` times the input norm. Source: Breakdown.SmoothFlow.Internal.RegEmbed.norm_dmul_le in Breakdown.Uniqueness.RegEmbedAux, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L20).

**All Fourier moments are integrable.** This proposition requires symbol measurability and integrability of every polynomial moment of its norm. Source: Breakdown.SmoothFlow.Internal.RegEmbed.HasMoments in Breakdown.Uniqueness.RegEmbedAux, line 28. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L28).

**All Sobolev orders give all moments.** A measurable symbol with finite Sobolev norms at every order has all Fourier moments integrable. Source: Breakdown.SmoothFlow.Internal.RegEmbed.hasMoments_of in Breakdown.Uniqueness.RegEmbedAux, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L31).

**Source namespace:** Breakdown.SmoothFlow.Internal.RegEmbed.HasMoments.

**Integrability from all moments.** The all-moments condition implies integrability of the symbol itself. Source: Breakdown.SmoothFlow.Internal.RegEmbed.HasMoments.integrable in Breakdown.Uniqueness.RegEmbedAux, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L45).

**Integrability of the first moment.** The all-moments condition implies integrability of frequency norm times symbol norm. Source: Breakdown.SmoothFlow.Internal.RegEmbed.HasMoments.integrable_one in Breakdown.Uniqueness.RegEmbedAux, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L50).

**Source namespace:** Breakdown.SmoothFlow.Internal.RegEmbed.

**Moments survive differentiation.** Applying a coordinate derivative multiplier preserves the all-moments condition. Source: Breakdown.SmoothFlow.Internal.RegEmbed.hasMoments_dmul in Breakdown.Uniqueness.RegEmbedAux, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L54).

**Coordinate from a unit-vector pairing.** Inner product with a coordinate unit vector returns that coordinate. Source: Breakdown.SmoothFlow.Internal.RegEmbed.inner_unitVector in Breakdown.Uniqueness.RegEmbedAux, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L67).

**Inverse transform of a derivative.** An integrable symbol with integrable first moment has inverse-transform derivative in coordinate `k` equal to the inverse transform of `2πiξ_k f`. Source: Breakdown.SmoothFlow.Internal.RegEmbed.fderiv_freqTrInv in Breakdown.Uniqueness.RegEmbedAux, line 70. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L70).

**Conjugating twice gives the vector.** Applying vector conjugation twice is the identity. Source: Breakdown.SmoothFlow.Internal.RegEmbed.conjVec_conjVec in Breakdown.Uniqueness.RegEmbedAux, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L101).

**Conjugation of scalar multiplication.** Vector conjugation conjugates the scalar and the vector in a scalar product. Source: Breakdown.SmoothFlow.Internal.RegEmbed.conjVec_smul in Breakdown.Uniqueness.RegEmbedAux, line 105. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L105).

**Integrability under a Fourier character.** Multiplication by a unit-modulus Fourier character preserves integrability. Source: Breakdown.SmoothFlow.Internal.RegEmbed.integrable_char_smul in Breakdown.Uniqueness.RegEmbedAux, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L109).

**Conjugation reverses the character.** Conjugating the Fourier character at `t` gives the character at `-t`. Source: Breakdown.SmoothFlow.Internal.RegEmbed.star_char in Breakdown.Uniqueness.RegEmbedAux, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L114).

**Real inverse transform from symmetry.** An integrable conjugate-symmetric symbol has an inverse Fourier transform fixed by conjugation. Source: Breakdown.SmoothFlow.Internal.RegEmbed.conjVec_freqTrInv in Breakdown.Uniqueness.RegEmbedAux, line 118. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L118).

**Recovering a conjugation-fixed vector.** Complexifying the real part of a conjugation-fixed vector returns that vector. Source: Breakdown.SmoothFlow.Internal.RegEmbed.complexifyVec_realVec in Breakdown.Uniqueness.RegEmbedAux, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L125).

**Derivative multipliers preserve symmetry.** Multiplication by `2πiξ_k` preserves conjugate symmetry under frequency negation. Source: Breakdown.SmoothFlow.Internal.RegEmbed.conjSym_dmul in Breakdown.Uniqueness.RegEmbedAux, line 132. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L132).

**Smooth inverse transform from moments.** A symbol with all Fourier moments integrable has a smooth inverse Fourier transform. Source: Breakdown.SmoothFlow.Internal.RegEmbed.contDiff_freqTrInv in Breakdown.Uniqueness.RegEmbedAux, line 138. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L138).

**Physical derivative by inverse transform.** A physical coordinate derivative is the real part of the inverse transform of the corresponding derivative-multiplied symbol. Source: Breakdown.SmoothFlow.Internal.RegEmbed.partialField_physField in Breakdown.Uniqueness.RegEmbedAux, line 143. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L143).

**Zero physical divergence from the symbol.** For a solenoidal all-moments symbol, the sum of inverse-transformed coordinate derivative components is zero. Source: Breakdown.SmoothFlow.Internal.RegEmbed.sum_freqTrInv_dmul in Breakdown.Uniqueness.RegEmbedAux, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L151).

**L2 membership from weighted domination.** A measurable symbol dominated in squared norm by a finite Sobolev density belongs to L2. Source: Breakdown.SmoothFlow.Internal.RegEmbed.memLp_two_of_le in Breakdown.Uniqueness.RegEmbedAux, line 172. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L172).

**L2 membership from all Sobolev orders.** A measurable symbol with all Sobolev norms finite belongs to L2. Source: Breakdown.SmoothFlow.Internal.RegEmbed.memLp_self in Breakdown.Uniqueness.RegEmbedAux, line 182. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L182).

**L2 derivative symbol.** Under the all-moments and finite-Sobolev assumptions, each coordinate derivative-multiplied symbol belongs to L2. Source: Breakdown.SmoothFlow.Internal.RegEmbed.memLp_dmul in Breakdown.Uniqueness.RegEmbedAux, line 186. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L186).

**Ordinary and L2 inverse transforms agree.** For an L1 and L2 symbol, the ordinary inverse transform agrees almost everywhere with its L2 inverse transform. Source: Breakdown.SmoothFlow.Internal.RegEmbed.freqTrInv_ae in Breakdown.Uniqueness.RegEmbedAux, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L201).

**L2 physical inverse transform.** The real part of the inverse transform of an L1 and L2 symbol belongs to L2. Source: Breakdown.SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv in Breakdown.Uniqueness.RegEmbedAux, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegEmbedAux.lean#L205).

### Breakdown.Uniqueness.RegGlue

This file combines regular Fourier existence, continuation and uniqueness to obtain physical regularity of an abstract mild solution.

Reading context: §5 and Appendix A.2; the continuation construction.

**Source namespace:** Breakdown.SmoothFlow.

**Test symbols have all Sobolev orders.** A smooth compactly supported solenoidal test field has a Fourier symbol with every Sobolev norm finite. Source: Breakdown.SmoothFlow.hsNormSq_symbolOf_all in Breakdown.Uniqueness.RegGlue, line 22. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlue.lean#L22).

**Kernel bound for the realization.** Identifying the realized interaction with the bounded Fourier bilinear kernel gives the `τ^(-3/4)` operator bound. Source: Breakdown.SmoothFlow.norm_kernel_le in Breakdown.Uniqueness.RegGlue, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlue.lean#L26).

**Matching Fourier and abstract flows.** Under the stated realization interfaces, an H3 symbol flow and the abstract mild flow with the same test-field data have equal embedded physical velocities. Source: Breakdown.SmoothFlow.embedX_physField_eq_of_flow in Breakdown.Uniqueness.RegGlue, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlue.lean#L33).

### Breakdown.Uniqueness.RegGlueAux

This file verifies the interval and compatibility properties used to glue regular solutions.

Reading context: §5 and Appendix A.2; compatibility across continuation times.

**Source namespace:** Breakdown.SmoothFlow.

**Symbol-flow contract.** This proposition combines an Hm curve, Duhamel's formula, solenoidal slices and the prescribed initial symbol. Source: Breakdown.SmoothFlow.IsSymbolFlow in Breakdown.Uniqueness.RegGlueAux, line 15. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlueAux.lean#L15).

**First homogeneous energy below H1.** The first homogeneous energy is bounded by the H1 energy. Source: Breakdown.SmoothFlow.homNormSq_one_le_hsNormSq in Breakdown.Uniqueness.RegGlueAux, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlueAux.lean#L19).

**Initial symbol as a zero-time flow.** A measurable solenoidal symbol with finite Hm norm defines a constant symbol flow on the degenerate interval ending at zero. Source: Breakdown.SmoothFlow.isSymbolFlow_const in Breakdown.Uniqueness.RegGlueAux, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlueAux.lean#L26).

**Higher regularity along a symbol flow.** An H3 symbol flow inherits every finite Sobolev order possessed by its initial data. Source: Breakdown.SmoothFlow.isHsCurve_of_flow in Breakdown.Uniqueness.RegGlueAux, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlueAux.lean#L38).

**Continuation from a homogeneous bound.** If every partial H3 symbol flow up to `T` has the stated uniform first homogeneous bound, a symbol flow exists on the whole interval `[0,T]`. Source: Breakdown.SmoothFlow.exists_symbolFlow_of_homBound in Breakdown.Uniqueness.RegGlueAux, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegGlueAux.lean#L45).

### Breakdown.Uniqueness.RegIdentify

This file identifies the embedded regular solution with the corresponding abstract mild solution.

Reading context: §5 and Appendix A.2; agreement of regular and abstract evolutions.

**Source namespace:** Breakdown.SmoothFlow.

**Fourier flow gives an abstract mild flow.** The stated realization interfaces turn an all-orders solenoidal Duhamel symbol curve into a mild curve in the Hilbert space. Source: Breakdown.SmoothFlow.isMildX_embedX_physField in Breakdown.Uniqueness.RegIdentify, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentify.lean#L12).

### Breakdown.Uniqueness.RegIdentifyAux

This file prepares the Fourier Duhamel identity for comparison with the abstract mild formulation.

Reading context: §5 and Appendix A.2; the mild-solution identification step.

**Source namespace:** Breakdown.SmoothFlow.

**Moving the radial factor outside time.** The `phiFactor` time integral equals `2π‖ξ‖` times the heat-symbol time integral. Source: Breakdown.SmoothFlow.integral_phiFactor_smul in Breakdown.Uniqueness.RegIdentifyAux, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAux.lean#L17).

**Integrable abstract nonlinear trajectory.** For the stated regular solenoidal curve, the embedded physical bilinear interaction is interval integrable up to each allowed time. Source: Breakdown.SmoothFlow.intervalIntegrable_bilinX_physField in Breakdown.Uniqueness.RegIdentifyAux, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAux.lean#L31).

**Fourier form of the nonlinear integral.** The abstract bilinear time integral is represented almost everywhere by the time integral of `phiFactor` times the nonlinear symbol. Source: Breakdown.SmoothFlow.coe_integral_bilinX_physField in Breakdown.Uniqueness.RegIdentifyAux, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAux.lean#L49).

### Breakdown.Uniqueness.RegIdentifyAuxAdvect

This file establishes weighted integrability of the advection symbol needed for the abstract bilinear operator.

Reading context: §5 and Appendix A.2; identification of physical advection.

**Source namespace:** Breakdown.SmoothFlow.

**Weighted L1 from Sobolev norms.** A measurable symbol with all Sobolev norms finite belongs to every polynomially weighted L1 space. Source: Breakdown.SmoothFlow.memLp_weight_of_hsNormSq in Breakdown.Uniqueness.RegIdentifyAuxAdvect, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxAdvect.lean#L12).

**Physical advection matches its symbol.** For the stated regular solenoidal symbol, physical advection equals the physical field reconstructed from the advection symbol. Source: Breakdown.SmoothFlow.advectionAt_physField_eq in Breakdown.Uniqueness.RegIdentifyAuxAdvect, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxAdvect.lean#L19).

### Breakdown.Uniqueness.RegIdentifyAuxBilin

This file identifies the Fourier nonlinear term with the abstract bilinear interaction.

Reading context: §5 and Appendix A.2; agreement of the two nonlinear operators.

**Source namespace:** Breakdown.SmoothFlow.

**Fourier form of the realized interaction.** At positive elapsed time, the realized bilinear interaction is represented by `phiFactor` times the nonlinear symbol. Source: Breakdown.SmoothFlow.coe_bilinX_physField in Breakdown.Uniqueness.RegIdentifyAuxBilin, line 15. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxBilin.lean#L15).

### Breakdown.Uniqueness.RegIdentifyAuxCont

This file proves continuity of the embedded regular curve and its nonlinear terms.

Reading context: §5 and Appendix A.2; continuity in the abstract mild identity.

**Source namespace:** Breakdown.SmoothFlow.Internal.RegIdentifyCont.

**L2 bound for the radial gradient factor.** Multiplying by `2π‖ξ‖` gives an L2 norm at most the square root of `4π²` times H1 energy. Source: Breakdown.SmoothFlow.Internal.RegIdentifyCont.eLpNorm_gradWeight_le in Breakdown.Uniqueness.RegIdentifyAuxCont, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxCont.lean#L14).

**Convergence of a scaled square root.** Multiplication by a finite nonnegative constant followed by a square root preserves convergence to zero. Source: Breakdown.SmoothFlow.Internal.RegIdentifyCont.tendsto_rpow_half in Breakdown.Uniqueness.RegIdentifyAuxCont, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxCont.lean#L36).

**Source namespace:** Breakdown.SmoothFlow.

**Continuous embedded physical flow.** An all-orders solenoidal Sobolev curve has a continuous embedded physical velocity on the closed time interval. Source: Breakdown.SmoothFlow.continuousOn_embedX_physField in Breakdown.Uniqueness.RegIdentifyAuxCont, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxCont.lean#L47).

### Breakdown.Uniqueness.RegIdentifyAuxDivFree

This file analyzes the Leray projection and its frequency-divergence cancellation.

Reading context: §5 and Appendix A.2; the divergence-free nonlinear symbol.

**Source namespace:** Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.

**Valid complex L2 conversion.** For an L2 complex vector function, the total Lp conversion agrees with the function almost everywhere. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.toLpOrZero_ae_eq in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L18).

**Valid real L2 conversion.** For an L2 real vector field, the total Lp conversion agrees with the field almost everywhere. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.toLpOrZero_ae_eq_real in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L23).

**Longitudinal projection formula.** The longitudinal projection is the frequency-vector inner product times that vector divided by squared frequency norm. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.longitudinal_eq in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L28).

**Frequency inner product formula.** The frequency-vector inner product equals the sum of complex-cast frequency coordinates times vector coordinates. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.inner_freqVec_eq in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L31).

**Frequency complexification is isometric.** The complex frequency vector has the same norm as the real frequency. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.norm_freqVec_eq in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L36).

**Frequency vector at the origin.** The complex frequency vector at zero is zero. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.freqVec_zero in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L39).

**Leray projection as a complement.** The divergence-free projection is the identity minus the longitudinal projection. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.divFreeC_eq_sub in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L41).

**Contractive longitudinal projection.** The longitudinal projection has operator norm at most one. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.norm_longitudinal_le_one in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L44).

**Measurable longitudinal projection.** The longitudinal projection is almost-everywhere strongly measurable as an operator-valued function. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.aestronglyMeasurable_longitudinal in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L58).

**Continuous differentiated heat factor.** The differentiated heat factor is continuous as a function of frequency for every fixed elapsed time. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.continuous_phi in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 69. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L69).

**Even differentiated heat factor.** Negating frequency leaves the differentiated heat factor unchanged. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.phiFactor_neg in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L73).

**Uniform differentiated heat bound.** For positive elapsed time, the differentiated heat factor is bounded by `2π(1+(4π²τ)⁻¹)`. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.norm_phiFactor_le in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 76. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L76).

**Projection is frequency-orthogonal.** At nonzero frequency, the projected vector has zero inner product with the frequency vector. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.inner_freqVec_divFreeC in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L100).

**Longitudinal part of a projected vector.** Applying the longitudinal projection to a divergence-free projected vector gives zero at every frequency. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.longitudinal_divFreeC in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L109).

**Projection respects conjugate symmetry.** Conjugating the projection at negative frequency reproduces the projection at positive frequency. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.conjVec_divFreeC_neg in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L115).

**Orthogonality to a longitudinal image.** A vector killed by the longitudinal projection is real-orthogonal to every vector in that projection's image. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.inner_longitudinal_eq_zero in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 121. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L121).

**Representative of complexification.** Complexification of a real L2 class is represented almost everywhere by pointwise vector complexification. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.coe_complexify in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 142. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L142).

**Fourier inversion in the real L2 class.** For an L1-L2 conjugate-symmetric symbol, Fourier transforming the complexified physical L2 field recovers the symbol's L2 class. Source: Breakdown.SmoothFlow.Internal.RegIdentifyDivFree.freqTrR_complexify_physField in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L146).

**Source namespace:** Breakdown.SmoothFlow.

**Fourier form of heat and projection.** The heat-divergence-free realization of a physical field is represented by `phiFactor` times the complex Leray projection of its symbol. Source: Breakdown.SmoothFlow.coe_heatDivFree_physField in Breakdown.Uniqueness.RegIdentifyAuxDivFree, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxDivFree.lean#L163).

### Breakdown.Uniqueness.RegIdentifyAuxHeat

This file identifies multiplication by the Fourier heat factor with the abstract heat evolution.

Reading context: §5 and Appendix A.2; agreement of the two heat semigroups.

**Source namespace:** Breakdown.SmoothFlow.

**Fourier form of the heat operator.** Under the heat realization interfaces, the abstract heat operator is pointwise multiplication by the heat factor almost everywhere. Source: Breakdown.SmoothFlow.coe_heatX_ae in Breakdown.Uniqueness.RegIdentifyAuxHeat, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxHeat.lean#L12).

### Breakdown.Uniqueness.RegIdentifyAuxSwap

This file exchanges the time integral with the embedding and gives a pointwise representative of the integrated symbol.

Reading context: §5 and Appendix A.2; interchange in the mild identity.

**Source namespace:** Breakdown.SmoothFlow.

**L2 bound on inner-product integrals.** The integral of the absolute complex inner product of two L2 fields is at most the product of their L2 norms. Source: Breakdown.SmoothFlow.integral_norm_inner_le_mul in Breakdown.Uniqueness.RegIdentifyAuxSwap, line 12. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSwap.lean#L12).

**Representing the time integral.** Under the stated integrability and joint measurability conditions, the Hilbert-space time integral is represented almost everywhere by pointwise time integration. Source: Breakdown.SmoothFlow.coe_intervalIntegral_ae in Breakdown.Uniqueness.RegIdentifyAuxSwap, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSwap.lean#L27).

### Breakdown.Uniqueness.RegIdentifyAuxSymbol

This file proves the integrability and derivative bounds required to interpret a regular symbol in the abstract state space.

Reading context: §5 and Appendix A.2; admissibility of regular frequency symbols.

**Source namespace:** Breakdown.SmoothFlow.Internal.

**Integrable coordinates of the symbol.** Each coordinate of a measurable symbol with all Sobolev orders finite is integrable. Source: Breakdown.SmoothFlow.Internal.component_integrable in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 14. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L14).

**Finite first frequency moment.** All Sobolev norms finite imply finiteness of the norm integral weighted by `1+‖ξ‖`. Source: Breakdown.SmoothFlow.Internal.weighted_lintegral_lt_top in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 25. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L25).

**Integrable Fourier derivatives.** Each coordinate frequency derivative of a measurable symbol with all Sobolev orders finite is integrable. Source: Breakdown.SmoothFlow.Internal.coord_component_integrable in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 31. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L31).

**L1 closure under complex convolution.** The convolution of two integrable complex functions is integrable. Source: Breakdown.SmoothFlow.Internal.convC_integrable in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 47. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L47).

**Integrability of the advection symbol.** A measurable symbol with all Sobolev orders finite has integrable advection symbol. Source: Breakdown.SmoothFlow.Internal.advectionSymbol_integrable in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 54. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L54).

**Vector conjugation by coordinates.** A coordinate of vector conjugation is the conjugate of that coordinate. Source: Breakdown.SmoothFlow.Internal.conjVec_coord in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 73. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L73).

**Convolution under conjugate reflection.** If both factors have the stated conjugate-reflection relations, their convolution has the corresponding conjugate-reflection relation. Source: Breakdown.SmoothFlow.Internal.convC_neg_conj in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 75. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L75).

**Source namespace:** Breakdown.SmoothFlow.

**Advection symbol belongs to L1.** For a regular measurable solenoidal symbol, the advection symbol belongs to L1. Source: Breakdown.SmoothFlow.memLp_one_advectionSymbol in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L89).

**Advection symbol belongs to L2.** For a regular measurable solenoidal symbol, the advection symbol belongs to L2. Source: Breakdown.SmoothFlow.memLp_two_advectionSymbol in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L94).

**Conjugate symmetry of advection.** The advection symbol of the stated regular solenoidal field is conjugate-symmetric under frequency negation. Source: Breakdown.SmoothFlow.advectionSymbol_neg in Breakdown.Uniqueness.RegIdentifyAuxSymbol, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxSymbol.lean#L115).

### Breakdown.Uniqueness.RegIdentifyAuxTime

This file establishes time continuity and measurability of the Fourier nonlinear expressions used in the embedded mild formula.

Reading context: §5 and Appendix A.2; time regularity of the abstract interaction.

**Source namespace:** Breakdown.SmoothFlow.Internal.

**Translation-reflection preserves mass.** Changing the integration variable from `η` to `ξ-η` preserves a nonnegative lower integral. Source: Breakdown.SmoothFlow.Internal.lintegral_comp_sub_left in Breakdown.Uniqueness.RegIdentifyAuxTime, line 14. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L14).

**Pointwise convolution from L2 norms.** The convolution norm is bounded by the square roots of the two squared-norm lower integrals. Source: Breakdown.SmoothFlow.Internal.enorm_convC_le in Breakdown.Uniqueness.RegIdentifyAuxTime, line 19. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L19).

**Three-term difference of L2 convolutions.** For L2 factors, subtracting two convolutions gives one difference-difference convolution plus two mixed convolutions. Source: Breakdown.SmoothFlow.Internal.convC_sub_eq in Breakdown.Uniqueness.RegIdentifyAuxTime, line 32. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L32).

**Square-root convergence to zero.** Taking square roots preserves convergence of nonnegative extended reals to zero. Source: Breakdown.SmoothFlow.Internal.tendsto_rpow_half_zero in Breakdown.Uniqueness.RegIdentifyAuxTime, line 51. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L51).

**L2 limits preserve convolution.** Convergence of both time-dependent factors in L2 gives convergence of their convolution at every fixed output frequency. Source: Breakdown.SmoothFlow.Internal.tendsto_convC in Breakdown.Uniqueness.RegIdentifyAuxTime, line 57. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L57).

**H1 density controls each coordinate.** A coordinate's squared norm is bounded by the full symbol's H1 density. Source: Breakdown.SmoothFlow.Internal.component_sq_le in Breakdown.Uniqueness.RegIdentifyAuxTime, line 103. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L103).

**H1 bounds coordinate multipliers.** A constant times a frequency coordinate times a symbol coordinate has squared norm bounded by the constant's square times the H1 density. Source: Breakdown.SmoothFlow.Internal.coord_sq_le in Breakdown.Uniqueness.RegIdentifyAuxTime, line 112. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L112).

**Coordinate energy from H1.** The squared-L2 integral of a symbol coordinate is at most its H1 energy. Source: Breakdown.SmoothFlow.Internal.lintegral_component_le in Breakdown.Uniqueness.RegIdentifyAuxTime, line 129. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L129).

**Multiplied coordinate energy from H1.** The squared-L2 integral of a constant frequency-coordinate multiplier is bounded by the constant's squared norm times H1 energy. Source: Breakdown.SmoothFlow.Internal.lintegral_coord_le in Breakdown.Uniqueness.RegIdentifyAuxTime, line 133. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L133).

**L2 from a finite square integral.** A measurable complex function with finite squared-norm lower integral belongs to L2. Source: Breakdown.SmoothFlow.Internal.memLp_of_lintegral_sq in Breakdown.Uniqueness.RegIdentifyAuxTime, line 138. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L138).

**Measurability of a coordinate.** Taking a symbol coordinate preserves almost-everywhere strong measurability. Source: Breakdown.SmoothFlow.Internal.aestronglyMeasurable_component in Breakdown.Uniqueness.RegIdentifyAuxTime, line 144. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L144).

**Measurability of a coordinate multiplier.** Multiplying a measurable symbol coordinate by a constant and a frequency coordinate preserves almost-everywhere strong measurability. Source: Breakdown.SmoothFlow.Internal.aestronglyMeasurable_coord in Breakdown.Uniqueness.RegIdentifyAuxTime, line 148. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L148).

**Continuity of derivative convolutions.** Along an H1 curve, the component convolution with a constant frequency-coordinate multiplier converges at every time and output frequency. Source: Breakdown.SmoothFlow.Internal.tendsto_convC_component in Breakdown.Uniqueness.RegIdentifyAuxTime, line 154. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L154).

**Continuous Fourier projection.** At fixed frequency, the complex divergence-free projection is continuous in its vector argument. Source: Breakdown.SmoothFlow.Internal.continuous_divFreeC in Breakdown.Uniqueness.RegIdentifyAuxTime, line 182. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L182).

**Convolution respects null-set equality.** Changing either convolution factor on a null set leaves every output value unchanged. Source: Breakdown.SmoothFlow.Internal.convC_congr in Breakdown.Uniqueness.RegIdentifyAuxTime, line 186. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L186).

**Strongly measurable complex convolution.** The convolution of two strongly measurable complex functions is strongly measurable. Source: Breakdown.SmoothFlow.Internal.stronglyMeasurable_convC in Breakdown.Uniqueness.RegIdentifyAuxTime, line 196. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L196).

**Strongly measurable nonlinear symbol.** An almost-everywhere strongly measurable vector symbol gives a strongly measurable nonlinear symbol. Source: Breakdown.SmoothFlow.Internal.stronglyMeasurable_nonlinSymbol in Breakdown.Uniqueness.RegIdentifyAuxTime, line 202. [Proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L202).

**Source namespace:** Breakdown.SmoothFlow.

**Continuous nonlinear symbol.** For the stated all-orders solenoidal curve, the nonlinear symbol is continuous in time at each frequency. Source: Breakdown.SmoothFlow.continuousOn_nonlinSymbol_apply in Breakdown.Uniqueness.RegIdentifyAuxTime, line 244. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L244).

**Joint measurability of the nonlinearity.** The nonlinear symbol of the stated all-orders solenoidal curve is jointly measurable on the closed time-frequency slab. Source: Breakdown.SmoothFlow.aestronglyMeasurable_uncurry_nonlinSymbol in Breakdown.Uniqueness.RegIdentifyAuxTime, line 255. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxTime.lean#L255).

### Breakdown.Uniqueness.RegIdentifyAuxVecIntegral

This file justifies vector-valued integration and norm bounds for the singular heat-bilinear time integral.

Reading context: §5 and Appendix A.2; Bochner integration in the mild identification.

**Source namespace:** Breakdown.SmoothFlow.

**Nonnegative differentiated heat factor.** The differentiated heat factor is nonnegative for every time and frequency. Source: Breakdown.SmoothFlow.phiFactor_nonneg' in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L13).

**Half-power differentiated heat bound.** For positive elapsed time, the differentiated heat factor is at most `τ^(-1/2)`. Source: Breakdown.SmoothFlow.phiFactor_le_rpow in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 17. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L17).

**Gaussian domination away from zero time.** For `τ ≥ τ₀ > 0`, the squared differentiated heat factor is bounded by `τ₀⁻¹ exp(-4π²τ₀‖ξ‖²)`. Source: Breakdown.SmoothFlow.phiFactor_sq_le in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 50. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L50).

**Integrable frequency Gaussian.** The frequency Gaussian `exp(-a‖ξ‖²)` is integrable for `a > 0`. Source: Breakdown.SmoothFlow.integrable_exp_neg_sq in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 82. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L82).

**Monotone Sobolev norm comparison.** A squared Sobolev norm is bounded by every higher-order squared Sobolev norm. Source: Breakdown.SmoothFlow.hsNormSq_le_of_le in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 93. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L93).

**L2 norm from order-zero Sobolev energy.** The extended L2 norm is the square root of order-zero Sobolev energy. Source: Breakdown.SmoothFlow.eLpNorm_two_eq_hs in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 99. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L99).

**Uniform pointwise nonlinear bound.** An H3 curve has one finite pointwise bound for its nonlinear symbol throughout the closed time interval and all frequencies. Source: Breakdown.SmoothFlow.nonlinSymbol_bound in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 105. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L105).

**Uniform L2 nonlinear bound.** An H3 curve has one finite L2 bound for its nonlinear symbols throughout the closed time interval. Source: Breakdown.SmoothFlow.eLpNorm_nonlinSymbol_bound in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 133. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L133).

**Continuity before the singular endpoint.** The realized bilinear trajectory is continuous in the integration time on `[0,t)` for the stated regular flow. Source: Breakdown.SmoothFlow.continuousOn_bilinX_physField in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 168. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L168).

**An integrable interaction singularity.** The realized bilinear interaction along the regular flow is bounded uniformly in the slice time by `Cτ^(-1/2)` for positive elapsed time. Source: Breakdown.SmoothFlow.norm_bilinX_physField_le in Breakdown.Uniqueness.RegIdentifyAuxVecIntegral, line 279. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegIdentifyAuxVecIntegral.lean#L279).

### Breakdown.Uniqueness.RegInitial

This file constructs regular Fourier initial data from smooth test fields and verifies their Sobolev and symmetry properties.

Reading context: §5 and Appendix A.2; admissible data for regular local existence.

**Source namespace:** Breakdown.SmoothFlow.

**Compact complexified test-field support.** Complexifying a test field preserves compact support. Source: Breakdown.SmoothFlow.hasCompactSupport_complexifyComp in Breakdown.Uniqueness.RegInitial, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L12).

**Smooth complexified test field.** Complexifying a test field preserves smoothness. Source: Breakdown.SmoothFlow.contDiff_complexifyComp in Breakdown.Uniqueness.RegInitial, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L16).

**Test field as a Schwartz function.** The complexification of a test field is packaged as a Schwartz function using smoothness and compact support. Source: Breakdown.SmoothFlow.testRapid in Breakdown.Uniqueness.RegInitial, line 20. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L20).

**Underlying Schwartz test function.** The underlying function of the Schwartz test-field package is the pointwise complexification of the original field. Source: Breakdown.SmoothFlow.testRapid_coe in Breakdown.Uniqueness.RegInitial, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L23).

**Schwartz Fourier symbol of test data.** The Schwartz test symbol is the Fourier transform of the Schwartz complexified test field. Source: Breakdown.SmoothFlow.testSymbol in Breakdown.Uniqueness.RegInitial, line 26. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L26).

**The test symbol is its Fourier image.** The ordinary symbol of a test field equals the underlying function of its Schwartz Fourier symbol. Source: Breakdown.SmoothFlow.symbolOf_eq_freqTr in Breakdown.Uniqueness.RegInitial, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L29).

**Measurable test-field symbol.** The Fourier symbol of a test field is almost-everywhere strongly measurable. Source: Breakdown.SmoothFlow.aestronglyMeasurable_symbolOf in Breakdown.Uniqueness.RegInitial, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L34).

**Real test data give conjugate symmetry.** The symbol of a real test field at negative frequency is the conjugate of its symbol at positive frequency. Source: Breakdown.SmoothFlow.freqTr_neg_complexify in Breakdown.Uniqueness.RegInitial, line 39. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L39).

**Trace on complex derivative matrices.** The complex trace map sums the three diagonal coordinate evaluations of a derivative matrix. Source: Breakdown.SmoothFlow.traceMap in Breakdown.Uniqueness.RegInitial, line 55. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L55).

**Coordinate formula for the trace.** The trace linear map evaluates to the sum of the three diagonal matrix entries. Source: Breakdown.SmoothFlow.traceMap_apply in Breakdown.Uniqueness.RegInitial, line 59. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L59).

**Derivative of complexified test data.** The derivative of a complexified test field is complexification composed with the real derivative. Source: Breakdown.SmoothFlow.fderiv_complexifyComp in Breakdown.Uniqueness.RegInitial, line 62. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L62).

**Divergence-free test symbol.** The frequency contraction of a test field's Fourier symbol is zero. Source: Breakdown.SmoothFlow.divergence_symbolOf in Breakdown.Uniqueness.RegInitial, line 66. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L66).

**Test symbols satisfy solenoidality.** The Fourier symbol of a test field satisfies both zero frequency contraction and conjugate symmetry. Source: Breakdown.SmoothFlow.isSolenoidalSymbol_symbolOf in Breakdown.Uniqueness.RegInitial, line 97. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L97).

**Polynomial growth of Sobolev weights.** Every Sobolev frequency weight has temperate growth. Source: Breakdown.SmoothFlow.hasTemperateGrowth_hsWeight in Breakdown.Uniqueness.RegInitial, line 101. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L101).

**Finite Sobolev norms of test symbols.** The Fourier symbol of a test field has finite Sobolev norm at every integer order. Source: Breakdown.SmoothFlow.hsNormSq_symbolOf_lt_top in Breakdown.Uniqueness.RegInitial, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L104).

**Recovering the original test field.** Taking the physical inverse transform of a test field's symbol returns the original test field. Source: Breakdown.SmoothFlow.physField_symbolOf in Breakdown.Uniqueness.RegInitial, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegInitial.lean#L125).

### Breakdown.Uniqueness.RegLocal

This file proves local existence of a regular Fourier solution for the stated Sobolev initial data.

Reading context: §5 and Appendix A.2; local regular-solution construction.

**Source namespace:** Breakdown.SmoothFlow.

**Uniform local symbol existence.** For `m ≥ 3`, an initial Hm energy bound determines one positive lifespan valid for every measurable solenoidal initial symbol with that bound. Source: Breakdown.SmoothFlow.exists_local_varConst in Breakdown.Uniqueness.RegLocal, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocal.lean#L12).

### Breakdown.Uniqueness.RegLocalAuxCurve

This file builds the time-dependent convolution terms used in the local fixed-point map.

Reading context: §5 and Appendix A.2; the nonlinear curve in local existence.

**Source namespace:** Breakdown.SmoothFlow.

**Adding Sobolev curves.** The pointwise sum of two Hm curves on the same interval is an Hm curve. Source: Breakdown.SmoothFlow.isHsCurve_add in Breakdown.Uniqueness.RegLocalAuxCurve, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurve.lean#L13).

**Heat evolution is a Sobolev curve.** A measurable symbol with finite Hm energy gives an Hm curve under its heat evolution from the stated initial time. Source: Breakdown.SmoothFlow.heatPart_isHsCurve in Breakdown.Uniqueness.RegLocalAuxCurve, line 32. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurve.lean#L32).

**Duhamel map preserves Sobolev curves.** For `m ≥ 3` and the stated initial data, the variation-of-constants map sends an Hm curve to an Hm curve. Source: Breakdown.SmoothFlow.varConstMap_isHsCurve in Breakdown.Uniqueness.RegLocalAuxCurve, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurve.lean#L44).

### Breakdown.Uniqueness.RegLocalAuxCurvePart1

This file proves convolution continuity and bounds for the Sobolev curves entering the local construction.

Reading context: §5 and Appendix A.2; continuity of the local nonlinear map.

**Source namespace:** Breakdown.SmoothFlow.

**Duhamel forcing integral.** The forcing integral integrates the heat multiplier times the forcing symbol from the initial time to the current time. Source: Breakdown.SmoothFlow.varConstIntegral in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L14).

**Real square equals integer square.** The real second power of a nonnegative extended real equals its natural-number square. Source: Breakdown.SmoothFlow.rpow_two_eq in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 17. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L17).

**Separating the heat time difference.** The heat multiplier at `t-s` factors into the multipliers at `t` and `-s`. Source: Breakdown.SmoothFlow.heat_mul in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L20).

**Squared heat multiplier.** The squared heat multiplier is `exp(-8π²‖ξ‖²τ)`. Source: Breakdown.SmoothFlow.heat_sq in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 27. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L27).

**Weighted exponential time integral.** For nonnegative `L` and ordered times, the weighted exponential integral is at most elapsed time plus one. Source: Breakdown.SmoothFlow.integral_exp_le in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 34. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L34).

**Extended norm of the heat scalar.** The extended norm of the complex-cast heat multiplier is its nonnegative-real value. Source: Breakdown.SmoothFlow.enorm_ofReal_heat in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 76. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L76).

**Weighted squared heat time bound.** Multiplying the squared heat time integral by `1+‖ξ‖²` gives a bound by elapsed time plus one. Source: Breakdown.SmoothFlow.lintegral_heat_sq_le in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 80. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L80).

**Cauchy-Schwarz for the forcing integral.** The squared forcing integral norm is bounded by the squared-heat time integral times the squared-forcing time integral. Source: Breakdown.SmoothFlow.enorm_varConstIntegral_sq_le in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 94. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L94).

**Successor Sobolev weight.** The order-`n+1` Sobolev weight equals the order-`n` weight times `1+‖ξ‖²`. Source: Breakdown.SmoothFlow.hsWeight_succ in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 124. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L124).

**One-order gain in the forcing estimate.** The weighted forcing integral at order `n+1` is bounded by interval length plus one times the integrated order-`n` forcing density. Source: Breakdown.SmoothFlow.varConst_weight_le in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 129. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L129).

**Squared norm of a difference.** The squared extended norm of a difference is at most twice the sum of the squared norms. Source: Breakdown.SmoothFlow.enorm_sub_sq_le in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 152. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L152).

**Sobolev weights are at least one.** Every nonnegative-real Sobolev weight is at least one. Source: Breakdown.SmoothFlow.one_le_hsWeight in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 165. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L165).

**Measurable Sobolev weight.** The nonnegative-real Sobolev weight is measurable. Source: Breakdown.SmoothFlow.measurable_hsWeight in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 170. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L170).

**Forcing integral gives a Sobolev curve.** A jointly measurable forcing with uniformly bounded Hn energy gives an H^(n+1) forcing-integral curve. Source: Breakdown.SmoothFlow.varConstIntegral_isHsCurve in Breakdown.Uniqueness.RegLocalAuxCurvePart1, line 176. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart1.lean#L176).

### Breakdown.Uniqueness.RegLocalAuxCurvePart2

This file estimates the projected nonlinear symbol and its Sobolev energy along the candidate curve.

Reading context: §5 and Appendix A.2; bounds for the projected local nonlinearity.

**Source namespace:** Breakdown.SmoothFlow.

**Jointly measurable complex projection.** The divergence-free projection is measurable jointly in frequency and vector input. Source: Breakdown.SmoothFlow.measurable_divFreeC_pair in Breakdown.Uniqueness.RegLocalAuxCurvePart2, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart2.lean#L14).

**Joint nonlinear measurability from H1.** A Sobolev curve of order at least one has a jointly measurable nonlinear symbol on the frequency-time slab. Source: Breakdown.SmoothFlow.nonlinSymbol_aestronglyMeasurable_curve in Breakdown.Uniqueness.RegLocalAuxCurvePart2, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart2.lean#L27).

**Monotone Sobolev norms.** The squared Sobolev norm increases with integer order. Source: Breakdown.SmoothFlow.hsNormSq_mono in Breakdown.Uniqueness.RegLocalAuxCurvePart2, line 45. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart2.lean#L45).

**Projected Sobolev energy bound.** The nonlinear symbol's Hk energy is at most four times the advection symbol's Hk energy. Source: Breakdown.SmoothFlow.hsNormSq_nonlinSymbol_le_four in Breakdown.Uniqueness.RegLocalAuxCurvePart2, line 53. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart2.lean#L53).

**Uniform lower-order nonlinear energy.** For `k ≥ 2`, an H^(k+1) curve has one bound for its nonlinear symbol's Hk energy throughout the interval. Source: Breakdown.SmoothFlow.hsNormSq_nonlinSymbol_curve_le in Breakdown.Uniqueness.RegLocalAuxCurvePart2, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart2.lean#L73).

### Breakdown.Uniqueness.RegLocalAuxCurvePart3

This file develops the continuity and integrability of coordinate convolution products in L2.

Reading context: §5 and Appendix A.2; the coordinate-level local convolution argument.

**Source namespace:** Breakdown.SmoothFlow.

**Complex squared difference bound.** The squared norm of a difference of complex numbers is at most twice the sum of their squared norms. Source: Breakdown.SmoothFlow.enorm_sub_sq_le_c in Breakdown.Uniqueness.RegLocalAuxCurvePart3, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart3.lean#L12).

**Finite square integral of a difference.** Under the stated measurability and finite-square hypotheses, subtracting two complex functions has finite squared-norm lower integral. Source: Breakdown.SmoothFlow.lintegral_sub_ne_top in Breakdown.Uniqueness.RegLocalAuxCurvePart3, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart3.lean#L25).

**Half powers preserve zero limits.** Taking the half power preserves convergence to zero for nonnegative extended reals along any filter. Source: Breakdown.SmoothFlow.half_rpow_tendsto in Breakdown.Uniqueness.RegLocalAuxCurvePart3, line 34. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart3.lean#L34).

**A finite square root is finite.** The half power of a finite nonnegative extended real is finite. Source: Breakdown.SmoothFlow.half_rpow_ne_top in Breakdown.Uniqueness.RegLocalAuxCurvePart3, line 40. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart3.lean#L40).

**Jointly continuous L2 convolutions.** The stated L2-continuous component curves have a convolution continuous jointly in output frequency and time. Source: Breakdown.SmoothFlow.continuousOn_convC_param in Breakdown.Uniqueness.RegLocalAuxCurvePart3, line 43. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart3.lean#L43).

**L2 bound for a coefficient multiplier.** A pointwise squared coefficient bound by `C` times a Sobolev weight bounds the multiplied coordinate's squared integral by `C` times Sobolev energy. Source: Breakdown.SmoothFlow.lintegral_coef_le in Breakdown.Uniqueness.RegLocalAuxCurvePart3, line 120. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart3.lean#L120).

**Jointly continuous bilinear advection.** The diagonal bilinear advection of a Sobolev curve of order at least one is jointly continuous in frequency and time. Source: Breakdown.SmoothFlow.continuousOn_advectionBilin_curve in Breakdown.Uniqueness.RegLocalAuxCurvePart3, line 137. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart3.lean#L137).

### Breakdown.Uniqueness.RegLocalAuxCurvePart4

This file proves the algebraic subtraction and integrability formulas for the local convolution map.

Reading context: §5 and Appendix A.2; difference estimates for the local nonlinear curve.

**Source namespace:** Breakdown.SmoothFlow.

**Real square equals integer square.** The real second power of a nonnegative extended real equals its natural-number square. Source: Breakdown.SmoothFlow.rpow_two_eq in Breakdown.Uniqueness.RegLocalAuxCurvePart4, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart4.lean#L12).

**Measurable shifted complex function.** Shifted reflection of an almost-everywhere strongly measurable complex function preserves that measurability. Source: Breakdown.SmoothFlow.aesm_comp_sub in Breakdown.Uniqueness.RegLocalAuxCurvePart4, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart4.lean#L15).

**Shifted-product Cauchy-Schwarz bound.** The lower integral of a shifted product of complex norms is bounded by the two L2 norms. Source: Breakdown.SmoothFlow.lintegral_mul_comp_sub_le in Breakdown.Uniqueness.RegLocalAuxCurvePart4, line 19. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart4.lean#L19).

**Pointwise L2 convolution bound.** The norm of a convolution is at most the product of the two L2 norms expressed as square-integral roots. Source: Breakdown.SmoothFlow.enorm_convC_le in Breakdown.Uniqueness.RegLocalAuxCurvePart4, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart4.lean#L31).

**Integrable L2 convolution products.** Two measurable square-integrable complex functions have an integrable shifted convolution product at every frequency. Source: Breakdown.SmoothFlow.integrable_convC_integrand in Breakdown.Uniqueness.RegLocalAuxCurvePart4, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart4.lean#L42).

**Subtracting the left convolution input.** For the stated L2 factors, a difference of convolutions in the first factor equals convolution with the difference. Source: Breakdown.SmoothFlow.convC_sub_left in Breakdown.Uniqueness.RegLocalAuxCurvePart4, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart4.lean#L52).

**Subtracting the right convolution input.** For the stated L2 factors, a difference of convolutions in the second factor equals convolution with the difference. Source: Breakdown.SmoothFlow.convC_sub_right in Breakdown.Uniqueness.RegLocalAuxCurvePart4, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart4.lean#L62).

### Breakdown.Uniqueness.RegLocalAuxCurvePart5

This file reconciles the complex convolution formulas with the library convolution operator and finishes the curve construction.

Reading context: §5 and Appendix A.2; assembly of the local nonlinear curve.

**Source namespace:** Breakdown.SmoothFlow.

**Real square equals integer square.** The real second power of a nonnegative extended real equals its natural-number square. Source: Breakdown.SmoothFlow.rpow_two_eq' in Breakdown.Uniqueness.RegLocalAuxCurvePart5, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart5.lean#L12).

**Integral-root formula for complex L2.** The complex extended L2 norm equals the square root of the squared-norm lower integral. Source: Breakdown.SmoothFlow.eLpNorm_two_eq in Breakdown.Uniqueness.RegLocalAuxCurvePart5, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart5.lean#L15).

**Complex L2 membership criterion.** A measurable complex function with finite squared-norm lower integral belongs to L2. Source: Breakdown.SmoothFlow.memLp_two_of in Breakdown.Uniqueness.RegLocalAuxCurvePart5, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart5.lean#L20).

**Finite square integral of an L2 function.** Membership in L2 makes the squared-norm lower integral finite. Source: Breakdown.SmoothFlow.lintegral_sq_ne_top_of_memLp in Breakdown.Uniqueness.RegLocalAuxCurvePart5, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart5.lean#L26).

**Complex and library convolutions agree.** The explicit complex convolution agrees with the library's multiplication-based convolution. Source: Breakdown.SmoothFlow.convC_eq_convolution in Breakdown.Uniqueness.RegLocalAuxCurvePart5, line 34. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart5.lean#L34).

**Continuity of an L2 convolution.** The convolution of two measurable square-integrable complex functions is continuous. Source: Breakdown.SmoothFlow.continuous_convC in Breakdown.Uniqueness.RegLocalAuxCurvePart5, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxCurvePart5.lean#L39).

### Breakdown.Uniqueness.RegLocalAuxEst

This file assembles the quantitative Sobolev bounds for the local fixed-point operator.

Reading context: §5 and Appendix A.2; contraction estimates for local existence.

**Source namespace:** Breakdown.SmoothFlow.

**Squared norm of a sum.** The squared extended norm of a sum is at most twice the sum of the squared norms. Source: Breakdown.SmoothFlow.enorm_add_sq_le' in Breakdown.Uniqueness.RegLocalAuxEst, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L15).

**Measurable Sobolev density.** The nonnegative-real Sobolev weight is measurable. Source: Breakdown.SmoothFlow.measurable_hsWeight_ofReal in Breakdown.Uniqueness.RegLocalAuxEst, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L29).

**Sobolev energy of a sum.** With the stated measurability, the Sobolev energy of `f+g` is at most twice the sum of the two energies. Source: Breakdown.SmoothFlow.hsNormSq_add_le_left in Breakdown.Uniqueness.RegLocalAuxEst, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L33).

**Heat does not increase Sobolev energy.** Multiplying by a heat symbol at nonnegative time does not increase any squared Sobolev norm. Source: Breakdown.SmoothFlow.hsNormSq_heat_smul_le in Breakdown.Uniqueness.RegLocalAuxEst, line 51. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L51).

**Squaring a nonnegative-real conversion.** The square of the nonnegative-real conversion of `B` is at most the conversion of `B²`. Source: Breakdown.SmoothFlow.ofReal_sq_le' in Breakdown.Uniqueness.RegLocalAuxEst, line 66. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L66).

**Continuous integration-time heat factor.** The complex-cast heat multiplier is continuous as the integration time varies. Source: Breakdown.SmoothFlow.continuous_heat_time in Breakdown.Uniqueness.RegLocalAuxEst, line 72. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L72).

**Bound on the local Duhamel map.** On intervals of length `δ ≤ 1`, the Hm energy of the Duhamel map is at most twice the initial energy plus `CδB²`. Source: Breakdown.SmoothFlow.varConstMap_bound in Breakdown.Uniqueness.RegLocalAuxEst, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L77).

**Contraction estimate for the Duhamel map.** For Hm curves in the stated energy ball, the Duhamel-map difference is bounded by `CδB` times the supremum squared Hm difference. Source: Breakdown.SmoothFlow.varConstMap_contract in Breakdown.Uniqueness.RegLocalAuxEst, line 124. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEst.lean#L124).

### Breakdown.Uniqueness.RegLocalAuxEstPart1

This file supplies weighted norm and heat estimates for the local fixed-point bounds.

Reading context: §5 and Appendix A.2; linear and weighted bounds in local existence.

**Source namespace:** Breakdown.SmoothFlow.

**Squared heat symbol formula.** The squared heat symbol is `exp(-8π²τ‖ξ‖²)`. Source: Breakdown.SmoothFlow.heatSymbol_sq in Breakdown.Uniqueness.RegLocalAuxEstPart1, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart1.lean#L12).

**Nonnegative heat multiplier.** The heat multiplier is nonnegative for every time and frequency. Source: Breakdown.SmoothFlow.heatSymbol_nonneg in Breakdown.Uniqueness.RegLocalAuxEstPart1, line 19. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart1.lean#L19).

**Explicit weighted heat time integral.** The integral of `x exp(-8π²(t-s)x)` equals the stated exponential difference divided by `8π²`. Source: Breakdown.SmoothFlow.integral_heatKernel in Breakdown.Uniqueness.RegLocalAuxEstPart1, line 22. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart1.lean#L22).

**Uniform heat-weight time bound.** On an interval of length at most one, the integral of `(1+‖ξ‖²)` times the squared heat multiplier is at most two. Source: Breakdown.SmoothFlow.lintegral_heatWeight_le in Breakdown.Uniqueness.RegLocalAuxEstPart1, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart1.lean#L38).

**Square cancels a half power.** The square of a nonnegative extended real's half power is the original number. Source: Breakdown.SmoothFlow.rpow_half_sq in Breakdown.Uniqueness.RegLocalAuxEstPart1, line 71. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart1.lean#L71).

**Sobolev gain for a heat forcing integral.** On intervals of length at most one, uniformly Hn-bounded measurable forcing gives an H^(n+1) integral bounded by twice elapsed time times the forcing bound. Source: Breakdown.SmoothFlow.hsNormSq_heatIntegral_le in Breakdown.Uniqueness.RegLocalAuxEstPart1, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart1.lean#L75).

### Breakdown.Uniqueness.RegLocalAuxEstPart2

This file proves joint measurability of the convolution and nonlinear representatives used by the fixed-point map.

Reading context: §5 and Appendix A.2; measurable local nonlinear representatives.

**Source namespace:** Breakdown.SmoothFlow.

**Measurability of convolution.** Convolution of strongly measurable complex functions is measurable. Source: Breakdown.SmoothFlow.measurable_convC_of in Breakdown.Uniqueness.RegLocalAuxEstPart2, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart2.lean#L12).

**Measurable self-advection.** A strongly measurable vector symbol has measurable diagonal bilinear advection. Source: Breakdown.SmoothFlow.measurable_advectionBilin_self in Breakdown.Uniqueness.RegLocalAuxEstPart2, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart2.lean#L18).

**Measurability under the Leray projection.** Applying the frequency-dependent Leray projection to a measurable vector symbol preserves measurability. Source: Breakdown.SmoothFlow.measurable_divFreeC_comp in Breakdown.Uniqueness.RegLocalAuxEstPart2, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart2.lean#L29).

**Measurable nonlinear symbol.** An almost-everywhere strongly measurable symbol has a measurable projected nonlinearity. Source: Breakdown.SmoothFlow.measurable_nonlinSymbol in Breakdown.Uniqueness.RegLocalAuxEstPart2, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart2.lean#L41).

**A measurable nonlinear representative.** The stated slice measurability and time continuity supply a jointly measurable function equal to the nonlinear curve on the closed interval. Source: Breakdown.SmoothFlow.exists_measurable_nonlin_curve in Breakdown.Uniqueness.RegLocalAuxEstPart2, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart2.lean#L46).

### Breakdown.Uniqueness.RegLocalAuxEstPart3

This file derives quadratic and difference bounds for the nonlinearity in the relevant Sobolev norm.

Reading context: §5 and Appendix A.2; nonlinear estimates for the local contraction.

**Source namespace:** Breakdown.SmoothFlow.

**Coordinates of the frequency vector.** Each complex frequency-vector coordinate is the complex cast of the corresponding real frequency coordinate. Source: Breakdown.SmoothFlow.freqVec_apply' in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L14).

**Frequency inner product in coordinates.** The complex inner product with the real frequency vector is the coordinate sum `∑ ξᵢwᵢ`. Source: Breakdown.SmoothFlow.inner_freqVec' in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L16).

**Frequency complexification is isometric.** The complex frequency vector has the same norm as the real frequency. Source: Breakdown.SmoothFlow.norm_freqVec in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L20).

**Projected vectors are transverse.** The divergence-free projection is orthogonal to the frequency vector at every frequency. Source: Breakdown.SmoothFlow.inner_freqVec_divFreeC in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L23).

**Leray projection contracts norm.** The divergence-free projection has vector norm at most the input norm. Source: Breakdown.SmoothFlow.norm_divFreeC_le_self in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L40).

**Projection preserves subtraction.** The divergence-free projection distributes over subtraction of vectors. Source: Breakdown.SmoothFlow.divFreeC_sub in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 62. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L62).

**Domination bounds Sobolev energy.** A pointwise norm bound between two symbols gives the same inequality between their squared Sobolev norms. Source: Breakdown.SmoothFlow.hsNormSq_le_of_norm_le in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 67. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L67).

**Monotonicity in Sobolev order.** The squared Sobolev norm increases with its order. Source: Breakdown.SmoothFlow.hsNormSq_mono in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 75. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L75).

**Square cancels a half power.** The square of a nonnegative extended real's half power is the original number. Source: Breakdown.SmoothFlow.rpow_half_sq in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 83. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L83).

**Squaring a square-root bound.** The stated bound by a constant times a square root implies a squared bound with constant `(|C|+1)²`. Source: Breakdown.SmoothFlow.sq_le_of_le_rpow in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 87. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L87).

**Advection loses one Sobolev order.** For `m ≥ 3`, bilinear advection's H^(m-1) energy is bounded by a positive constant times the two Hm energies. Source: Breakdown.SmoothFlow.hsNormSq_advectionBilin_le' in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 97. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L97).

**Projected nonlinearity norm bound.** The nonlinear symbol norm is at most the diagonal advection norm. Source: Breakdown.SmoothFlow.norm_nonlinSymbol_le in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 130. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L130).

**Quadratic nonlinear Sobolev bound.** For `m ≥ 3`, the nonlinear symbol's H^(m-1) energy is bounded by a positive constant times the square of the Hm energy. Source: Breakdown.SmoothFlow.hsNormSq_nonlinSymbol_le in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L135).

**Weight zero gives ordinary volume.** Polynomially weighted volume at order zero is ordinary volume. Source: Breakdown.SmoothFlow.weightedVolume_zero in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 145. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L145).

**Difference of quadratic advection.** Under the stated finite-Hm assumptions, the difference of diagonal advections equals the two bilinear difference terms almost everywhere. Source: Breakdown.SmoothFlow.advectionBilin_sub_ae in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 151. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L151).

**Local Lipschitz nonlinearity.** For `m ≥ 3`, the H^(m-1) energy of a nonlinear-symbol difference is controlled by the sum of Hm energies times the Hm difference energy. Source: Breakdown.SmoothFlow.hsNormSq_nonlinSymbol_sub_le in Breakdown.Uniqueness.RegLocalAuxEstPart3, line 174. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart3.lean#L174).

### Breakdown.Uniqueness.RegLocalAuxEstPart4

This file transfers between Sobolev orders and proves continuity of the nonlinear map on Sobolev curves.

Reading context: §5 and Appendix A.2; norm comparison in the local argument.

**Source namespace:** Breakdown.SmoothFlow.

**Higher Sobolev norms bound lower ones.** If `k ≤ m`, the squared Hk norm is bounded by the squared Hm norm. Source: Breakdown.SmoothFlow.hsNormSq_mono_index in Breakdown.Uniqueness.RegLocalAuxEstPart4, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart4.lean#L13).

**Shifting a Sobolev curve to time zero.** A Sobolev curve of order at least one becomes an H1 curve on `[0,b-a]` after shifting its initial time to zero. Source: Breakdown.SmoothFlow.isHsCurve_shift in Breakdown.Uniqueness.RegLocalAuxEstPart4, line 21. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart4.lean#L21).

**Continuous Leray projection in its input.** For fixed frequency, the complex divergence-free projection is continuous in its vector input. Source: Breakdown.SmoothFlow.continuous_divFreeC_apply in Breakdown.Uniqueness.RegLocalAuxEstPart4, line 37. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart4.lean#L37).

**Continuous Sobolev nonlinearity.** At each frequency, the nonlinear symbol of a Sobolev curve of order at least one is continuous on its time interval. Source: Breakdown.SmoothFlow.continuousOn_nonlinSymbol_curve in Breakdown.Uniqueness.RegLocalAuxEstPart4, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxEstPart4.lean#L41).

### Breakdown.Uniqueness.RegLocalAuxFix

This file applies the contraction construction and extracts a fixed point satisfying the Fourier mild equation.

Reading context: §5 and Appendix A.2; the local fixed-point step.

**Source namespace:** Breakdown.SmoothFlow.

**Picard iterates of the Duhamel map.** The fixed-point iteration starts from the constant initial symbol and repeatedly applies the Duhamel map. Source: Breakdown.SmoothFlow.fixedPointIter in Breakdown.Uniqueness.RegLocalAuxFix, line 15. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxFix.lean#L15).

**Sobolev energy is unchanged by negation.** Negating a symbol leaves its squared Sobolev norm unchanged. Source: Breakdown.SmoothFlow.hsNormSq_neg in Breakdown.Uniqueness.RegLocalAuxFix, line 19. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxFix.lean#L19).

**Symmetric Sobolev distance.** The squared Sobolev norm of `f-g` equals that of `g-f`. Source: Breakdown.SmoothFlow.hsNormSq_sub_comm in Breakdown.Uniqueness.RegLocalAuxFix, line 22. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxFix.lean#L22).

**Doubling a nonnegative-real value.** Doubling the nonnegative-real conversion of a real number equals converting its double. Source: Breakdown.SmoothFlow.two_mul_ofReal in Breakdown.Uniqueness.RegLocalAuxFix, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxFix.lean#L26).

**Existence of a local Duhamel fixed point.** For `m ≥ 3`, an initial energy bound gives a uniform positive lifespan and an Hm fixed point almost everywhere with conjugate-symmetric slices. Source: Breakdown.SmoothFlow.exists_varConst_fixedPoint in Breakdown.Uniqueness.RegLocalAuxFix, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxFix.lean#L31).

### Breakdown.Uniqueness.RegLocalAuxHs

This file proves measurability, addition bounds and the zero-norm criterion for the weighted Sobolev norm used in the local iteration.

Reading context: §5 and Appendix A.2; the local Sobolev solution space.

**Source namespace:** Breakdown.SmoothFlow.

**Measurable Sobolev weight.** The real Sobolev weight is measurable. Source: Breakdown.SmoothFlow.hsWeight_measurable in Breakdown.Uniqueness.RegLocalAuxHs, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxHs.lean#L12).

**Strictly positive Sobolev weight.** The Sobolev frequency weight is strictly positive at every frequency. Source: Breakdown.SmoothFlow.hsWeight_pos in Breakdown.Uniqueness.RegLocalAuxHs, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxHs.lean#L16).

**Measurable Sobolev energy density.** The weighted squared-norm integrand of a measurable symbol is almost-everywhere measurable. Source: Breakdown.SmoothFlow.hsIntegrand_aemeasurable in Breakdown.Uniqueness.RegLocalAuxHs, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxHs.lean#L20).

**Squared norm of a sum.** The squared extended norm of a sum is at most twice the sum of the squared norms. Source: Breakdown.SmoothFlow.enorm_add_sq_le in Breakdown.Uniqueness.RegLocalAuxHs, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxHs.lean#L25).

**Sobolev energy triangle bound.** The squared Sobolev norm of the sum of two measurable symbols is at most twice the sum of their squared norms. Source: Breakdown.SmoothFlow.hsNormSq_add_le in Breakdown.Uniqueness.RegLocalAuxHs, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxHs.lean#L39).

**Zero Sobolev energy forces zero.** A measurable symbol with zero Sobolev energy vanishes almost everywhere. Source: Breakdown.SmoothFlow.ae_eq_zero_of_hsNormSq_eq_zero in Breakdown.Uniqueness.RegLocalAuxHs, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxHs.lean#L57).

### Breakdown.Uniqueness.RegLocalAuxLimit

This file constructs limits of geometrically Cauchy Sobolev curves and passes the local iteration to its limit.

Reading context: §5 and Appendix A.2; convergence of the local fixed-point iteration.

**Source namespace:** Breakdown.SmoothFlow.

**Sobolev-weighted measure.** The Sobolev measure multiplies volume by the nonnegative-real Sobolev weight. Source: Breakdown.SmoothFlow.hsMeasure in Breakdown.Uniqueness.RegLocalAuxLimit, line 12. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L12).

**Measurable Sobolev measure density.** The nonnegative-real Sobolev density is measurable. Source: Breakdown.SmoothFlow.measurable_ofReal_hsWeight in Breakdown.Uniqueness.RegLocalAuxLimit, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L15).

**Sobolev measure follows volume null sets.** The Sobolev-weighted measure is absolutely continuous with respect to volume. Source: Breakdown.SmoothFlow.hsMeasure_ac in Breakdown.Uniqueness.RegLocalAuxLimit, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L20).

**Volume follows Sobolev null sets.** Volume is absolutely continuous with respect to the Sobolev-weighted measure. Source: Breakdown.SmoothFlow.volume_ac_hsMeasure in Breakdown.Uniqueness.RegLocalAuxLimit, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L23).

**Weighted L2 norm equals Sobolev norm.** The L2 norm for the Sobolev-weighted measure is the square root of Sobolev energy. Source: Breakdown.SmoothFlow.eLpNorm_hsMeasure in Breakdown.Uniqueness.RegLocalAuxLimit, line 30. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L30).

**Sobolev energy is weighted L2 squared.** The Sobolev energy is the square of the L2 norm for its weighted measure. Source: Breakdown.SmoothFlow.hsNormSq_eq_eLpNorm in Breakdown.Uniqueness.RegLocalAuxLimit, line 38. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L38).

**Weighted L2 bound from real energy.** A real bound on Sobolev energy bounds the corresponding L2 norm by the nonnegative-real square root. Source: Breakdown.SmoothFlow.eLpNorm_le_sqrt in Breakdown.Uniqueness.RegLocalAuxLimit, line 43. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L43).

**Finite Sobolev energy gives weighted L2.** A measurable symbol with finite Sobolev energy belongs to L2 for the Sobolev-weighted measure. Source: Breakdown.SmoothFlow.memLp_hsMeasure in Breakdown.Uniqueness.RegLocalAuxLimit, line 56. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L56).

**Lp norm of a Sobolev L2 element.** The extended L2 norm of a Sobolev L2 element is the nonnegative-real conversion of its norm. Source: Breakdown.SmoothFlow.eLpNorm_Lp_hsMeasure in Breakdown.Uniqueness.RegLocalAuxLimit, line 63. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L63).

**Frequency negation preserves energy.** Replacing a symbol by its frequency-reflected version leaves its Sobolev energy unchanged. Source: Breakdown.SmoothFlow.hsNormSq_comp_neg in Breakdown.Uniqueness.RegLocalAuxLimit, line 67. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L67).

**Conjugation preserves extended norm.** Vector conjugation preserves the extended norm. Source: Breakdown.SmoothFlow.enorm_conjVec_eq in Breakdown.Uniqueness.RegLocalAuxLimit, line 75. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L75).

**Conjugation preserves Sobolev energy.** Pointwise vector conjugation leaves the squared Sobolev norm unchanged. Source: Breakdown.SmoothFlow.hsNormSq_comp_conj in Breakdown.Uniqueness.RegLocalAuxLimit, line 80. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L80).

**Limits of geometric Cauchy curves.** The stated geometrically controlled sequence of bounded conjugate-symmetric Hm curves has an Hm limit with the same bound and uniform convergence in squared Hm distance. Source: Breakdown.SmoothFlow.hsCurve_limit in Breakdown.Uniqueness.RegLocalAuxLimit, line 84. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxLimit.lean#L84).

### Breakdown.Uniqueness.RegLocalAuxSymm

This file proves that the local construction preserves the frequency-divergence and conjugate-symmetry constraints.

Reading context: §5 and Appendix A.2; reality and incompressibility of local solutions.

**Source namespace:** Breakdown.SmoothFlow.

**Duhamel map.** The Duhamel map adds heat evolution of the initial symbol to the heat-weighted nonlinear forcing integral. Source: Breakdown.SmoothFlow.varConstMap in Breakdown.Uniqueness.RegLocalAuxSymm, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L12).

**Duhamel map at its initial time.** At the initial time, the Duhamel map equals the prescribed initial symbol. Source: Breakdown.SmoothFlow.varConstMap_self in Breakdown.Uniqueness.RegLocalAuxSymm, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L16).

**Convolution ignores null-set changes.** Almost-everywhere changes to either input leave every complex convolution value unchanged. Source: Breakdown.SmoothFlow.convC_congr_ae in Breakdown.Uniqueness.RegLocalAuxSymm, line 21. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L21).

**Nonlinearity ignores null-set changes.** Almost-everywhere equal symbols have identical nonlinear-symbol functions. Source: Breakdown.SmoothFlow.nonlinSymbol_congr_ae in Breakdown.Uniqueness.RegLocalAuxSymm, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L30).

**Sobolev curves ignore null-set changes.** Replacing every time slice by an almost-everywhere equal representative preserves the Sobolev-curve property. Source: Breakdown.SmoothFlow.isHsCurve_congr in Breakdown.Uniqueness.RegLocalAuxSymm, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L45).

**Squared frequency coordinates.** The sum of the three squared real frequency coordinates equals squared frequency norm. Source: Breakdown.SmoothFlow.sum_sq_eq_norm_sq in Breakdown.Uniqueness.RegLocalAuxSymm, line 66. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L66).

**Projection removes frequency divergence.** The divergence-free projection has zero frequency dot product at every frequency. Source: Breakdown.SmoothFlow.dot_divFreeC in Breakdown.Uniqueness.RegLocalAuxSymm, line 70. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L70).

**Solenoidal nonlinear symbol.** The projected nonlinear symbol has zero frequency contraction for every input symbol. Source: Breakdown.SmoothFlow.nonlinSymbol_div in Breakdown.Uniqueness.RegLocalAuxSymm, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L100).

**Coordinate conjugation formula.** Vector conjugation acts by complex conjugation on each coordinate. Source: Breakdown.SmoothFlow.conjVec_apply in Breakdown.Uniqueness.RegLocalAuxSymm, line 106. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L106).

**Frequency-vector coordinate formula.** The frequency-vector coordinates are the complex casts of the real frequency coordinates. Source: Breakdown.SmoothFlow.freqVec_apply in Breakdown.Uniqueness.RegLocalAuxSymm, line 108. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L108).

**Conjugation as a real isometry.** Vector conjugation is packaged as a real linear isometry. Source: Breakdown.SmoothFlow.conjVecIso in Breakdown.Uniqueness.RegLocalAuxSymm, line 110. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L110).

**Convolution respects conjugate symmetry.** Almost-everywhere conjugate-reflection identities for both factors imply the corresponding exact identity for their convolution. Source: Breakdown.SmoothFlow.convC_neg in Breakdown.Uniqueness.RegLocalAuxSymm, line 115. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L115).

**Conjugate symmetry of self-advection.** An almost-everywhere conjugate-symmetric symbol has an exactly conjugate-symmetric diagonal advection symbol. Source: Breakdown.SmoothFlow.advectionBilin_neg in Breakdown.Uniqueness.RegLocalAuxSymm, line 128. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L128).

**Conjugate reflection of the projection.** Projecting a conjugated vector at negative frequency gives the conjugate of its projection at positive frequency. Source: Breakdown.SmoothFlow.divFreeC_neg_conj in Breakdown.Uniqueness.RegLocalAuxSymm, line 140. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L140).

**Conjugate symmetry of the nonlinearity.** An almost-everywhere conjugate-symmetric symbol has an exactly conjugate-symmetric nonlinear symbol. Source: Breakdown.SmoothFlow.nonlinSymbol_neg in Breakdown.Uniqueness.RegLocalAuxSymm, line 147. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L147).

**Frequency inner product.** The inner product with the frequency vector equals the sum of its coordinate products. Source: Breakdown.SmoothFlow.inner_freqVec in Breakdown.Uniqueness.RegLocalAuxSymm, line 151. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L151).

**Duhamel map preserves solenoidality.** Solenoidal initial data and the stated almost-everywhere conjugate symmetry of the input curve give a solenoidal output of the Duhamel map. Source: Breakdown.SmoothFlow.varConstMap_solenoidal in Breakdown.Uniqueness.RegLocalAuxSymm, line 155. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegLocalAuxSymm.lean#L155).

### Breakdown.Uniqueness.RegPersist

This file bootstraps local regular solutions to all required Sobolev orders while retaining the prescribed initial regularity.

Reading context: §5 and Appendix A.2; persistence and smoothing of regular solutions.

**Source namespace:** Breakdown.SmoothFlow.

**Sobolev sum energy estimate.** For measurable inputs, the Sobolev energy of a sum is at most twice the sum of the separate energies. Source: Breakdown.SmoothFlow.hsNormSq_add_le_two in Breakdown.Uniqueness.RegPersist, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersist.lean#L12).

**Sobolev difference energy estimate.** For measurable inputs, the Sobolev energy of a difference is at most twice the sum of the separate energies. Source: Breakdown.SmoothFlow.hsNormSq_sub_le_two in Breakdown.Uniqueness.RegPersist, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersist.lean#L18).

**A two-term bound gives a zero limit.** A nonnegative quantity bounded eventually by twice each of two quantities tending to zero also tends to zero. Source: Breakdown.SmoothFlow.tendsto_zero_of_le_two in Breakdown.Uniqueness.RegPersist, line 24. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersist.lean#L24).

**Half-order persistence bounds.** An H3 solenoidal Duhamel flow with Hm initial data satisfies uniform fractional-norm bounds at the stated half-order increments up to `m`. Source: Breakdown.SmoothFlow.persist_bound in Breakdown.Uniqueness.RegPersist, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersist.lean#L33).

**Persistence of initial regularity.** An H3 solenoidal Duhamel flow remains an Hm curve for every `m ≥ 3` for which its initial Hm energy is finite. Source: Breakdown.SmoothFlow.isHsCurve_of_persist in Breakdown.Uniqueness.RegPersist, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersist.lean#L79).

### Breakdown.Uniqueness.RegPersistAux

This file supplies heat-flow continuity and fractional Sobolev estimates for the regularity bootstrap.

Reading context: §5 and Appendix A.2; auxiliary smoothing estimates.

**Source namespace:** Breakdown.SmoothFlow.

**Measurable fractional Sobolev weight.** The nonnegative-real fractional Sobolev weight is measurable for every real order. Source: Breakdown.SmoothFlow.measurable_ofReal_weight in Breakdown.Uniqueness.RegPersistAux, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L12).

**Square of a nonnegative sum.** The square of the sum of two nonnegative extended reals is at most twice the sum of their squares. Source: Breakdown.SmoothFlow.enn_sq_add_le in Breakdown.Uniqueness.RegPersistAux, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L16).

**Heat contraction after the start.** For `t ≥ a`, the extended norm of the complex heat multiplier at elapsed time `t-a` is at most one. Source: Breakdown.SmoothFlow.heat_enorm_le_one in Breakdown.Uniqueness.RegPersistAux, line 28. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L28).

**Measurable linear heat evolution.** Heat evolution of an almost-everywhere strongly measurable symbol remains almost-everywhere strongly measurable. Source: Breakdown.SmoothFlow.aestronglyMeasurable_heatPart in Breakdown.Uniqueness.RegPersistAux, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L35).

**Integer fractional norms agree with Hm.** At a nonnegative integer order, the fractional squared norm equals the ordinary squared Sobolev norm. Source: Breakdown.SmoothFlow.fracNormSq_natCast in Breakdown.Uniqueness.RegPersistAux, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L42).

**Monotone fractional Sobolev norms.** The squared fractional Sobolev norm increases with its real order. Source: Breakdown.SmoothFlow.fracNormSq_mono in Breakdown.Uniqueness.RegPersistAux, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L46).

**Fractional energy of a sum.** For measurable symbols, the fractional energy of a sum is at most twice the sum of the separate energies. Source: Breakdown.SmoothFlow.fracNormSq_add_le in Breakdown.Uniqueness.RegPersistAux, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L54).

**Fractional energy under negation.** Negating a symbol leaves its fractional Sobolev energy unchanged. Source: Breakdown.SmoothFlow.fracNormSq_neg in Breakdown.Uniqueness.RegPersistAux, line 75. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L75).

**Fractional energy of a difference.** For measurable symbols, the fractional energy of a difference is at most twice the sum of the separate energies. Source: Breakdown.SmoothFlow.fracNormSq_sub_le in Breakdown.Uniqueness.RegPersistAux, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L79).

**Heat contracts fractional energy.** At nonnegative elapsed time, heat evolution does not increase any fractional Sobolev energy. Source: Breakdown.SmoothFlow.fracNormSq_heatPart_le in Breakdown.Uniqueness.RegPersistAux, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L85).

**Sobolev sum bound.** The Sobolev energy of two measurable symbols' sum is at most twice the sum of their energies. Source: Breakdown.SmoothFlow.hsNormSq_add_le' in Breakdown.Uniqueness.RegPersistAux, line 94. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L94).

**Real energy bound on a closed interval.** A Sobolev curve has a common real bound on its Sobolev energy throughout the closed interval. Source: Breakdown.SmoothFlow.hsNormSq_bdd_of_curve in Breakdown.Uniqueness.RegPersistAux, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L100).

**Sobolev continuity of heat evolution.** For finite-Hm initial data, heat evolution is continuous in Hm distance within the stated closed time interval. Source: Breakdown.SmoothFlow.tendsto_hsNormSq_heatPart in Breakdown.Uniqueness.RegPersistAux, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L125).

**Splitting low and high frequency weights.** For the stated orders and positive base bounds, the lower power is controlled by a low-frequency term and a higher-power remainder. Source: Breakdown.SmoothFlow.weight_split in Breakdown.Uniqueness.RegPersistAux, line 166. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L166).

**Higher norms improve continuity.** A uniform fractional bound above integer order `m`, together with H3 continuity, gives Hm continuity on the interval. Source: Breakdown.SmoothFlow.tendsto_hsNormSq_of_frac in Breakdown.Uniqueness.RegPersistAux, line 182. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAux.lean#L182).

### Breakdown.Uniqueness.RegPersistAuxDefs

This file defines the fractional Sobolev norm and the elapsed-time heat contribution used in the persistence induction.

Reading context: §5 and Appendix A.2; the fractional Sobolev bootstrap framework.

**Source namespace:** Breakdown.SmoothFlow.

**Fractional Sobolev energy.** The fractional squared norm integrates `(1+‖ξ‖²)^r` times squared symbol norm. Source: Breakdown.SmoothFlow.fracNormSq in Breakdown.Uniqueness.RegPersistAuxDefs, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxDefs.lean#L12).

**Linear heat part.** The heat part multiplies the initial symbol by the heat multiplier at elapsed time `t-a`. Source: Breakdown.SmoothFlow.heatPart in Breakdown.Uniqueness.RegPersistAuxDefs, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxDefs.lean#L15).

### Breakdown.Uniqueness.RegPersistAuxGain

This file proves the half-order regularity gain for the nonlinear Duhamel remainder.

Reading context: §5 and Appendix A.2; the gain step in Sobolev persistence.

**Source namespace:** Breakdown.SmoothFlow.

**Cauchy-Schwarz for lower integrals.** For measurable nonnegative factors, the square of their product integral is at most the product of their square integrals. Source: Breakdown.SmoothFlow.lintegral_mul_sq_le_of_aemeasurable in Breakdown.Uniqueness.RegPersistAuxGain, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxGain.lean#L16).

**Integrated three-quarter singularity.** For ordered endpoints, the lower integral of `(t-s)^(-3/4)` is bounded by `4(t-a)^(1/4)`. Source: Breakdown.SmoothFlow.lintegral_Ioo_sub_rpow_le in Breakdown.Uniqueness.RegPersistAuxGain, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxGain.lean#L29).

**A half-order nonlinear gain.** A uniform fractional order-`r` bound on the stated flow gives a uniform order-`r+1/2` bound after subtracting its linear heat part. Source: Breakdown.SmoothFlow.fracNormSq_varConst_gain in Breakdown.Uniqueness.RegPersistAuxGain, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxGain.lean#L55).

### Breakdown.Uniqueness.RegPersistAuxHeat

This file proves the Sobolev smoothing and continuity of the heat contribution to a regular solution.

Reading context: §5 and Appendix A.2; the linear part of the persistence bootstrap.

**Source namespace:** Breakdown.SmoothFlow.

**Polynomial times exponential decay.** For nonnegative `v`, the quantity `v^n exp(-v)` is at most `n!`. Source: Breakdown.SmoothFlow.pow_mul_exp_neg_le in Breakdown.Uniqueness.RegPersistAuxHeat, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxHeat.lean#L12).

**Scalar heat-gain estimate.** For `0 < τ ≤ T` and `x ≥ 0`, the stated heat-weight expression times `τ³` is bounded by `2|T|+7`. Source: Breakdown.SmoothFlow.heat_gain_base in Breakdown.Uniqueness.RegPersistAuxHeat, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxHeat.lean#L20).

**Heat gain with a half derivative.** On `0 < τ ≤ T`, the squared heat multiplier times `‖ξ‖²(1+‖ξ‖²)^(1/2)` is bounded by `Cτ^(-3/2)`. Source: Breakdown.SmoothFlow.heatSymbol_gain_le in Breakdown.Uniqueness.RegPersistAuxHeat, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxHeat.lean#L44).

### Breakdown.Uniqueness.RegPersistAuxMeas

This file establishes measurable representatives and continuity facts for the L2 and convolution expressions in the regularity bootstrap.

Reading context: §5 and Appendix A.2; measurable nonlinear terms in persistence.

**Source namespace:** Breakdown.SmoothFlow.

**Continuous complex coordinate projection.** Each coordinate projection on complex vector space is continuous. Source: Breakdown.SmoothFlow.continuous_coordC in Breakdown.Uniqueness.RegPersistAuxMeas, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L12).

**Continuous real coordinate projection.** Each coordinate projection on physical space is continuous. Source: Breakdown.SmoothFlow.continuous_coordR in Breakdown.Uniqueness.RegPersistAuxMeas, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L15).

**Measurability of Leray projection.** The divergence-free projection is measurable jointly in frequency and vector input. Source: Breakdown.SmoothFlow.measurable_divFreeC in Breakdown.Uniqueness.RegPersistAuxMeas, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L18).

**Convolution preserves null-set equality.** Changing either input on a null set leaves the complex convolution unchanged at every frequency. Source: Breakdown.SmoothFlow.convC_congr_ae in Breakdown.Uniqueness.RegPersistAuxMeas, line 30. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L30).

**Null-set equality of nonlinear symbols.** Almost-everywhere equal inputs have equal nonlinear-symbol functions. Source: Breakdown.SmoothFlow.nonlinSymbol_eq_of_ae in Breakdown.Uniqueness.RegPersistAuxMeas, line 40. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L40).

**Measurability of complex convolution.** Strongly measurable complex inputs have measurable convolution. Source: Breakdown.SmoothFlow.measurable_convC in Breakdown.Uniqueness.RegPersistAuxMeas, line 52. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L52).

**Measurability of the nonlinear symbol.** An almost-everywhere strongly measurable symbol has measurable nonlinear symbol. Source: Breakdown.SmoothFlow.measurable_nonlinSymbol in Breakdown.Uniqueness.RegPersistAuxMeas, line 58. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L58).

**L2 membership from a finite square norm.** A measurable complex function with finite squared-norm lower integral belongs to L2. Source: Breakdown.SmoothFlow.memLp_two_of_lintegral in Breakdown.Uniqueness.RegPersistAuxMeas, line 74. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L74).

**Complex L2 integral formula.** The complex L2 norm is the square root of the squared-norm lower integral. Source: Breakdown.SmoothFlow.eLpNorm_two_eq in Breakdown.Uniqueness.RegPersistAuxMeas, line 81. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L81).

**Complex L2 conversion or zero.** The complex L2 conversion takes the input's L2 class when it exists and uses zero otherwise. Source: Breakdown.SmoothFlow.toL2C in Breakdown.Uniqueness.RegPersistAuxMeas, line 87. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L87).

**Complex L2 conversion on valid inputs.** For an L2 function, the total conversion equals its ordinary Lp class. Source: Breakdown.SmoothFlow.toL2C_eq in Breakdown.Uniqueness.RegPersistAuxMeas, line 90. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L90).

**Convergence of L2 representatives.** Convergence of the squared L2 difference to zero gives convergence of the converted L2 elements. Source: Breakdown.SmoothFlow.tendsto_toL2C in Breakdown.Uniqueness.RegPersistAuxMeas, line 94. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L94).

**Convergence of product integrals in L2.** When both factors converge in L2 under the stated interval conditions, their complex product integrals converge. Source: Breakdown.SmoothFlow.tendsto_integral_mul in Breakdown.Uniqueness.RegPersistAuxMeas, line 110. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L110).

**Sobolev weights dominate one.** Every Sobolev frequency weight is at least one. Source: Breakdown.SmoothFlow.one_le_hsWeight in Breakdown.Uniqueness.RegPersistAuxMeas, line 135. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L135).

**Extended square norm as a real value.** The squared extended norm equals the nonnegative-real conversion of the squared ordinary norm. Source: Breakdown.SmoothFlow.enorm_sq_eq in Breakdown.Uniqueness.RegPersistAuxMeas, line 138. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L138).

**Coordinate square integral below H3.** The squared integral of any coordinate is bounded by the full H3 energy. Source: Breakdown.SmoothFlow.lintegral_coord_le in Breakdown.Uniqueness.RegPersistAuxMeas, line 142. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L142).

**Derivative-coordinate energy below H3.** The squared integral of a Fourier coordinate derivative is bounded by `4π²` times H3 energy. Source: Breakdown.SmoothFlow.lintegral_grad_le in Breakdown.Uniqueness.RegPersistAuxMeas, line 153. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L153).

**Convolution continuity on an interval.** Along an H3 curve, each advection component convolution is continuous within the time interval at every allowed time. Source: Breakdown.SmoothFlow.continuousWithinAt_convC in Breakdown.Uniqueness.RegPersistAuxMeas, line 182. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L182).

**Time continuity of the H3 nonlinearity.** At fixed frequency, the nonlinear symbol of an H3 curve is continuous on its closed interval. Source: Breakdown.SmoothFlow.continuousOn_nonlinSymbol in Breakdown.Uniqueness.RegPersistAuxMeas, line 223. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L223).

**Measurable nonlinear norm in spacetime.** The extended nonlinear-symbol norm of the stated solenoidal H3 curve is jointly measurable on the time-frequency product. Source: Breakdown.SmoothFlow.aemeasurable_enorm_nonlinSymbol in Breakdown.Uniqueness.RegPersistAuxMeas, line 237. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxMeas.lean#L237).

### Breakdown.Uniqueness.RegPersistAuxNonlin

This file bounds the nonlinear symbol by scalar self-convolutions and weighted Sobolev densities.

Reading context: §5 and Appendix A.2; nonlinear control in the persistence step.

**Source namespace:** Breakdown.SmoothFlow.

**Vector norm below coordinate sum.** The complex vector norm is at most the sum of its coordinate norms. Source: Breakdown.SmoothFlow.norm_le_sum_comp in Breakdown.Uniqueness.RegPersistAuxNonlin, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L12).

**Vector norm below the coordinate sum.** The extended complex vector norm is at most the sum of the coordinate extended norms. Source: Breakdown.SmoothFlow.enorm_le_sum_comp in Breakdown.Uniqueness.RegPersistAuxNonlin, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L18).

**Frequency contraction bound.** The frequency-coordinate contraction has norm at most `3‖ξ‖‖z‖`. Source: Breakdown.SmoothFlow.norm_sum_coord_mul_le in Breakdown.Uniqueness.RegPersistAuxNonlin, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L23).

**Coarse frequency-vector bound.** The complex frequency vector has norm at most three times the real frequency norm. Source: Breakdown.SmoothFlow.norm_freqVec_le in Breakdown.Uniqueness.RegPersistAuxNonlin, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L33).

**Coarse projection bound.** The divergence-free projection is bounded by ten times its input norm in this estimate. Source: Breakdown.SmoothFlow.norm_divFreeC_le in Breakdown.Uniqueness.RegPersistAuxNonlin, line 42. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L42).

**Extended coarse projection bound.** The extended norm of the divergence-free projection is at most ten times the input extended norm. Source: Breakdown.SmoothFlow.enorm_divFreeC_le in Breakdown.Uniqueness.RegPersistAuxNonlin, line 63. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L63).

**Integer Sobolev order comparison.** The squared Sobolev norm at any lower integer order is bounded by the higher-order norm. Source: Breakdown.SmoothFlow.hsNormSq_mono_nat in Breakdown.Uniqueness.RegPersistAuxNonlin, line 71. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L71).

**Self-convolution bounds nonlinearity.** For a measurable solenoidal H3 symbol, its nonlinear norm is bounded by `C‖ξ‖` times the self-convolution of its norm. Source: Breakdown.SmoothFlow.enorm_nonlinSymbol_le in Breakdown.Uniqueness.RegPersistAuxNonlin, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxNonlin.lean#L78).

### Breakdown.Uniqueness.RegPersistAuxProductBound

This file proves the weighted convolution product estimates used to gain fractional Sobolev regularity.

Reading context: §5 and Appendix A.2; product estimates for smoothing.

**Source namespace:** Breakdown.SmoothFlow.

**Half power of a square.** Taking the half power of a nonnegative extended real's square returns the original number. Source: Breakdown.SmoothFlow.ennreal_sq_rpow_half in Breakdown.Uniqueness.RegPersistAuxProductBound, line 12. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L12).

**Square cancels a half power.** The square of a nonnegative extended real's half power is the original number. Source: Breakdown.SmoothFlow.ennreal_rpow_half_sq in Breakdown.Uniqueness.RegPersistAuxProductBound, line 16. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L16).

**Pointwise squared convolution bound.** The square of a nonnegative convolution is bounded by a convolution with one factor squared times the other factor's total mass. Source: Breakdown.SmoothFlow.conv_sq_le_pointwise in Breakdown.Uniqueness.RegPersistAuxProductBound, line 20. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L20).

**Measurability of a convolution kernel.** The product of measurable input and shifted factors is measurable on the product frequency space. Source: Breakdown.SmoothFlow.aemeasurable_conv_kernel in Breakdown.Uniqueness.RegPersistAuxProductBound, line 39. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L39).

**Mass of a nonnegative convolution.** The total lower integral of a measurable nonnegative convolution equals the product of the two input masses. Source: Breakdown.SmoothFlow.lintegral_conv_right in Breakdown.Uniqueness.RegPersistAuxProductBound, line 44. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L44).

**Weighted self-convolution estimate.** A weight obeying the stated splitting inequality gives the displayed weighted-L2 self-convolution bound with constant `4K²`. Source: Breakdown.SmoothFlow.weighted_conv_base in Breakdown.Uniqueness.RegPersistAuxProductBound, line 56. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L56).

**Fractional weight under addition.** For nonnegative real order, the output Sobolev weight is bounded by `4^r` times the sum of the input weights. Source: Breakdown.SmoothFlow.weight_rpow_le in Breakdown.Uniqueness.RegPersistAuxProductBound, line 112. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L112).

**Square-root fractional weight splitting.** The square root of the output weight is bounded by the stated `4^(r/2)` multiple of the two input square-root weights. Source: Breakdown.SmoothFlow.weight_root_le in Breakdown.Uniqueness.RegPersistAuxProductBound, line 132. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L132).

**Fractional weighted convolution bound.** For nonnegative fractional order, the weighted squared self-convolution is bounded by a constant times fractional Sobolev energy and squared Fourier L1 norm. Source: Breakdown.SmoothFlow.lintegral_weight_conv_sq_le in Breakdown.Uniqueness.RegPersistAuxProductBound, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPersistAuxProductBound.lean#L154).

### Breakdown.Uniqueness.RegPhysAux

This file constructs the physical velocity, pressure and time derivative from regular frequency curves and proves their weighted integrability.

Reading context: §5 and Appendix A.2; reconstruction of a physical regular solution.

**Source namespace:** Breakdown.SmoothFlow.

**Frequency complexification is isometric.** The complex frequency vector has the same norm as the real frequency. Source: Breakdown.SmoothFlow.norm_freqVec_eq in Breakdown.Uniqueness.RegPhysAux, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L14).

**Shifting polynomial L1 weights.** Multiplying an order-`k+j` weighted L1 symbol by `(1+‖ξ‖)^j` gives an order-`k` weighted L1 symbol. Source: Breakdown.SmoothFlow.memLp_weight_shift in Breakdown.Uniqueness.RegPhysAux, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L18).

**First complex coordinate vector.** The selected vector is one in the first complex coordinate and zero in the others. Source: Breakdown.SmoothFlow.singleVec in Breakdown.Uniqueness.RegPhysAux, line 31. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L31).

**Inverse transform of a scalar embedding.** Embedding a scalar symbol in the first coordinate commutes with inverse Fourier transformation. Source: Breakdown.SmoothFlow.freqTrInv_smul_single in Breakdown.Uniqueness.RegPhysAux, line 33. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L33).

**Recovering the embedded scalar.** The first coordinate of `z` times the selected unit vector is `z`. Source: Breakdown.SmoothFlow.single_apply_zero in Breakdown.Uniqueness.RegPhysAux, line 39. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L39).

**Measurability of the embedded scalar.** Measurability of the scalar embedded in the first complex coordinate implies measurability of the scalar itself. Source: Breakdown.SmoothFlow.aesm_of_single in Breakdown.Uniqueness.RegPhysAux, line 42. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L42).

**Real part of the first coordinate.** This continuous linear functional extracts the real part of the first complex coordinate. Source: Breakdown.SmoothFlow.firstRe in Breakdown.Uniqueness.RegPhysAux, line 48. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L48).

**Scalar reconstruction by evaluation.** The physical scalar equals the first-coordinate real part of the inverse transform of its vector embedding. Source: Breakdown.SmoothFlow.physScalar_eq in Breakdown.Uniqueness.RegPhysAux, line 51. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L51).

**Two names for the pressure embedding.** Using the selected unit vector gives the same embedded pressure symbol as the explicit first-coordinate vector. Source: Breakdown.SmoothFlow.pressure_single_eq in Breakdown.Uniqueness.RegPhysAux, line 56. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L56).

**Smooth physical velocity in spacetime.** The stated all-orders solenoidal Duhamel curve reconstructs a velocity smooth on the entire closed time slab. Source: Breakdown.SmoothFlow.smooth_physField_curve in Breakdown.Uniqueness.RegPhysAux, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L64).

**Smooth reconstructed pressure.** The stated all-orders solenoidal Duhamel curve reconstructs pressure smooth on the entire closed time slab. Source: Breakdown.SmoothFlow.smooth_pressure_curve in Breakdown.Uniqueness.RegPhysAux, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L71).

**Weighted L1 Laplacian symbol.** The Laplacian symbol belongs to weighted L1 of order `k` when the input has order `k+2`. Source: Breakdown.SmoothFlow.memLp_sspSymbol in Breakdown.Uniqueness.RegPhysAux, line 83. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L83).

**Weighted integrability of pressure.** For the stated regular solenoidal curve, the pressure symbol embedded in one coordinate belongs to every weighted L1 space at each allowed time. Source: Breakdown.SmoothFlow.memLp_pressure_single_curve in Breakdown.Uniqueness.RegPhysAux, line 100. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L100).

**Isometric scalar coordinate embedding.** Multiplying the selected unit vector by a complex scalar preserves that scalar's norm. Source: Breakdown.SmoothFlow.norm_smul_singleVec in Breakdown.Uniqueness.RegPhysAux, line 105. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L105).

**Weighted pressure-gradient bounds.** The pressure-gradient symbol and the pressure times frequency vector belong to every weighted L1 space along the stated curve. Source: Breakdown.SmoothFlow.memLp_gradPressure_curve in Breakdown.Uniqueness.RegPhysAux, line 109. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L109).

**Integrable pressure symbol.** The pressure symbol of each allowed slice of the stated regular solenoidal curve is integrable. Source: Breakdown.SmoothFlow.integrable_pressure_curve in Breakdown.Uniqueness.RegPhysAux, line 133. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L133).

**Weighted time-derivative integrability.** The time-derivative symbol of each allowed regular solenoidal slice belongs to every weighted L1 space. Source: Breakdown.SmoothFlow.memLp_timeDeriv_curve in Breakdown.Uniqueness.RegPhysAux, line 141. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L141).

**Physical time derivative from its symbol.** At interior times, differentiating the reconstructed velocity gives the physical field of the time-derivative symbol. Source: Breakdown.SmoothFlow.hasDerivAt_physField_curve in Breakdown.Uniqueness.RegPhysAux, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L154).

**Integrable symbols for the PDE.** Along the stated regular solenoidal curve, the time derivative, advection, Laplacian and pressure-gradient symbols are all integrable. Source: Breakdown.SmoothFlow.integrable_symbols_curve in Breakdown.Uniqueness.RegPhysAux, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L163).

**Advection identity for each time slice.** The advection of each reconstructed regular solenoidal slice equals the inverse-transform physical advection symbol. Source: Breakdown.SmoothFlow.advectionAt_physField_curve in Breakdown.Uniqueness.RegPhysAux, line 173. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L173).

**Laplacian identity for each time slice.** The Laplacian of each reconstructed regular slice equals the physical field of its Laplacian symbol. Source: Breakdown.SmoothFlow.sumSecondPartialsAt_physField_curve in Breakdown.Uniqueness.RegPhysAux, line 178. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L178).

**Pressure-gradient identity for the curve.** The gradient of the reconstructed pressure equals the physical field of its gradient symbol at each allowed time. Source: Breakdown.SmoothFlow.gradientAt_pressure_curve in Breakdown.Uniqueness.RegPhysAux, line 183. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L183).

**Divergence-free reconstructed velocity.** Every allowed slice of the stated solenoidal regular curve reconstructs a velocity with zero divergence. Source: Breakdown.SmoothFlow.divergenceAt_physField_curve in Breakdown.Uniqueness.RegPhysAux, line 190. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAux.lean#L190).

### Breakdown.Uniqueness.RegPhysAuxBasic

This file verifies the algebraic identities connecting reconstructed fields with the frequency Navier-Stokes equation.

Reading context: §5 and Appendix A.2; the reconstructed physical equation.

**Source namespace:** Breakdown.SmoothFlow.

**Laplacian symbol.** The Laplacian symbol multiplies the vector symbol by `-4π²‖ξ‖²`. Source: Breakdown.SmoothFlow.sspSymbol in Breakdown.Uniqueness.RegPhysAuxBasic, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L12).

**Pressure-gradient symbol.** The pressure-gradient symbol is `2πi` times the pressure symbol times the frequency vector. Source: Breakdown.SmoothFlow.gradPressureSymbol in Breakdown.Uniqueness.RegPhysAuxBasic, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L15).

**The frequency Navier-Stokes identity.** The time-derivative symbol plus advection equals the Laplacian symbol minus the pressure-gradient symbol. Source: Breakdown.SmoothFlow.timeDerivSymbol_add_advectionSymbol in Breakdown.Uniqueness.RegPhysAuxBasic, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L18).

**Integrable character-modulated symbol.** Multiplication by a Fourier character preserves integrability of a vector symbol. Source: Breakdown.SmoothFlow.integrable_char_smul in Breakdown.Uniqueness.RegPhysAuxBasic, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L38).

**Reconstruction respects addition.** The physical inverse transform distributes over addition of integrable vector symbols. Source: Breakdown.SmoothFlow.physField_add in Breakdown.Uniqueness.RegPhysAuxBasic, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L45).

**Reconstruction respects subtraction.** The physical inverse transform distributes over subtraction of integrable vector symbols. Source: Breakdown.SmoothFlow.physField_sub in Breakdown.Uniqueness.RegPhysAuxBasic, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L50).

**Measurable polynomial L1 density.** The polynomial frequency density is almost-everywhere measurable. Source: Breakdown.SmoothFlow.aemeasurable_weight in Breakdown.Uniqueness.RegPhysAuxBasic, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L55).

**Volume follows weighted-L1 null sets.** Ordinary volume is absolutely continuous with respect to the weighted L1 measure. Source: Breakdown.SmoothFlow.volume_ac_weight in Breakdown.Uniqueness.RegPhysAuxBasic, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L59).

**Weighted-L1 measure follows volume.** The weighted L1 measure is absolutely continuous with respect to ordinary volume. Source: Breakdown.SmoothFlow.weight_ac_volume in Breakdown.Uniqueness.RegPhysAuxBasic, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L64).

**Lower integral for weighted L1.** Integration against the weighted L1 measure inserts the polynomial frequency weight into the ordinary lower integral. Source: Breakdown.SmoothFlow.lintegral_weight in Breakdown.Uniqueness.RegPhysAuxBasic, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L67).

**Weighted L1 finiteness criterion.** For a measurable symbol, weighted L1 membership is equivalent to finiteness of its weighted norm integral. Source: Breakdown.SmoothFlow.memLp_weight_iff in Breakdown.Uniqueness.RegPhysAuxBasic, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L72).

**Weighted L1 from all Sobolev orders.** Every allowed slice of an all-orders Sobolev curve belongs to every polynomially weighted L1 space. Source: Breakdown.SmoothFlow.memLp_weight_of_curve in Breakdown.Uniqueness.RegPhysAuxBasic, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L77).

**Weighted L1 gives integrability.** A symbol belonging to a polynomially weighted L1 space is integrable against ordinary volume. Source: Breakdown.SmoothFlow.integrable_of_memLp_weight in Breakdown.Uniqueness.RegPhysAuxBasic, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxBasic.lean#L85).

### Breakdown.Uniqueness.RegPhysAuxDeriv

This file differentiates inverse Fourier integrals and identifies physical spatial derivatives with frequency multipliers.

Reading context: §5 and Appendix A.2; spatial regularity of reconstructed fields.

**Source namespace:** Breakdown.SmoothFlow.Internal.

**Integrable weighted vector symbol.** A weighted L1 symbol multiplied by its polynomial weight is integrable against ordinary volume. Source: Breakdown.SmoothFlow.Internal.integrable_weight_smul in Breakdown.Uniqueness.RegPhysAuxDeriv, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L14).

**Ordinary measurability from weighted L1.** Membership in weighted L1 implies almost-everywhere strong measurability for ordinary volume. Source: Breakdown.SmoothFlow.Internal.aestronglyMeasurable_of_weight in Breakdown.Uniqueness.RegPhysAuxDeriv, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L24).

**Moments below the available weight.** Weighted L1 of order `k` makes every frequency-norm moment of order at most `k` integrable. Source: Breakdown.SmoothFlow.Internal.integrable_pow_mul_of_weight in Breakdown.Uniqueness.RegPhysAuxDeriv, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L33).

**Ordinary integrability from a weight.** Membership in polynomially weighted L1 implies ordinary integrability. Source: Breakdown.SmoothFlow.Internal.integrable_of_weight in Breakdown.Uniqueness.RegPhysAuxDeriv, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L44).

**Sign convention for the Fourier pairing.** The bilinear map underlying the negative inner-product operator is the negative real inner-product bilinear map. Source: Breakdown.SmoothFlow.Internal.toLinearMap₁₂_neg_innerSL in Breakdown.Uniqueness.RegPhysAuxDeriv, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L50).

**Inverse transform as a vector integral.** The inverse Fourier transform is the vector Fourier integral using the negative inner-product pairing. Source: Breakdown.SmoothFlow.Internal.freqTrInv_eq_integral in Breakdown.Uniqueness.RegPhysAuxDeriv, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L55).

**Directional Fourier derivative factor.** The inverse-transform directional multiplier is `2πi⟨v,h⟩` times the input symbol. Source: Breakdown.SmoothFlow.Internal.freqTrSMulRight_apply_eq in Breakdown.Uniqueness.RegPhysAuxDeriv, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L62).

**Integrable derivative operator integrand.** An integrable symbol with an integrable first frequency moment has an integrable linear-map-valued Fourier derivative integrand. Source: Breakdown.SmoothFlow.Internal.integrable_freqTrSMulRight in Breakdown.Uniqueness.RegPhysAuxDeriv, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L73).

**Integrable directional multiplier.** An integrable symbol with integrable first frequency moment remains integrable after a fixed directional Fourier multiplier. Source: Breakdown.SmoothFlow.Internal.integrable_symbol_smul in Breakdown.Uniqueness.RegPhysAuxDeriv, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L81).

**Derivative of the inverse transform.** The inverse transform of a symbol with integrable first moment has derivative given by the Fourier integral of its derivative multiplier. Source: Breakdown.SmoothFlow.Internal.hasFDerivAt_freqTrInv in Breakdown.Uniqueness.RegPhysAuxDeriv, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L89).

**Evaluating the Fourier derivative.** Evaluating the derivative Fourier integral on a direction equals inverse transformation after multiplication by `2πi⟨ξ,h⟩`. Source: Breakdown.SmoothFlow.Internal.freqTrIntegral_smulRight_apply in Breakdown.Uniqueness.RegPhysAuxDeriv, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L101).

**Integrability after a Fourier phase.** Multiplying an integrable symbol by the inverse-transform Fourier character preserves integrability. Source: Breakdown.SmoothFlow.Internal.integrable_freqTr_integrand in Breakdown.Uniqueness.RegPhysAuxDeriv, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L114).

**Inverse transform by coordinates.** For integrable vector symbols, taking a coordinate commutes with inverse Fourier transformation. Source: Breakdown.SmoothFlow.Internal.freqTrInv_coord in Breakdown.Uniqueness.RegPhysAuxDeriv, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L122).

**Coordinate from a unit-vector pairing.** Inner product with a coordinate unit vector returns that coordinate. Source: Breakdown.SmoothFlow.Internal.inner_unitVector in Breakdown.Uniqueness.RegPhysAuxDeriv, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L130).

**Sum of squared coordinate pairings.** The sum of the squared inner products with coordinate unit vectors equals the squared vector norm. Source: Breakdown.SmoothFlow.Internal.sum_inner_unitVector_sq in Breakdown.Uniqueness.RegPhysAuxDeriv, line 133. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L133).

**Coordinates of a unit-vector sum.** The `j`th coordinate of a sum of unit-vector multiples is its `j`th coefficient. Source: Breakdown.SmoothFlow.Internal.sum_smul_unitVector_apply in Breakdown.Uniqueness.RegPhysAuxDeriv, line 141. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L141).

**Frequency complexification is isometric.** The complex frequency vector has the same norm as the real frequency. Source: Breakdown.SmoothFlow.Internal.norm_freqVec in Breakdown.Uniqueness.RegPhysAuxDeriv, line 145. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L145).

**Source namespace:** Breakdown.SmoothFlow.

**Directional inverse-transform derivative.** Weighted L1 of order one gives differentiability of the inverse transform and the directional multiplier formula. Source: Breakdown.SmoothFlow.fderiv_freqTrInv_apply in Breakdown.Uniqueness.RegPhysAuxDeriv, line 151. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L151).

**A physical directional derivative.** For weighted L1 order one, a directional physical derivative is reconstructed from the symbol multiplied by `2πi⟨ξ,h⟩`. Source: Breakdown.SmoothFlow.fderiv_physField_apply in Breakdown.Uniqueness.RegPhysAuxDeriv, line 160. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L160).

**Physical Laplacian from two moments.** Weighted L1 of order two makes the physical Laplacian equal to reconstruction of the Laplacian symbol. Source: Breakdown.SmoothFlow.sumSecondPartialsAt_physField in Breakdown.Uniqueness.RegPhysAuxDeriv, line 170. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L170).

**Physical gradient from a scalar symbol.** For integrable scalar data with integrable frequency-vector product, the physical gradient is reconstructed from `2πi g(ξ)ξ`. Source: Breakdown.SmoothFlow.gradientAt_physScalar in Breakdown.Uniqueness.RegPhysAuxDeriv, line 228. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L228).

**Solenoidal symbol gives zero divergence.** A weighted-L1 order-one symbol with zero frequency contraction reconstructs a divergence-free physical field. Source: Breakdown.SmoothFlow.divergenceAt_physField in Breakdown.Uniqueness.RegPhysAuxDeriv, line 259. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxDeriv.lean#L259).

### Breakdown.Uniqueness.RegPhysAuxEval

This file justifies evaluation and time differentiation of Banach-valued inverse Fourier curves.

Reading context: §5 and Appendix A.2; time derivatives of physical reconstruction.

**Source namespace:** Breakdown.SmoothFlow.

**Reciprocal evaluation weight.** The evaluation weight is the reciprocal of `(1+‖ξ‖)^k`. Source: Breakdown.SmoothFlow.evalWeight in Breakdown.Uniqueness.RegPhysAuxEval, line 12. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L12).

**Positive reciprocal weight.** The reciprocal evaluation weight is strictly positive at every frequency. Source: Breakdown.SmoothFlow.evalWeight_pos in Breakdown.Uniqueness.RegPhysAuxEval, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L14).

**Reciprocal weight bounded by one.** The reciprocal evaluation weight is at most one. Source: Breakdown.SmoothFlow.evalWeight_le_one in Breakdown.Uniqueness.RegPhysAuxEval, line 17. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L17).

**Continuous reciprocal weight.** The reciprocal evaluation weight is continuous in frequency. Source: Breakdown.SmoothFlow.continuous_evalWeight in Breakdown.Uniqueness.RegPhysAuxEval, line 21. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L21).

**Evaluation integrand norm bound.** The reciprocal weight times the Fourier character does not increase the pointwise input norm. Source: Breakdown.SmoothFlow.evalIntegrand_norm_le in Breakdown.Uniqueness.RegPhysAuxEval, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L26).

**Integrable weighted evaluation integrand.** The evaluation integrand of a weighted L1 element is integrable against its weighted measure. Source: Breakdown.SmoothFlow.evalIntegrand_integrable in Breakdown.Uniqueness.RegPhysAuxEval, line 31. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L31).

**Linear weighted evaluation map.** Weighted evaluation integrates the Fourier character times the reciprocal weight against the weighted-L1 representative. Source: Breakdown.SmoothFlow.evalLin in Breakdown.Uniqueness.RegPhysAuxEval, line 42. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L42).

**Continuous weighted evaluation map.** The weighted evaluation map is made into a continuous linear map using its norm bound by one. Source: Breakdown.SmoothFlow.evalCLM in Breakdown.Uniqueness.RegPhysAuxEval, line 56. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L56).

**Integral formula for weighted evaluation.** The continuous weighted evaluation map equals the displayed reciprocal-weight Fourier integral. Source: Breakdown.SmoothFlow.evalCLM_apply in Breakdown.Uniqueness.RegPhysAuxEval, line 62. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L62).

**Weighted evaluation recovers inversion.** Evaluating a valid weighted L1 representative gives the ordinary inverse Fourier transform at the selected point. Source: Breakdown.SmoothFlow.evalCLM_toWeightL1 in Breakdown.Uniqueness.RegPhysAuxEval, line 66. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L66).

**Derivative of an inverse-transform curve.** A derivative in weighted L1 yields the corresponding pointwise time derivative after inverse Fourier transformation at an interior time. Source: Breakdown.SmoothFlow.hasDerivAt_freqTrInv_curve in Breakdown.Uniqueness.RegPhysAuxEval, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxEval.lean#L85).

### Breakdown.Uniqueness.RegPhysAuxPressure

This file identifies the regular pressure symbol and its gradient with the bilinear pressure construction.

Reading context: §5 and Appendix A.2; the pressure part of physical reconstruction.

**Source namespace:** Breakdown.SmoothFlow.

**Weighted pressure-symbol embedding.** For a solenoidal symbol with all weighted L1 moments, its pressure embedded in one coordinate belongs to every weighted L1 space. Source: Breakdown.SmoothFlow.memLp_pressureSymbol_single in Breakdown.Uniqueness.RegPhysAuxPressure, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressure.lean#L14).

**Smooth weighted-L1 pressure curve.** The embedded pressure of the stated all-orders solenoidal Duhamel curve is smooth to every finite time order in each weighted L1 space. Source: Breakdown.SmoothFlow.contDiffOn_toWeightL1_pressureSingle in Breakdown.Uniqueness.RegPhysAuxPressure, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressure.lean#L24).

### Breakdown.Uniqueness.RegPhysAuxPressurePart1

This file defines and estimates the pressure bilinear kernel, including weighted-measure and representative identities.

Reading context: §5 and Appendix A.2; construction of the frequency pressure operator.

**Source namespace:** Breakdown.SmoothFlow.

**Frequency dot product.** The frequency dot product sums the complex-cast frequency coordinates times the vector coordinates. Source: Breakdown.SmoothFlow.freqDot in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L12).

**Pressure bilinear kernel.** The pressure pairing kernel is the product of two frequency dot products divided by squared frequency norm. Source: Breakdown.SmoothFlow.pressurePairTerm in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L14).

**Bilinear pressure symbol.** The bilinear pressure symbol is the negative integral of the pressure pairing kernel over the two shifted input symbols. Source: Breakdown.SmoothFlow.pressureBilinSymbol in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L17).

**Source namespace:** Breakdown.SmoothFlow.PressureSingle.Internal.

**Additivity of the frequency dot product.** The frequency dot product distributes over vector addition. Source: Breakdown.SmoothFlow.PressureSingle.Internal.freqDot_add in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L22).

**Scaling the frequency dot product.** A real scalar multiplying the vector factors out of the frequency dot product. Source: Breakdown.SmoothFlow.PressureSingle.Internal.freqDot_smul in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L25).

**Pressure kernel adds in its first input.** The pressure pairing kernel distributes over addition in its first vector input. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pairTerm_add_left in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L31).

**Pressure kernel adds in its second input.** The pressure pairing kernel distributes over addition in its second vector input. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pairTerm_add_right in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L36).

**Scaling the first pressure input.** Real scalar multiplication in the first pressure-kernel input factors out of the kernel. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pairTerm_smul_left in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L41).

**Scaling the second pressure input.** Real scalar multiplication in the second pressure-kernel input factors out of the kernel. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pairTerm_smul_right in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L46).

**Continuous pressure pairing kernel.** At fixed frequency, the pressure pairing kernel is continuous jointly in its two vector inputs. Source: Breakdown.SmoothFlow.PressureSingle.Internal.continuous_pairTerm in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L51).

**Frequency dot-product norm estimate.** The frequency dot-product norm is bounded by `3‖ξ‖‖z‖`. Source: Breakdown.SmoothFlow.PressureSingle.Internal.norm_freqDot_le in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L56).

**Pressure kernel norm estimate.** The pressure pairing kernel is bounded by nine times the product of the two vector norms. Source: Breakdown.SmoothFlow.PressureSingle.Internal.norm_pairTerm_le in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L65).

**Extended pressure kernel estimate.** The extended pressure pairing norm is bounded by nine times the product of the two extended vector norms. Source: Breakdown.SmoothFlow.PressureSingle.Internal.enorm_pairTerm_le in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L83).

**Pressure bounded by norm convolution.** The bilinear pressure-symbol norm is bounded by nine times the convolution of the two input norms. Source: Breakdown.SmoothFlow.PressureSingle.Internal.enorm_pressureBilinSymbol_le in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L90).

**Measurable nonnegative convolution.** The lower-integral convolution of two measurable nonnegative functions is measurable. Source: Breakdown.SmoothFlow.PressureSingle.Internal.measurable_conv in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L98).

**Mass of a measurable convolution.** The total lower integral of a measurable nonnegative convolution is the product of its input masses. Source: Breakdown.SmoothFlow.PressureSingle.Internal.lintegral_conv_measurable in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L103).

**Convolving measurable representatives.** Replacing almost-everywhere measurable nonnegative factors by their measurable representatives leaves each convolution value unchanged. Source: Breakdown.SmoothFlow.PressureSingle.Internal.conv_congr_mk in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L115).

**Measurable convolution from ae data.** The lower-integral convolution of almost-everywhere measurable nonnegative functions is measurable. Source: Breakdown.SmoothFlow.PressureSingle.Internal.aemeasurable_conv in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 123. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L123).

**Convolution mass from ae data.** The lower integral of a nonnegative convolution with almost-everywhere measurable inputs equals the product of their masses. Source: Breakdown.SmoothFlow.PressureSingle.Internal.lintegral_conv in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L130).

**Multiplicative polynomial weight bound.** The output polynomial weight is bounded by the product of the weights at the two input frequencies. Source: Breakdown.SmoothFlow.PressureSingle.Internal.weight_le_mul in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 136. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L136).

**Measurable pressure-analysis weight.** The polynomial frequency weight is measurable. Source: Breakdown.SmoothFlow.PressureSingle.Internal.measurable_weight in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 145. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L145).

**Weighted L1 convolution bound.** The weighted total mass of a nonnegative convolution is at most the product of the two weighted masses. Source: Breakdown.SmoothFlow.PressureSingle.Internal.lintegral_weight_conv_le in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L148).

**Volume follows weighted null sets.** Volume is absolutely continuous with respect to polynomially weighted volume. Source: Breakdown.SmoothFlow.PressureSingle.Internal.volume_ac in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 163. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L163).

**Weighted volume follows null sets.** Polynomially weighted volume is absolutely continuous with respect to volume. Source: Breakdown.SmoothFlow.PressureSingle.Internal.weighted_ac in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 167. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L167).

**The weighted integral density formula.** The weighted lower integral equals the ordinary lower integral with polynomial density inserted. Source: Breakdown.SmoothFlow.PressureSingle.Internal.lintegral_weighted in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 170. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L170).

**Polynomial density is at least one.** The nonnegative-real polynomial frequency density is at least one. Source: Breakdown.SmoothFlow.PressureSingle.Internal.one_le_weight in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 174. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L174).

**Measurability from weighted L1.** Weighted L1 membership gives almost-everywhere strong measurability against ordinary volume. Source: Breakdown.SmoothFlow.PressureSingle.Internal.aesm_of_memLp in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 178. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L178).

**Weighted L1 norm formula.** For a measurable symbol, the weighted L1 norm equals the lower integral of its polynomially weighted norm. Source: Breakdown.SmoothFlow.PressureSingle.Internal.eLpNorm_eq in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 182. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L182).

**Finite weighted norm integral.** Weighted L1 membership makes the weighted pointwise-norm lower integral finite. Source: Breakdown.SmoothFlow.PressureSingle.Internal.lintegral_enorm_lt_top in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 186. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L186).

**Finite unweighted norm integral.** Weighted L1 membership also makes the unweighted pointwise-norm lower integral finite. Source: Breakdown.SmoothFlow.PressureSingle.Internal.lintegral_enorm_lt_top' in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 191. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L191).

**Measurability of shifted vector symbols.** Shifted reflection of an almost-everywhere strongly measurable vector symbol preserves that measurability. Source: Breakdown.SmoothFlow.PressureSingle.Internal.aesm_shift in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 197. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L197).

**Integrability of the pressure kernel.** A finite convolution of input norms ensures integrability of the corresponding pressure pairing integrand. Source: Breakdown.SmoothFlow.PressureSingle.Internal.integrable_pairTerm in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L201).

**Finite convolution almost everywhere.** Two weighted L1 symbols have finite norm convolution at almost every output frequency. Source: Breakdown.SmoothFlow.PressureSingle.Internal.ae_conv_lt_top in Breakdown.Uniqueness.RegPhysAuxPressurePart1, line 212. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart1.lean#L212).

### Breakdown.Uniqueness.RegPhysAuxPressurePart2

This file proves weighted integrability and continuity bounds for the bilinear pressure symbol.

Reading context: §5 and Appendix A.2; analytic estimates for reconstructed pressure.

**Source namespace:** Breakdown.SmoothFlow.PressureSingle.Internal.

**Pressure ignores null-set input changes.** Almost-everywhere changes to either input leave every bilinear pressure-symbol value unchanged. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pressureBilin_congr in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L14).

**Pressure adds in its first symbol.** Under the stated pointwise integrability assumptions, the bilinear pressure symbol distributes over addition in the first input. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pressureBilin_add_left in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L24).

**Pressure adds in its second symbol.** Under the stated pointwise integrability assumptions, the bilinear pressure symbol distributes over addition in the second input. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pressureBilin_add_right in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L32).

**Pressure scales in its first symbol.** Real scaling of the first symbol scales the bilinear pressure by the same scalar. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pressureBilin_smul_left in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L40).

**Pressure scales in its second symbol.** Real scaling of the second symbol scales the bilinear pressure by the same scalar. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pressureBilin_smul_right in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L47).

**Measurability of frequency dot products.** The frequency dot product of the stated measurable frequency and vector maps is measurable. Source: Breakdown.SmoothFlow.PressureSingle.Internal.measurable_freqDot in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L54).

**Joint measurability of pressure products.** For measurable input symbols, the shifted pressure pairing integrand is measurable on the product frequency space. Source: Breakdown.SmoothFlow.PressureSingle.Internal.measurable_pairTerm_prod in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L61).

**Measurable bilinear pressure symbol.** Bilinear pressure formed from almost-everywhere strongly measurable inputs is almost-everywhere strongly measurable. Source: Breakdown.SmoothFlow.PressureSingle.Internal.aesm_pressureBilin in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L72).

**Norm of the selected complex unit vector.** The selected first-coordinate complex unit vector has extended norm one. Source: Breakdown.SmoothFlow.PressureSingle.Internal.enorm_single_one in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 81. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L81).

**Weighted L1 pressure bound.** The pressure symbol embedded in one coordinate has weighted L1 norm at most nine times the product of the two weighted L1 input norms. Source: Breakdown.SmoothFlow.PressureSingle.Internal.eLpNorm_pressureSingle_le in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L85).

**Pressure stays in weighted L1.** The embedded bilinear pressure of two weighted L1 symbols belongs to the same weighted L1 space. Source: Breakdown.SmoothFlow.PressureSingle.Internal.memLp_pressureSingle in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L108).

**Source namespace:** Breakdown.SmoothFlow.

**Continuous bilinear pressure operator.** A continuous bilinear map on each weighted L1 space realizes the embedded bilinear pressure symbol on admissible inputs. Source: Breakdown.SmoothFlow.exists_bilin_pressureSingle in Breakdown.Uniqueness.RegPhysAuxPressurePart2, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart2.lean#L119).

### Breakdown.Uniqueness.RegPhysAuxPressurePart3

This file justifies the pressure-gradient convolution formula and its integrable representatives.

Reading context: §5 and Appendix A.2; differentiation of the pressure symbol.

**Source namespace:** Breakdown.SmoothFlow.PressureSingle.Internal.

**Advection-product norm bound.** An advection component product is bounded by `2π` times the two vector norms and the derivative frequency norm. Source: Breakdown.SmoothFlow.PressureSingle.Internal.norm_advTerm_le in Breakdown.Uniqueness.RegPhysAuxPressurePart3, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart3.lean#L14).

**Integrability of an advection component.** Finiteness of the derivative-weighted norm convolution makes the stated advection component integrable. Source: Breakdown.SmoothFlow.PressureSingle.Internal.integrable_advTerm' in Breakdown.Uniqueness.RegPhysAuxPressurePart3, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart3.lean#L25).

**Derivative convolution is finite a.e..** An order-one weighted L1 symbol has finite derivative-weighted norm self-convolution almost everywhere. Source: Breakdown.SmoothFlow.PressureSingle.Internal.ae_advTerm_lt_top in Breakdown.Uniqueness.RegPhysAuxPressurePart3, line 46. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart3.lean#L46).

**Two pressure-symbol formulas agree.** For a solenoidal order-one weighted L1 symbol, the pressure obtained from advection equals the bilinear pressure formula almost everywhere. Source: Breakdown.SmoothFlow.PressureSingle.Internal.pressureSymbol_ae_eq in Breakdown.Uniqueness.RegPhysAuxPressurePart3, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxPressurePart3.lean#L61).

### Breakdown.Uniqueness.RegPhysAuxProduct

This file identifies reconstructed products and advection with their physical-space counterparts.

Reading context: §5 and Appendix A.2; the physical nonlinear term.

**Source namespace:** Breakdown.SmoothFlow.

**All weighted moments for advection.** A symbol in every polynomially weighted L1 space has its advection symbol in every such space. Source: Breakdown.SmoothFlow.memLp_advectionSymbol in Breakdown.Uniqueness.RegPhysAuxProduct, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProduct.lean#L13).

**Reconstruction gives physical advection.** For a solenoidal symbol with all weighted L1 moments, physical advection equals reconstruction of the advection symbol at every point. Source: Breakdown.SmoothFlow.advectionAt_physField in Breakdown.Uniqueness.RegPhysAuxProduct, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProduct.lean#L17).

### Breakdown.Uniqueness.RegPhysAuxProductPart1

This file proves weighted convolution bounds and the coordinate identities for quadratic advection.

Reading context: §5 and Appendix A.2; integrability of physical products.

**Source namespace:** Breakdown.SmoothFlow.Internal.ConvProduct.

**Extended polynomial frequency weight.** The weight is the nonnegative-real version of `(1+‖ξ‖)^k`. Source: Breakdown.SmoothFlow.Internal.ConvProduct.wt in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 14. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L14).

**Polynomially weighted frequency measure.** The polynomial-weight measure multiplies volume by the extended polynomial frequency weight. Source: Breakdown.SmoothFlow.Internal.ConvProduct.polyWeight in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 16. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L16).

**Measurable polynomial weight.** The extended polynomial frequency weight is measurable. Source: Breakdown.SmoothFlow.Internal.ConvProduct.measurable_wt in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L18).

**Product bound for polynomial weights.** The weight at an output frequency is bounded by the product of the weights at the two input frequencies. Source: Breakdown.SmoothFlow.Internal.ConvProduct.wt_le in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L21).

**Weighted volume dominates volume.** Polynomially weighted volume is at least ordinary volume as a measure. Source: Breakdown.SmoothFlow.Internal.ConvProduct.volume_le_polyWeight in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L31).

**Weighted L1 by a norm integral.** Membership in polynomially weighted L1 is equivalent to ordinary measurability and a finite weighted norm integral. Source: Breakdown.SmoothFlow.Internal.ConvProduct.memLp_polyWeight_iff in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 38. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L38).

**Weighted L1 implies integrability.** An element of polynomially weighted L1 is integrable against ordinary volume. Source: Breakdown.SmoothFlow.Internal.ConvProduct.integrable_of_memLp_polyWeight in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L54).

**Coordinates preserve weighted L1.** Each coordinate of a vector symbol in weighted L1 belongs to the corresponding scalar weighted L1 space. Source: Breakdown.SmoothFlow.Internal.ConvProduct.memLp_polyWeight_apply in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L58).

**Differentiation costs one L1 weight.** Multiplication by a coordinate Fourier derivative maps weighted L1 of order `k+1` into weighted L1 of order `k`. Source: Breakdown.SmoothFlow.Internal.ConvProduct.memLp_freq_smul in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L62).

**Explicit and library convolution agree.** The explicit complex convolution is the library convolution using complex multiplication. Source: Breakdown.SmoothFlow.Internal.ConvProduct.convC_eq_convolution in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L96).

**Complex convolution ignores null sets.** Almost-everywhere replacement of either input leaves the explicit complex convolution unchanged. Source: Breakdown.SmoothFlow.Internal.ConvProduct.convC_congr_ae' in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L101).

**A weighted convolution estimate.** The weighted L1 convolution integral is at most the product of the two weighted L1 input integrals. Source: Breakdown.SmoothFlow.Internal.ConvProduct.lintegral_convC_le in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L110).

**Weighted L1 is closed under convolution.** The convolution of two scalar symbols in the same polynomially weighted L1 space remains in that space. Source: Breakdown.SmoothFlow.Internal.ConvProduct.memLp_convC in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L146).

**Coordinates of quadratic advection.** Each coordinate of the advection symbol is the sum of convolutions with the corresponding coordinate Fourier derivative. Source: Breakdown.SmoothFlow.Internal.ConvProduct.advectionSymbol_apply in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 169. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L169).

**Weighted L1 advection closure.** If a symbol belongs to every polynomially weighted L1 space, its advection symbol belongs to each chosen weighted L1 space. Source: Breakdown.SmoothFlow.Internal.ConvProduct.memLp_advectionSymbol_aux in Breakdown.Uniqueness.RegPhysAuxProductPart1, line 174. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart1.lean#L174).

### Breakdown.Uniqueness.RegPhysAuxProductPart2

This file applies the convolution theorem to identify inverse Fourier products and directional advection.

Reading context: §5 and Appendix A.2; conversion of convolution to physical multiplication.

**Source namespace:** Breakdown.SmoothFlow.Internal.ConvProduct.

**Integrability after phase modulation.** Multiplication by a unit-modulus Fourier phase preserves integrability for a complex normed-space-valued symbol. Source: Breakdown.SmoothFlow.Internal.ConvProduct.integrable_char_smul in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L14).

**Integral form of the inverse transform.** The inverse Fourier transform is the integral of the symbol multiplied by the positive Fourier phase. Source: Breakdown.SmoothFlow.Internal.ConvProduct.freqTrInv_eq_integral in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L23).

**Inverse transform componentwise.** A coordinate of the inverse transform of an integrable vector symbol equals the inverse transform of that coordinate. Source: Breakdown.SmoothFlow.Internal.ConvProduct.freqTrInv_apply_eq in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 28. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L28).

**Inverse transform of a finite sum.** Inverse Fourier transformation distributes over a three-term sum of integrable symbols. Source: Breakdown.SmoothFlow.Internal.ConvProduct.freqTrInv_sum in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L34).

**Inverse transform of a scalar multiple.** A constant complex scalar factors out of inverse Fourier transformation. Source: Breakdown.SmoothFlow.Internal.ConvProduct.freqTrInv_const_smul in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 40. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L40).

**Convolution becomes multiplication.** For integrable complex symbols, the inverse transform of their convolution is the product of their inverse transforms. Source: Breakdown.SmoothFlow.Internal.ConvProduct.freqTrInv_convC in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L48).

**Conjugate-symmetric scalar inversion.** A conjugate-symmetric scalar symbol has an inverse transform fixed by conjugation. Source: Breakdown.SmoothFlow.Internal.ConvProduct.freqTrInv_conj_symm in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L54).

**Advection as a directional derivative.** For the stated regular solenoidal symbol, the multiplier in the physical-velocity direction reconstructs the same field as the advection symbol. Source: Breakdown.SmoothFlow.Internal.ConvProduct.physField_freqInner_eq in Breakdown.Uniqueness.RegPhysAuxProductPart2, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxProductPart2.lean#L71).

### Breakdown.Uniqueness.RegPhysAuxSmooth

This file proves joint smoothness of reconstructed physical fields from weighted frequency integrability and smooth time curves.

Reading context: §5 and Appendix A.2; smoothness of the physical regular solution.

**Source namespace:** Breakdown.SmoothFlow.Internal.

**Polynomially bounded amplitude.** This proposition requires a measurable complex amplitude bounded by a constant times `(1+‖ξ‖)^k`. Source: Breakdown.SmoothFlow.Internal.WeightBounded in Breakdown.Uniqueness.RegPhysAuxSmooth, line 14. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L14).

**Monotonicity of polynomial weights.** The polynomial frequency weight increases with its integer exponent. Source: Breakdown.SmoothFlow.Internal.weight_mono in Breakdown.Uniqueness.RegPhysAuxSmooth, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L17).

**A valid amplitude bound is nonnegative.** Any constant bounding a complex amplitude by a positive polynomial weight must be nonnegative. Source: Breakdown.SmoothFlow.Internal.nonneg_of_bound in Breakdown.Uniqueness.RegPhysAuxSmooth, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L20).

**Source namespace:** Breakdown.SmoothFlow.Internal.WeightBounded.

**Relaxing the amplitude weight.** An amplitude bounded at order `ℓ` is also bounded at every order `k ≥ ℓ`. Source: Breakdown.SmoothFlow.Internal.WeightBounded.mono in Breakdown.Uniqueness.RegPhysAuxSmooth, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L26).

**Source namespace:** Breakdown.SmoothFlow.Internal.

**Volume follows weighted null sets.** Volume is absolutely continuous with respect to the polynomially weighted L1 measure. Source: Breakdown.SmoothFlow.Internal.volume_ac_weight in Breakdown.Uniqueness.RegPhysAuxSmooth, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L32).

**Weighted norm lower-integral formula.** The lower integral of a symbol norm for weighted L1 equals its ordinary lower integral with the polynomial weight inserted. Source: Breakdown.SmoothFlow.Internal.lintegral_weight in Breakdown.Uniqueness.RegPhysAuxSmooth, line 39. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L39).

**Bounded amplitude evaluation.** An amplitude bounded by `C` times the order-`k` weight defines an integrable pairing with weighted L1 data and bounds its integral norm by `C‖g‖`. Source: Breakdown.SmoothFlow.Internal.integrable_and_norm_le in Breakdown.Uniqueness.RegPhysAuxSmooth, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L45).

**Inverse Fourier phase.** The inverse Fourier phase is `exp(2πi⟨ξ,x⟩)`. Source: Breakdown.SmoothFlow.Internal.phase in Breakdown.Uniqueness.RegPhysAuxSmooth, line 75. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L75).

**Unit modulus of the Fourier phase.** The inverse Fourier phase has norm one. Source: Breakdown.SmoothFlow.Internal.norm_phase in Breakdown.Uniqueness.RegPhysAuxSmooth, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L77).

**Continuous Fourier phase.** For a fixed spatial point, the inverse Fourier phase is continuous in frequency. Source: Breakdown.SmoothFlow.Internal.continuous_phase in Breakdown.Uniqueness.RegPhysAuxSmooth, line 79. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L79).

**Spatial addition splits the phase.** The phase at `x+h` is the product of the phases at `x` and `h`. Source: Breakdown.SmoothFlow.Internal.phase_add in Breakdown.Uniqueness.RegPhysAuxSmooth, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L83).

**Measurable modulated amplitude.** Multiplying a polynomially bounded measurable amplitude by the Fourier phase gives an almost-everywhere strongly measurable function. Source: Breakdown.SmoothFlow.Internal.amp_meas in Breakdown.Uniqueness.RegPhysAuxSmooth, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L90).

**Phase preserves the amplitude bound.** Multiplying by the unit Fourier phase preserves the same polynomial amplitude bound. Source: Breakdown.SmoothFlow.Internal.amp_bound in Breakdown.Uniqueness.RegPhysAuxSmooth, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L94).

**Integrable amplitude evaluation.** A polynomially bounded amplitude times the Fourier phase can be integrated against weighted L1 data. Source: Breakdown.SmoothFlow.Internal.amp_integrable in Breakdown.Uniqueness.RegPhysAuxSmooth, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L100).

**Amplitude evaluation operator.** The amplitude operator is the continuous linear map integrating phase-modulated amplitude against the weighted L1 input. Source: Breakdown.SmoothFlow.Internal.ampOp in Breakdown.Uniqueness.RegPhysAuxSmooth, line 105. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L105).

**The amplitude operator integral.** The amplitude evaluation operator equals its defining phase-modulated integral. Source: Breakdown.SmoothFlow.Internal.ampOp_apply in Breakdown.Uniqueness.RegPhysAuxSmooth, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L122).

**Directional amplitude multiplier.** The directional amplitude multiplies the original amplitude by `2πi⟨ξ,h⟩`. Source: Breakdown.SmoothFlow.Internal.ampDir in Breakdown.Uniqueness.RegPhysAuxSmooth, line 126. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L126).

**One additional weight for a derivative.** A directional Fourier derivative raises the polynomial amplitude bound by one order. Source: Breakdown.SmoothFlow.Internal.ampDir_bound in Breakdown.Uniqueness.RegPhysAuxSmooth, line 129. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L129).

**Amplitude derivative operator.** The amplitude derivative operator sends a spatial direction to the amplitude operator with its directional multiplier. Source: Breakdown.SmoothFlow.Internal.ampDeriv in Breakdown.Uniqueness.RegPhysAuxSmooth, line 146. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L146).

**Evaluating the amplitude derivative.** Applying the amplitude derivative to a direction gives the amplitude operator for that directional multiplier. Source: Breakdown.SmoothFlow.Internal.ampDeriv_apply in Breakdown.Uniqueness.RegPhysAuxSmooth, line 173. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L173).

**Quadratic remainder for a complex phase.** For real `θ`, the norm of `exp(iθ)-1-iθ` is at most `θ²`. Source: Breakdown.SmoothFlow.Internal.norm_cexp_sub_le in Breakdown.Uniqueness.RegPhysAuxSmooth, line 176. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L176).

**Differentiating the amplitude operator.** With two spare polynomial weights beyond the amplitude order, the amplitude operator has the stated spatial derivative. Source: Breakdown.SmoothFlow.Internal.hasFDerivAt_ampOp in Breakdown.Uniqueness.RegPhysAuxSmooth, line 204. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L204).

**Smoothness with spare frequency moments.** An amplitude operator is C^m when the available polynomial weight exceeds its amplitude order by at least `m+2`. Source: Breakdown.SmoothFlow.Internal.contDiff_ampOp in Breakdown.Uniqueness.RegPhysAuxSmooth, line 271. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L271).

**Source namespace:** Breakdown.SmoothFlow.

**Smoothness from weighted time curves.** A curve smooth in every weighted L1 space reconstructs an inverse Fourier transform smooth on the closed spacetime slab. Source: Breakdown.SmoothFlow.contDiffOn_freqTrInv_curve in Breakdown.Uniqueness.RegPhysAuxSmooth, line 296. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegPhysAuxSmooth.lean#L296).

### Breakdown.Uniqueness.RegToolkit

This file collects Sobolev embedding and tame estimates used by both local existence and continuation.

Reading context: §5 and Appendix A.2; the regularity estimate toolkit.

**Source namespace:** Breakdown.SmoothFlow.

**An L2 reciprocal Sobolev weight.** The square of the polynomial-to-Sobolev weight ratio is bounded by `2^k(1+‖ξ‖²)⁻²`. Source: Breakdown.SmoothFlow.weight_ratio_sq_le in Breakdown.Uniqueness.RegToolkit, line 14. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L14).

**Integrability of the comparison weight.** The comparison density `2^k(1+‖ξ‖²)⁻²` is integrable in three dimensions. Source: Breakdown.SmoothFlow.weight_integrable in Breakdown.Uniqueness.RegToolkit, line 33. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L33).

**L2 from a finite square integral.** A measurable complex function with finite squared-norm lower integral belongs to L2. Source: Breakdown.SmoothFlow.memLp_two_of_lintegral_sq in Breakdown.Uniqueness.RegToolkit, line 39. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L39).

**Coordinate energy density below H1.** A component's squared norm is bounded by the full H1 energy density. Source: Breakdown.SmoothFlow.component_sq_le_weight in Breakdown.Uniqueness.RegToolkit, line 45. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L45).

**Frequency-coordinate density below H1.** The squared norm of a frequency coordinate times the matching symbol coordinate is bounded by H1 energy density. Source: Breakdown.SmoothFlow.coord_component_sq_le_weight in Breakdown.Uniqueness.RegToolkit, line 55. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L55).

**L2 coordinates from H1 energy.** A measurable symbol with finite H1 energy has each coordinate in L2. Source: Breakdown.SmoothFlow.memLp_component in Breakdown.Uniqueness.RegToolkit, line 70. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L70).

**L2 frequency-coordinate components.** Finite H1 energy gives L2 membership for frequency-coordinate multiples of the corresponding symbol components. Source: Breakdown.SmoothFlow.memLp_coord_component in Breakdown.Uniqueness.RegToolkit, line 77. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L77).

**Weighted Fourier L1 from Sobolev energy.** The order-`k` weighted Fourier L1 integral is bounded by a constant times the H^(k+2) norm. Source: Breakdown.SmoothFlow.weightedFreqL1_le in Breakdown.Uniqueness.RegToolkit, line 85. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L85).

**Fourier L1 from H2.** The Fourier L1 norm is bounded by a constant times the H2 norm. Source: Breakdown.SmoothFlow.freqL1Norm_le_hsNormSq in Breakdown.Uniqueness.RegToolkit, line 144. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L144).

**Fourier L1 interpolation estimate.** The Fourier L1 norm is bounded by a constant times the quarter powers of the first and second homogeneous energies. Source: Breakdown.SmoothFlow.freqL1Norm_le_supBound in Breakdown.Uniqueness.RegToolkit, line 150. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L150).

**Tame Sobolev advection estimate.** The Hm energy of bilinear advection is bounded by a constant times the stated combination of Fourier L1, H^(m+1), Hm and first-frequency-moment norms. Source: Breakdown.SmoothFlow.hsNormSq_advectionBilin_le in Breakdown.Uniqueness.RegToolkit, line 154. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L154).

**Advection symbol in divergence form.** For the stated integrable solenoidal symbol, advection equals `2πi` times output-frequency contraction of the coordinate self-convolutions. Source: Breakdown.SmoothFlow.advectionSymbol_eq_div in Breakdown.Uniqueness.RegToolkit, line 160. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkit.lean#L160).

### Breakdown.Uniqueness.RegToolkitAuxSupBound

This file bounds frequency integrals and supremum norms by the appropriate Sobolev norms.

Reading context: §5 and Appendix A.2; Sobolev-to-uniform bounds.

**Source namespace:** Breakdown.SmoothFlow.

**Weight for the Fourier L1 interpolation.** The auxiliary weight is `1/(‖ξ‖²(1+‖ξ‖²))`. Source: Breakdown.SmoothFlow.supWeight in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 12. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L12).

**Finite interpolation-weight integral.** The nonnegative lower integral of the auxiliary interpolation weight is finite. Source: Breakdown.SmoothFlow.supWeight_lintegral_lt_top in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 14. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L14).

**Scaling the interpolation weight.** Rescaling the auxiliary rational weight yields the displayed factors `1/(dc⁴)` and `c³` for positive `c` and `d`. Source: Breakdown.SmoothFlow.supBound_scale in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 26. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L26).

**Scalar inequality for interpolation.** The stated positive parameters bound `2s` by the first two weighted square terms and a reciprocal-weight remainder. Source: Breakdown.SmoothFlow.supBound_real in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 54. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L54).

**Almost every frequency is nonzero.** The zero frequency is excluded on a set of full volume measure. Source: Breakdown.SmoothFlow.supBound_ae_ne in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 67. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L67).

**Two-parameter Fourier L1 estimate.** For positive parameters `c` and `d`, the Fourier L1 norm is controlled by the first two homogeneous energies and the auxiliary weight integral. Source: Breakdown.SmoothFlow.supBound_param in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 71. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L71).

**Zero homogeneous norm kills Fourier L1.** If any homogeneous squared norm is zero, then the Fourier L1 norm is zero. Source: Breakdown.SmoothFlow.supBound_zero in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 122. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L122).

**Optimised Fourier L1 interpolation.** The Fourier L1 norm is bounded by a constant times the quarter powers of the first and second homogeneous energies. Source: Breakdown.SmoothFlow.freqL1_le_supBound in Breakdown.Uniqueness.RegToolkitAuxSupBound, line 141. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxSupBound.lean#L141).

### Breakdown.Uniqueness.RegToolkitAuxTame

This file proves the tame nonlinear Sobolev estimates, tracking the low-order factor separately from the high-order factor.

Reading context: §5 and Appendix A.2; high-order control for continuation.

**Source namespace:** Breakdown.SmoothFlow.

**Squared convolution by Cauchy-Schwarz.** The squared nonnegative convolution is bounded by one factor's mass times a convolution with the other factor squared. Source: Breakdown.SmoothFlow.lintegral_mul_sq_le in Breakdown.Uniqueness.RegToolkitAuxTame, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L12).

**L2-L1 convolution inequality.** The squared L2 integral of a nonnegative convolution is bounded by the first factor's squared L2 integral times the second factor's squared L1 mass. Source: Breakdown.SmoothFlow.productBound_sq in Breakdown.Uniqueness.RegToolkitAuxTame, line 48. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L48).

**Complex norm from coordinate norms.** The complex vector norm is bounded by the sum of its coordinate norms. Source: Breakdown.SmoothFlow.norm_le_sum_components in Breakdown.Uniqueness.RegToolkitAuxTame, line 64. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L64).

**Extended norm from coordinate norms.** The extended complex vector norm is bounded by the sum of its coordinate extended norms. Source: Breakdown.SmoothFlow.enorm_le_sum_components in Breakdown.Uniqueness.RegToolkitAuxTame, line 70. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L70).

**Gradient norm density.** The gradient density is the nonnegative-real value of `2π‖ξ‖‖g(ξ)‖`. Source: Breakdown.SmoothFlow.gradDensity in Breakdown.Uniqueness.RegToolkitAuxTame, line 75. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L75).

**A density bound for advection.** An advection component's norm is bounded by the first symbol norm times the second symbol's gradient density. Source: Breakdown.SmoothFlow.enorm_term_le in Breakdown.Uniqueness.RegToolkitAuxTame, line 78. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L78).

**Advection controlled by norm convolution.** The bilinear advection norm is bounded by nine times the convolution of the first symbol norm with the second symbol's gradient density. Source: Breakdown.SmoothFlow.enorm_advectionBilin_le in Breakdown.Uniqueness.RegToolkitAuxTame, line 91. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L91).

**Japanese bracket of frequency.** The frequency bracket is `√(1+‖ξ‖²)`. Source: Breakdown.SmoothFlow.bracket in Breakdown.Uniqueness.RegToolkitAuxTame, line 106. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L106).

**Nonnegative frequency bracket.** The frequency bracket is nonnegative. Source: Breakdown.SmoothFlow.bracket_nonneg in Breakdown.Uniqueness.RegToolkitAuxTame, line 108. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L108).

**Square of the frequency bracket.** The square of the frequency bracket is `1+‖ξ‖²`. Source: Breakdown.SmoothFlow.bracket_sq in Breakdown.Uniqueness.RegToolkitAuxTame, line 110. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L110).

**Bracket dominates frequency norm.** The frequency norm is at most its bracket. Source: Breakdown.SmoothFlow.norm_le_bracket in Breakdown.Uniqueness.RegToolkitAuxTame, line 113. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L113).

**Subadditivity of the frequency bracket.** The bracket of a sum is at most the sum of the two brackets. Source: Breakdown.SmoothFlow.bracket_add_le in Breakdown.Uniqueness.RegToolkitAuxTame, line 116. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L116).

**Power of a nonnegative sum.** For nonnegative inputs, the integer power of their sum is bounded by `2^m` times the sum of their powers. Source: Breakdown.SmoothFlow.add_pow_le_two_pow in Breakdown.Uniqueness.RegToolkitAuxTame, line 135. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L135).

**Square-root Sobolev weight.** The auxiliary extended weight is the nonnegative-real value of the frequency bracket to power `m`. Source: Breakdown.SmoothFlow.sigmaW in Breakdown.Uniqueness.RegToolkitAuxTame, line 151. [Private definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L151).

**Splitting the square-root weight.** The output square-root weight is at most `2^m` times the sum of the two input weights. Source: Breakdown.SmoothFlow.sigmaW_le in Breakdown.Uniqueness.RegToolkitAuxTame, line 153. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L153).

**Square-root weight squared.** Squaring the auxiliary weight gives the nonnegative-real Sobolev weight. Source: Breakdown.SmoothFlow.sigmaW_sq in Breakdown.Uniqueness.RegToolkitAuxTame, line 169. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L169).

**Weighted gradient-density bound.** The squared product of the square-root weight and gradient density is bounded by `4π²` times the order-`m+1` Sobolev density. Source: Breakdown.SmoothFlow.sigmaW_grad_sq in Breakdown.Uniqueness.RegToolkitAuxTame, line 173. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L173).

**Integral of the gradient density.** The total gradient density equals `2π` times the first Fourier frequency moment. Source: Breakdown.SmoothFlow.lintegral_gradDensity in Breakdown.Uniqueness.RegToolkitAuxTame, line 192. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L192).

**Measurable norm convolution.** The convolution lower integral of two measurable nonnegative functions is measurable. Source: Breakdown.SmoothFlow.measurable_conv in Breakdown.Uniqueness.RegToolkitAuxTame, line 199. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L199).

**Commutativity of nonnegative convolution.** Exchanging the two factors of a nonnegative convolution leaves its value unchanged. Source: Breakdown.SmoothFlow.conv_comm in Breakdown.Uniqueness.RegToolkitAuxTame, line 204. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L204).

**Fourfold square-sum estimate.** The square of a sum of nonnegative extended reals is at most four times the sum of their squares. Source: Breakdown.SmoothFlow.sq_add_le_four in Breakdown.Uniqueness.RegToolkitAuxTame, line 210. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L210).

**Measurable gradient density.** A measurable vector symbol has measurable gradient density. Source: Breakdown.SmoothFlow.measurable_gradDensity in Breakdown.Uniqueness.RegToolkitAuxTame, line 221. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L221).

**Measurable square-root Sobolev weight.** The auxiliary square-root Sobolev weight is measurable. Source: Breakdown.SmoothFlow.measurable_sigmaW in Breakdown.Uniqueness.RegToolkitAuxTame, line 226. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L226).

**An explicit tame symbol estimate.** For measurable symbols, bilinear advection satisfies the displayed tame bound with constant `324·4^m·4π²`. Source: Breakdown.SmoothFlow.tame_measurable in Breakdown.Uniqueness.RegToolkitAuxTame, line 230. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L230).

**Convolution respects representatives.** Changing either complex input on a null set leaves convolution unchanged. Source: Breakdown.SmoothFlow.convC_congr_ae in Breakdown.Uniqueness.RegToolkitAuxTame, line 304. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L304).

**Advection respects representatives.** Changing either vector symbol on a null set leaves bilinear advection unchanged. Source: Breakdown.SmoothFlow.advectionBilin_congr_ae in Breakdown.Uniqueness.RegToolkitAuxTame, line 313. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L313).

**Sobolev energy respects null sets.** Almost-everywhere equal symbols have equal squared Sobolev norms. Source: Breakdown.SmoothFlow.hsNormSq_congr_ae in Breakdown.Uniqueness.RegToolkitAuxTame, line 325. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L325).

**Fourier L1 norm respects null sets.** Almost-everywhere equal symbols have equal Fourier L1 norms. Source: Breakdown.SmoothFlow.freqL1Norm_congr_ae in Breakdown.Uniqueness.RegToolkitAuxTame, line 331. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L331).

**First moments ignore null-set changes.** Almost-everywhere equal symbols have equal first frequency moments. Source: Breakdown.SmoothFlow.gradFreqL1Norm_congr_ae in Breakdown.Uniqueness.RegToolkitAuxTame, line 337. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L337).

**Tame advection bound for ae data.** The tame Sobolev estimate extends to almost-everywhere strongly measurable symbol inputs. Source: Breakdown.SmoothFlow.hsNormSq_advection_tame_bound in Breakdown.Uniqueness.RegToolkitAuxTame, line 343. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegToolkitAuxTame.lean#L343).

### Breakdown.Uniqueness.RegUnique

This file proves uniqueness of regular Fourier solutions with the same initial data on their common interval.

Reading context: §5 and Appendix A.2; uniqueness inside the regular solution class.

**Source namespace:** Breakdown.SmoothFlow.

**Uniqueness of H3 symbol flows.** Two solenoidal H3 curves satisfying Duhamel's formula with identical initial symbols agree at every time on the closed interval. Source: Breakdown.SmoothFlow.varConst_unique in Breakdown.Uniqueness.RegUnique, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUnique.lean#L12).

### Breakdown.Uniqueness.RegUniqueAux1

This file controls convolution mass and first frequency moments used to estimate the difference of regular solutions.

Reading context: §5 and Appendix A.2; scalar convolution estimates for regular uniqueness.

**Source namespace:** Breakdown.SmoothFlow.

**Derivative-weighted convolution mass.** The convolution mass integrates the first symbol norm against frequency norm times the shifted second symbol norm. Source: Breakdown.SmoothFlow.convMass in Breakdown.Uniqueness.RegUniqueAux1, line 12. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L12).

**Reflecting lower integrals.** Changing the variable from `η` to `ξ-η` preserves the lower integral of a nonnegative function. Source: Breakdown.SmoothFlow.lintegral_sub_left_space in Breakdown.Uniqueness.RegUniqueAux1, line 15. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L15).

**Complex vector norm from its coordinates.** A complex vector's norm is at most the sum of its coordinate norms. Source: Breakdown.SmoothFlow.norm_le_sum_coord in Breakdown.Uniqueness.RegUniqueAux1, line 19. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L19).

**Extended vector norm from coordinates.** A complex vector's extended norm is at most the sum of its coordinate extended norms. Source: Breakdown.SmoothFlow.enorm_le_sum_coord in Breakdown.Uniqueness.RegUniqueAux1, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L26).

**Advection norm from convolution mass.** The bilinear advection norm is bounded by `18π` times the derivative-weighted convolution mass. Source: Breakdown.SmoothFlow.enorm_advectionBilin_le in Breakdown.Uniqueness.RegUniqueAux1, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L32).

**Convolution mass from homogeneous energy.** The convolution mass is bounded by the order-zero Sobolev norm of the first input times the first homogeneous norm of the second. Source: Breakdown.SmoothFlow.convMass_le_hs in Breakdown.Uniqueness.RegUniqueAux1, line 72. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L72).

**Convolution mass with a bounded input.** A finite uniform bound `β` on the first symbol norm bounds convolution mass by `β` times the second symbol's first frequency moment. Source: Breakdown.SmoothFlow.convMass_le_left in Breakdown.Uniqueness.RegUniqueAux1, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L93).

**Convolution mass with bounded derivative.** A finite uniform bound `β` on the second symbol's frequency-weighted norm bounds convolution mass by `β` times the first symbol's Fourier L1 norm. Source: Breakdown.SmoothFlow.convMass_le_right in Breakdown.Uniqueness.RegUniqueAux1, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux1.lean#L103).

### Breakdown.Uniqueness.RegUniqueAux2

This file derives weighted bounds for the nonlinear difference of two regular Fourier symbols.

Reading context: §5 and Appendix A.2; the nonlinear difference estimate.

**Source namespace:** Breakdown.SmoothFlow.

**Projection of a difference.** The difference of two projected vectors equals projection of their difference. Source: Breakdown.SmoothFlow.divFreeC_sub in Breakdown.Uniqueness.RegUniqueAux2, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L12).

**Dot product as a complex inner product.** The frequency-coordinate contraction equals the complex inner product with the frequency vector. Source: Breakdown.SmoothFlow.sum_eq_inner in Breakdown.Uniqueness.RegUniqueAux2, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L16).

**Frequency complexification is isometric.** The complex frequency vector has the same norm as the real frequency. Source: Breakdown.SmoothFlow.norm_freqVec in Breakdown.Uniqueness.RegUniqueAux2, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L20).

**Twofold projection estimate.** This estimate bounds the complex divergence-free projection by twice the input norm. Source: Breakdown.SmoothFlow.norm_divFreeC_le in Breakdown.Uniqueness.RegUniqueAux2, line 23. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L23).

**Integral of a decaying exponential.** For positive decay rate `k`, the exponential integral is `(1-exp(-kh))/k`. Source: Breakdown.SmoothFlow.integral_exp_neg in Breakdown.Uniqueness.RegUniqueAux2, line 40. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L40).

**Heat time integral with one weight.** For ordered times, `(1+‖ξ‖)` times the heat time integral is at most elapsed time plus its square root. Source: Breakdown.SmoothFlow.heatSymbol_integral_le in Breakdown.Uniqueness.RegUniqueAux2, line 48. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L48).

**Nonnegative heat symbol.** The heat symbol is nonnegative at every time and frequency. Source: Breakdown.SmoothFlow.heatSymbol_nonneg in Breakdown.Uniqueness.RegUniqueAux2, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L96).

**Continuous shifted heat symbol.** The heat symbol at `t-s` is continuous as a function of the integration variable `s`. Source: Breakdown.SmoothFlow.continuous_heatSymbol_sub in Breakdown.Uniqueness.RegUniqueAux2, line 98. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L98).

**H3 controls order-zero energy.** The order-zero Sobolev energy is bounded by H3 energy. Source: Breakdown.SmoothFlow.hsNormSq_zero_le_three in Breakdown.Uniqueness.RegUniqueAux2, line 102. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L102).

**H3 controls the first homogeneous energy.** The first homogeneous energy is bounded by H3 energy. Source: Breakdown.SmoothFlow.homNormSq_one_le_three in Breakdown.Uniqueness.RegUniqueAux2, line 108. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L108).

**Weighted integral controls Fourier L1.** The Fourier L1 norm is bounded by the norm integral with weight `1+‖ξ‖`. Source: Breakdown.SmoothFlow.freqL1Norm_le_weighted in Breakdown.Uniqueness.RegUniqueAux2, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L115).

**Weighted control of the first moment.** The first frequency moment is bounded by the norm integral with weight `1+‖ξ‖`. Source: Breakdown.SmoothFlow.gradFreqL1Norm_le_weighted in Breakdown.Uniqueness.RegUniqueAux2, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L122).

**Sobolev energy of a sum.** With the stated measurability, the squared Sobolev norm of a sum is at most twice the sum of the squared norms. Source: Breakdown.SmoothFlow.hsNormSq_add_le_two_mul in Breakdown.Uniqueness.RegUniqueAux2, line 129. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L129).

**Uniform finite bound on Sobolev curves.** A Sobolev curve on a closed interval has one finite bound on its squared norm. Source: Breakdown.SmoothFlow.hsCurve_bound in Breakdown.Uniqueness.RegUniqueAux2, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux2.lean#L148).

### Breakdown.Uniqueness.RegUniqueAux3

This file combines heat-kernel time bounds with the common H3 bound to propagate equality of regular solutions.

Reading context: §5 and Appendix A.2; the short-interval uniqueness argument.

**Source namespace:** Breakdown.SmoothFlow.

**Extended twofold projection estimate.** The extended norm of the complex divergence-free projection is at most twice the input extended norm. Source: Breakdown.SmoothFlow.enorm_divFreeC_le in Breakdown.Uniqueness.RegUniqueAux3, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L13).

**Finite convolution mass for H3 symbols.** Two measurable H3 symbols have finite derivative-weighted convolution mass at every output frequency. Source: Breakdown.SmoothFlow.convMass_lt_top in Breakdown.Uniqueness.RegUniqueAux3, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L19).

**Sobolev energy of a difference.** The squared Sobolev norm of a difference is at most twice the sum of the squared norms under the stated measurability assumption. Source: Breakdown.SmoothFlow.hsNormSq_sub_le in Breakdown.Uniqueness.RegUniqueAux3, line 29. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L29).

**Convolution bounds nonlinear differences.** The nonlinear-symbol difference is bounded by `36π` times the two convolution masses containing the input difference. Source: Breakdown.SmoothFlow.enorm_nonlinSymbol_sub_le in Breakdown.Uniqueness.RegUniqueAux3, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L35).

**Time continuity of the nonlinear symbol.** The nonlinear symbol of an H3 curve is continuous in time at every fixed frequency. Source: Breakdown.SmoothFlow.continuousOn_nonlinSymbol in Breakdown.Uniqueness.RegUniqueAux3, line 67. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L67).

**Duhamel formula for a flow difference.** Two H3 Duhamel curves with identical initial symbols differ by the heat-weighted time integral of their nonlinear-symbol difference. Source: Breakdown.SmoothFlow.varConst_sub_eq in Breakdown.Uniqueness.RegUniqueAux3, line 104. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L104).

**Heat integral after an initial zero.** If the forcing vanishes up to `T` and is bounded by `M` afterward, the weighted heat integral is bounded by `M((t-T)+√(t-T))`. Source: Breakdown.SmoothFlow.heat_varConst_bound in Breakdown.Uniqueness.RegUniqueAux3, line 125. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L125).

**Uniform nonlinear difference estimate.** The stated first-moment, Fourier L1 and weighted-difference bounds imply the pointwise nonlinear difference bound `72πKB`. Source: Breakdown.SmoothFlow.norm_nonlinSymbol_sub_le_of_bound in Breakdown.Uniqueness.RegUniqueAux3, line 165. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L165).

**Nonlinear differences under an H3 bound.** A common finite H3 energy bound yields the displayed frequency-uniform bound on the difference of nonlinear symbols. Source: Breakdown.SmoothFlow.enorm_nonlinSymbol_sub_le_const in Breakdown.Uniqueness.RegUniqueAux3, line 201. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux3.lean#L201).

### Breakdown.Uniqueness.RegUniqueAux4

This file proves the advection subtraction identities and integrability needed in the regular uniqueness estimate.

Reading context: §5 and Appendix A.2; algebra of nonlinear differences.

**Source namespace:** Breakdown.SmoothFlow.

**Bound on an advection integrand.** Each shifted advection component is bounded by `2π` times the first norm, shifted frequency norm and second norm. Source: Breakdown.SmoothFlow.norm_advTerm_le in Breakdown.Uniqueness.RegUniqueAux4, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux4.lean#L12).

**Advection from finite convolution mass.** Finite convolution mass makes each component of the advection integrand integrable. Source: Breakdown.SmoothFlow.integrable_advTerm in Breakdown.Uniqueness.RegUniqueAux4, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux4.lean#L29).

**Subtraction in the first advection input.** At a frequency with the stated finite convolution masses, bilinear advection distributes over subtraction in its first input. Source: Breakdown.SmoothFlow.advectionBilin_sub_left in Breakdown.Uniqueness.RegUniqueAux4, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux4.lean#L53).

**Subtracting the second advection input.** At a frequency with the stated finite convolution masses, bilinear advection distributes over subtraction in its second input. Source: Breakdown.SmoothFlow.advectionBilin_sub_right in Breakdown.Uniqueness.RegUniqueAux4, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/RegUniqueAux4.lean#L64).

### Breakdown.Uniqueness.Restrict

This file restricts global smooth solutions and energy bounds to finite intervals and derives the unit-viscosity blow-up datum from the abstract orbit.

Reading context: §5 and Appendix A.2; normalization of the physical endpoint theorem.

**Source namespace:** Breakdown.

**Restricting a global smooth solution.** A unit-viscosity global smooth solution with solenoidal initial data satisfies the closed-interval solution contract for each terminal time. Source: Breakdown.isSolutionOn_of_isSmoothSolution in Breakdown.Uniqueness.Restrict, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Restrict.lean#L10).

**Global energy bound gives local bounds.** One global energy bound gives energy boundedness on every closed time interval. Source: Breakdown.energyBoundedOn_of_hasBoundedEnergy in Breakdown.Uniqueness.Restrict, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Restrict.lean#L27).

**Source namespace:** Breakdown.MildFramework.

**Closing a smaller mild interval.** A mild solution on the original interval restricts to the closed interval ending at any earlier allowed time. Source: Breakdown.MildFramework.isMildOnIcc_of_isMildOn in Breakdown.Uniqueness.Restrict, line 32. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Restrict.lean#L32).

**Source namespace:** Breakdown.

**Smooth slices of a closed slab.** Smoothness on a closed spacetime slab gives smooth spatial slices at every time in the slab. Source: Breakdown.contDiff_slice_of_contDiffOn in Breakdown.Uniqueness.Restrict, line 38. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Restrict.lean#L38).

**Source namespace:** Breakdown.IsSolutionOn.

**Smooth velocity slices of a solution.** Every allowed spatial velocity slice of a closed-interval solution is smooth. Source: Breakdown.IsSolutionOn.contDiff_velocity in Breakdown.Uniqueness.Restrict, line 45. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Restrict.lean#L45).

**Smooth pressure slices of a solution.** Every allowed spatial pressure slice of a closed-interval solution is smooth. Source: Breakdown.IsSolutionOn.contDiff_pressure in Breakdown.Uniqueness.Restrict, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Restrict.lean#L49).

### Breakdown.Uniqueness.Scaling

This file transports smoothness, the Navier-Stokes equation and energy bounds under the viscosity and spacetime scaling used at the endpoint.

Reading context: §5 and Appendix A.2; scaling the physical contradiction.

**Source namespace:** Breakdown.

**Smooth slices at nonnegative times.** Smoothness on the nonnegative-time spacetime domain gives smooth slices at every nonnegative time. Source: Breakdown.contDiff_slice_of_contDiffOn in Breakdown.Uniqueness.Scaling, line 10. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L10).

**Time differentiability at positive times.** A function smooth on the nonnegative-time spacetime domain is time-differentiable at each positive time and fixed spatial point. Source: Breakdown.differentiableAt_time_of_contDiffOn in Breakdown.Uniqueness.Scaling, line 18. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L18).

**Smoothness after viscosity time scaling.** Positive viscosity time-rescaling and constant amplitude scaling preserve smoothness on the nonnegative-time spacetime domain. Source: Breakdown.contDiffOn_rescale in Breakdown.Uniqueness.Scaling, line 30. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L30).

**Divergence under constant scaling.** For differentiable velocity, multiplying by a constant multiplies its divergence by that constant. Source: Breakdown.divergenceAt_const_smul in Breakdown.Uniqueness.Scaling, line 41. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L41).

**Quadratic scaling of advection.** For differentiable velocity, constant amplitude scaling multiplies advection by the square of that constant. Source: Breakdown.advectionAt_const_smul in Breakdown.Uniqueness.Scaling, line 46. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L46).

**Linear scaling of the vector Laplacian.** Constant scaling of a smooth vector field scales its Laplacian by the same constant. Source: Breakdown.sumSecondPartialsAt_const_smul in Breakdown.Uniqueness.Scaling, line 51. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L51).

**Linear scaling of a pressure gradient.** Multiplying a differentiable scalar pressure by a constant multiplies its gradient by that constant. Source: Breakdown.gradientAt_const_mul in Breakdown.Uniqueness.Scaling, line 57. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L57).

**Time derivative after viscosity scaling.** The derivative of `c g(t/ν)` is `c/ν` times the derivative of `g` at `t/ν` under the stated differentiability assumption. Source: Breakdown.hasDerivAt_rescale_time in Breakdown.Uniqueness.Scaling, line 62. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/Scaling.lean#L62).

### Breakdown.Uniqueness.SelfStress

This file estimates the stress of a single velocity by cutoff energy and L6 bounds.

Reading context: §5 and Appendix A.2; the diagonal pressure-stress contribution.

**Source namespace:** Breakdown.

**Hessian entry below derivative norm.** The absolute value of a coordinate second partial is at most the full second derivative norm. Source: Breakdown.abs_secondPartial_le_norm in Breakdown.Uniqueness.SelfStress, line 11. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SelfStress.lean#L11).

**Continuous smooth Hessian entries.** Each coordinate second partial of a smooth scalar function is continuous. Source: Breakdown.continuous_secondPartial_smooth in Breakdown.Uniqueness.SelfStress, line 18. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SelfStress.lean#L18).

**Integrable finite-energy density.** A finite-energy field has integrable squared norm. Source: Breakdown.integrable_norm_sq in Breakdown.Uniqueness.SelfStress, line 23. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SelfStress.lean#L23).

**Integrable near-pressure stress.** For positive radius and finite-energy field data, the near part of the cutoff pressure-stress density is integrable. Source: Breakdown.integrable_near_part in Breakdown.Uniqueness.SelfStress, line 29. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SelfStress.lean#L29).

**An integral triangle bound.** When the first summand is integrable, the absolute integral of the sum is bounded by the sum of the two absolute integrals. Source: Breakdown.abs_integral_add_le_of_integrable in Breakdown.Uniqueness.SelfStress, line 94. [Private proved lemma](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SelfStress.lean#L94).

**Self-stress estimate.** For finite-energy data and `r ≥ 1`, the self-stress is controlled by the stated cubic local term and two far-field errors of orders `r^(-3/2)` and `r^(-5/2)`. Source: Breakdown.self_stress_le in Breakdown.Uniqueness.SelfStress, line 106. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SelfStress.lean#L106).

### Breakdown.Uniqueness.SimpleTerms

This file bounds the direct diffusion and transport terms in the weighted energy comparison.

Reading context: §5 and Appendix A.2; the elementary terms in physical uniqueness.

**Source namespace:** Breakdown.

**Integrating an energy-density bound.** A scalar integrand bounded by `C‖w‖²` has absolute integral at most `CA²` under the stated nonnegative coefficient and energy bound. Source: Breakdown.abs_integral_le_energy_mul in Breakdown.Uniqueness.SimpleTerms, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SimpleTerms.lean#L10).

**Integrable cutoff energy density.** A positive-radius cutoff times the squared norm of a continuous field is integrable. Source: Breakdown.integrable_cutoffPow_mul_sq in Breakdown.Uniqueness.SimpleTerms, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SimpleTerms.lean#L25).

**Cutoff Laplacian error bound.** For finite-energy data and radii at least one, the cutoff Laplacian contribution is bounded by `CA²/r`. Source: Breakdown.sumSecondPartials_term_le in Breakdown.Uniqueness.SimpleTerms, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SimpleTerms.lean#L37).

**Transport cutoff error bound.** For admissible difference data and `r ≥ 1`, the comparison-field transport flux is bounded by `CU₀A²/r`. Source: Breakdown.transport_term_le in Breakdown.Uniqueness.SimpleTerms, line 60. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SimpleTerms.lean#L60).

**Stretching bounded by local energy.** For admissible difference data and positive radius, the stretching term is bounded by `2U₁` times cutoff energy. Source: Breakdown.stretching_term_le in Breakdown.Uniqueness.SimpleTerms, line 93. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SimpleTerms.lean#L93).

### Breakdown.Uniqueness.SmoothUniqueness

This file proves equality of bounded-energy smooth solutions when one solution has the stated local velocity-and-gradient bounds.

Reading context: §5 and Appendix A.2; physical smooth-solution uniqueness.

**Source namespace:** Breakdown.

**Energy of two fields' difference.** The lower integral of the squared difference is bounded by `2|a|+2|b|` when the two energy bounds are `a` and `b`. Source: Breakdown.lintegral_norm_sub_sq_le in Breakdown.Uniqueness.SmoothUniqueness, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SmoothUniqueness.lean#L13).

**Differential Grönwall bound from zero.** A continuous function starting at zero with derivative at most `Ly+c` obeys the displayed exponential bound on the closed interval. Source: Breakdown.le_of_hasDerivAt_le_linear in Breakdown.Uniqueness.SmoothUniqueness, line 51. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SmoothUniqueness.lean#L51).

**Cutoff increases with radius.** The fourth-power cutoff is monotone in the radius when the smaller radius is positive. Source: Breakdown.cutoffPow_mono in Breakdown.Uniqueness.SmoothUniqueness, line 107. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SmoothUniqueness.lean#L107).

**Smooth uniqueness with energy control.** Two energy-bounded smooth solutions with equal initial velocity agree on the closed interval if one has uniformly bounded velocity and gradient there. Source: Breakdown.eq_of_isSolutionOn in Breakdown.Uniqueness.SmoothUniqueness, line 114. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/SmoothUniqueness.lean#L114).

### Breakdown.Uniqueness.StressFar

This file assembles the far-field stress estimate for the Newtonian pressure potential.

Reading context: §5 and Appendix A.2; the far-field pressure bound.

**Source namespace:** Breakdown.

**Far pressure-stress estimate.** For finite-energy data and `r ≥ 1`, the far pressure stress is bounded by a constant times the stated `A²` local-L6 and `A³` radius-decay terms. Source: Breakdown.far_stress_le in Breakdown.Uniqueness.StressFar, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFar.lean#L14).

### Breakdown.Uniqueness.StressFarAux

This file bounds the exterior Newtonian kernel by translated Hölder estimates and cutoff decay.

Reading context: §5 and Appendix A.2; kernel estimates for far-field stress.

**Source namespace:** Breakdown.Internal.FarStress.

**Near singular kernel.** The near kernel is inverse radius squared inside the radius-`r` ball and zero outside it. Source: Breakdown.Internal.FarStress.nearKernel in Breakdown.Uniqueness.StressFarAux, line 10. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L10).

**Far singular kernel.** The far kernel is inverse radius cubed outside the radius-`r` ball and zero inside it. Source: Breakdown.Internal.FarStress.farKernel in Breakdown.Uniqueness.StressFarAux, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L13).

**Measurable near kernel.** The near singular kernel is measurable for every radius. Source: Breakdown.Internal.FarStress.measurable_nearKernel in Breakdown.Uniqueness.StressFarAux, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L16).

**Measurable far kernel.** The far singular kernel is measurable for every radius. Source: Breakdown.Internal.FarStress.measurable_farKernel in Breakdown.Uniqueness.StressFarAux, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L20).

**Near-kernel L6/5 power bound.** For positive radius, the near kernel's L^(6/5) power integral is bounded by `(20π/3)r^(3/5)`. Source: Breakdown.Internal.FarStress.lintegral_nearKernel_rpow_le in Breakdown.Uniqueness.StressFarAux, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L24).

**Far-kernel L2 power bound.** For positive radius, the squared far-kernel integral is bounded by `(4π/3)r⁻³`. Source: Breakdown.Internal.FarStress.lintegral_farKernel_sq_le in Breakdown.Uniqueness.StressFarAux, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L37).

**A translated exponent-six estimate.** The shifted convolution of a kernel and a field is bounded by the kernel L^(6/5) norm times the field L6 norm. Source: Breakdown.Internal.FarStress.lintegral_translate_lpProd_six in Breakdown.Uniqueness.StressFarAux, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L50).

**Translated Cauchy-Schwarz estimate.** The shifted convolution of two nonnegative functions is bounded by their L2 norms. Source: Breakdown.Internal.FarStress.lintegral_translate_lpProd_two in Breakdown.Uniqueness.StressFarAux, line 64. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L64).

**Square root of a nonnegative square.** For nonnegative real `t`, the nonnegative-real square root of `t²` is the nonnegative-real value of `t`. Source: Breakdown.Internal.FarStress.ofReal_sq_rpow_half in Breakdown.Uniqueness.StressFarAux, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L78).

**Sixth root of a nonnegative sixth power.** For nonnegative real `t`, taking the sixth root of its sixth power recovers its nonnegative-real value. Source: Breakdown.Internal.FarStress.ofReal_pow_six_rpow in Breakdown.Uniqueness.StressFarAux, line 83. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L83).

**Reciprocal powers cancel.** For nonnegative `t`, raising its three-halves power to power two-thirds recovers its nonnegative-real value. Source: Breakdown.Internal.FarStress.ofReal_rpow_three_halves in Breakdown.Uniqueness.StressFarAux, line 89. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L89).

**Difference of cubes on the unit interval.** The absolute difference of the cubes of two numbers in `[0,1]` is at most one. Source: Breakdown.Internal.FarStress.abs_cube_sub_le_one in Breakdown.Uniqueness.StressFarAux, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L94).

**Lipschitz estimate for positive cubes.** For nonnegative inputs, the difference of cubes is bounded by `3/2` times the input difference times the sum of the squares. Source: Breakdown.Internal.FarStress.abs_cube_sub_le in Breakdown.Uniqueness.StressFarAux, line 103. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L103).

**Splitting the cutoff kernel.** The stated cutoff Lipschitz bound controls the weighted Hessian kernel by two near-kernel terms and one far-kernel term. Source: Breakdown.Internal.FarStress.kernel_weight_le in Breakdown.Uniqueness.StressFarAux, line 112. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux.lean#L112).

### Breakdown.Uniqueness.StressFarAux2

This file interpolates weighted energy and L6 control to estimate the far-field stress density.

Reading context: §5 and Appendix A.2; interpolation in the far-field estimate.

**Source namespace:** Breakdown.Internal.FarStress.

**Nonnegative conversion of squares.** For nonnegative real `t`, converting then taking the real square equals converting `t²`. Source: Breakdown.Internal.FarStress.ofReal_rpow_two_eq in Breakdown.Uniqueness.StressFarAux2, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux2.lean#L10).

**Nonnegative conversion of sixth powers.** For nonnegative real `t`, converting then taking the real sixth power equals converting `t⁶`. Source: Breakdown.Internal.FarStress.ofReal_rpow_six_eq in Breakdown.Uniqueness.StressFarAux2, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux2.lean#L14).

**Combining natural and real powers.** For nonnegative `t` and real exponent `p ≥ 0`, the nonnegative-real power of `tⁿ` equals the conversion of `t^(np)`. Source: Breakdown.Internal.FarStress.ofReal_pow_rpow in Breakdown.Uniqueness.StressFarAux2, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux2.lean#L19).

**L2 bound on the cutoff flux.** A flux bounded by `c₂‖w‖/r` has squared lower integral at most `(c₂A/r)²` under the stated energy bound. Source: Breakdown.Internal.FarStress.lintegral_flux_sq_le in Breakdown.Uniqueness.StressFarAux2, line 25. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux2.lean#L25).

**Weighted L6 bound on the flux.** The local L6 bound and the pointwise flux estimate give a weighted sixth-power integral at most `(c₂S/r)^6`. Source: Breakdown.Internal.FarStress.lintegral_weighted_flux_six_le in Breakdown.Uniqueness.StressFarAux2, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux2.lean#L47).

**Weighted energy interpolation.** The stated energy and local-L6 bounds control the weighted quadratic density's L^(3/2) norm by `SA`. Source: Breakdown.Internal.FarStress.productBound_weight_le in Breakdown.Uniqueness.StressFarAux2, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux2.lean#L73).

### Breakdown.Uniqueness.StressFarAux3

This file completes the scalar estimate required for the far-field pressure contribution.

Reading context: §5 and Appendix A.2; closure of the far-field stress bound.

**Source namespace:** Breakdown.Internal.FarStress.

**Base estimate for the far stress.** The stated energy, local-L6, cutoff and flux bounds imply the explicit near-kernel and far-kernel estimate for the double stress integral. Source: Breakdown.Internal.FarStress.far_base_le in Breakdown.Uniqueness.StressFarAux3, line 10. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressFarAux3.lean#L10).

### Breakdown.Uniqueness.StressNear

This file bounds the near-field pressure stress using the Hessian L2 estimate for the Newtonian potential.

Reading context: §5 and Appendix A.2; the near-field pressure bound.

**Source namespace:** Breakdown.

**Quadratic stress by a matrix L2 norm.** A quadratic tensor contraction is bounded by squared vector norm times the square root of the sum of squared matrix entries. Source: Breakdown.abs_double_sum_le in Breakdown.Uniqueness.StressNear, line 10. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressNear.lean#L10).

**Compact support inherited from a cutoff.** A function vanishing wherever a positive-radius radial cutoff vanishes has compact support. Source: Breakdown.hasCompactSupport_of_cutoff in Breakdown.Uniqueness.StressNear, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressNear.lean#L26).

**Combining the near-stress scalar bounds.** The stated nonnegative energy and flux bounds give `L ≤ 4c (a^(1/6))^(3/2) A^(3/2)/r` for positive `r`. Source: Breakdown.final_bound in Breakdown.Uniqueness.StressNear, line 34. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressNear.lean#L34).

**Near pressure-stress estimate.** For finite-energy data and `r ≥ 1`, the near pressure stress is bounded by a constant times the three-halves powers of local L6 norm and `A`, divided by `r`. Source: Breakdown.near_stress_le in Breakdown.Uniqueness.StressNear, line 75. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressNear.lean#L75).

### Breakdown.Uniqueness.StressSplit

This file separates the pressure source and its potential into near and far pieces with a remainder vanishing at the evaluation point.

Reading context: §5 and Appendix A.2; the pressure decomposition used in uniqueness.

**Source namespace:** Breakdown.

**Linear functional from coordinate values.** A linear functional applied to a vector equals the sum of its unit-vector values times that vector's coordinates. Source: Breakdown.sum_apply_unitVector_mul in Breakdown.Uniqueness.StressSplit, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L12).

**Derivative of the energy cutoff.** For positive radius, the derivative of the fourth-power cutoff is four times cutoff cubed times its derivative. Source: Breakdown.fderiv_cutoffPow in Breakdown.Uniqueness.StressSplit, line 17. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L17).

**Source equals cutoff times flux.** For a smooth divergence-free field, the cutoff source equals `4 cutoff³` times the cutoff flux. Source: Breakdown.cutoffSource_eq in Breakdown.Uniqueness.StressSplit, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L26).

**Smooth cutoff flux.** The cutoff flux of a smooth field is smooth for positive radius. Source: Breakdown.contDiff_cutoffFlux in Breakdown.Uniqueness.StressSplit, line 43. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L43).

**Compact cutoff-flux support.** For positive radius, the cutoff flux has compact support for every input field. Source: Breakdown.hasCompactSupport_cutoffFlux in Breakdown.Uniqueness.StressSplit, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L47).

**Linearity of second partials.** Coordinate second partials distribute over a sum and real scalar multiple of smooth scalar functions. Source: Breakdown.secondPartial_add_smul in Breakdown.Uniqueness.StressSplit, line 52. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L52).

**Splitting at a vanishing remainder.** When the source has the stated constant-plus-vanishing-remainder form, its potential Hessian splits into a local Hessian and a kernel-Hessian integral. Source: Breakdown.potential_split_generic in Breakdown.Uniqueness.StressSplit, line 64. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L64).

**Splitting the pressure source.** The Hessian of the cutoff-source potential splits into a cutoff-weighted flux potential and the integral containing the difference of the two cutoff cubes. Source: Breakdown.secondPartial_source_split in Breakdown.Uniqueness.StressSplit, line 96. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Uniqueness/StressSplit.lean#L96).
<!-- /passage:sec-breakdown-uniqueness -->

## Breakdown/Weak

<!-- passage:sec-breakdown-weak -->

### Breakdown.Weak.AdvectionByParts

This file proves the weak integration-by-parts formula that moves advection from the velocity onto a smooth divergence-free test field.

Reading context: §7.10 and Corollary 7.2; the weak-to-mild route.

**Source namespace:** Breakdown.WeakProfile.Internal.AdvectionByParts.

**Advection test-pairing density.** The pairing density contracts two velocity fields with the coordinate derivatives of a test field. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.pairForm in Breakdown.Weak.AdvectionByParts, line 17. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L17).

**Three-factor Hölder inequality.** The integral of three nonnegative measurable factors is bounded by their L6, L6 and L^(3/2) norms. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.lintegral_three_le in Breakdown.Weak.AdvectionByParts, line 20. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L20).

**Hölder bound for three vector norms.** The product integral of three measurable vector norms is bounded by two L6 norms and the third L^(3/2) norm. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.lintegral_enorm_three_le in Breakdown.Weak.AdvectionByParts, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L42).

**Finite compact L3/2 norm.** A continuous compactly supported field has finite L^(3/2) norm. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.lintegral_rpow_ne_top in Breakdown.Weak.AdvectionByParts, line 51. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L51).

**Coordinate pairing norm bound.** The norm of the coordinate-summed pairing is bounded by the sum of the two vector norms times each derivative-vector norm. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.enorm_sum_le in Breakdown.Weak.AdvectionByParts, line 63. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L63).

**Bounded bilinear test pairing on L6.** For a test field, the advection pairing is integrable on two L6 inputs and bounded by a fixed constant times their L6 norms. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.pairForm_bound in Breakdown.Weak.AdvectionByParts, line 77. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L77).

**Subtracting the first pairing input.** The integrated test pairing distributes over subtraction in its first L6 input. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.pairForm_sub_left in Breakdown.Weak.AdvectionByParts, line 119. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L119).

**Subtracting the second pairing input.** The integrated test pairing distributes over subtraction in its second L6 input. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.pairForm_sub_right in Breakdown.Weak.AdvectionByParts, line 126. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L126).

**Diagonal advection test form.** The diagonal form integrates the test-pairing density with the same L6 field in both inputs. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.diagForm in Breakdown.Weak.AdvectionByParts, line 133. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L133).

**Continuous diagonal test form.** For a valid test field, the diagonal advection test form is continuous on L6. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.continuous_diagForm in Breakdown.Weak.AdvectionByParts, line 135. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L135).

**Derivative of a coordinate-field product.** Differentiating a field multiplied by one of its coordinates gives the two terms of the product rule. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.fderiv_coord_smul in Breakdown.Weak.AdvectionByParts, line 158. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L158).

**Smooth advection integration by parts.** For two solenoidal test fields, the quadratic derivative pairing equals the negative advection pairing. Source: Breakdown.WeakProfile.Internal.AdvectionByParts.smooth_by_parts in Breakdown.Weak.AdvectionByParts, line 168. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L168).

**Source namespace:** Breakdown.WeakProfile.

**Discharge advection integration by parts.** This theorem proves the interface identifying the weak quadratic test integral with the negative trilinear form. Source: Breakdown.WeakProfile.advectionByParts_holds in Breakdown.Weak.AdvectionByParts, line 218. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/AdvectionByParts.lean#L218).

### Breakdown.Weak.Basic

This file defines the profile-to-physical rescaling, weak evolution rates, slice realizations and the good-time integral identities.

Reading context: §7.10 and Corollary 7.2; the weak-profile framework.

**Source namespace:** Breakdown.WeakProfile.

**Spatial rescaling of a test field.** Spatial rescaling evaluates the field at `b` times the spatial argument without an amplitude factor. Source: Breakdown.WeakProfile.spaceScale in Breakdown.Weak.Basic, line 13. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L13).

**Coordinate column of a weak gradient.** A gradient component evaluates the derivative-valued field on a coordinate unit vector. Source: Breakdown.WeakProfile.gradComponent in Breakdown.Weak.Basic, line 15. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L15).

**Similarity scaling factor.** The similarity scale is `exp(-(σ-s₀)/2)`. Source: Breakdown.WeakProfile.similarityScale in Breakdown.Weak.Basic, line 18. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L18).

**Rescaled spacetime test field.** The rescaled test multiplies the spatially scaled negative Laplacian by the time test and the square of the similarity scale. Source: Breakdown.WeakProfile.scaledTest in Breakdown.Weak.Basic, line 22. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L22).

**Weak evolution rate against a test.** The weak rate is the Hilbert pairing with the embedded negative Laplacian plus the quadratic trilinear pairing against that negative Laplacian. Source: Breakdown.WeakProfile.weakRate in Breakdown.Weak.Basic, line 25. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L25).

**Rate against a Laplacian pair.** The Laplacian-pair rate combines the Hilbert inner product with the trilinear pairing against the second element's velocity. Source: Breakdown.WeakProfile.sspRate in Breakdown.Weak.Basic, line 28. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L28).

**Similarity-time test rate.** The similarity rate combines the negative derivative of the scalar time test with its rescaled weak evolution rate. Source: Breakdown.WeakProfile.similarityRate in Breakdown.Weak.Basic, line 30. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L30).

**Bounded curve realizing weak slices.** This proposition requires the Hilbert curve's velocity and coordinate derivatives to realize the supplied weak slice data almost everywhere, with one uniform norm bound. Source: Breakdown.WeakProfile.IsSliceCurve in Breakdown.Weak.Basic, line 43. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L43).

**Tensor-product weak evolution identity.** This proposition requires the weak time identity against every compact smooth time test and every solenoidal spatial test inside the interval. Source: Breakdown.WeakProfile.IsTensorWeak in Breakdown.Weak.Basic, line 49. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L49).

**A full-measure set of good times.** This proposition requires a full-measure subset of the open interval where every Laplacian-pair integral identity holds between ordered good times. Source: Breakdown.WeakProfile.IsGoodSet in Breakdown.Weak.Basic, line 54. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Basic.lean#L54).

### Breakdown.Weak.BilinIntegrable

This file proves integrability of the abstract bilinear evolution along bounded measurable state curves.

Reading context: §7.10 and Corollary 7.2; admissibility of the weak route's Duhamel integral.

**Source namespace:** Breakdown.WeakProfile.Internal.BilinIntegrable.

**A difference of diagonal interactions.** Subtracting two diagonal bilinear interactions gives the interaction of the difference with the first field plus the second field with the difference. Source: Breakdown.WeakProfile.Internal.BilinIntegrable.bilinX_diag_sub in Breakdown.Weak.BilinIntegrable, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/BilinIntegrable.lean#L14).

**Interaction continuity for positive time.** Clamping elapsed time below by a positive `δ` makes the diagonal bilinear interaction jointly continuous in time and state. Source: Breakdown.WeakProfile.Internal.BilinIntegrable.continuous_bilinX_max in Breakdown.Weak.BilinIntegrable, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/BilinIntegrable.lean#L19).

**Measurability on truncated intervals.** For a bounded measurable curve, the shifted bilinear integrand is measurable on each stated interval truncated away from its terminal singularity. Source: Breakdown.WeakProfile.Internal.BilinIntegrable.aestronglyMeasurable_piece in Breakdown.Weak.BilinIntegrable, line 61. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/BilinIntegrable.lean#L61).

**Measurability on an open interval.** The shifted bilinear integrand of a measurable curve is measurable on the full open integration interval under the stated time inequalities. Source: Breakdown.WeakProfile.Internal.BilinIntegrable.aestronglyMeasurable_Ioo in Breakdown.Weak.BilinIntegrable, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/BilinIntegrable.lean#L80).

**Source namespace:** Breakdown.WeakProfile.

**Discharge bilinear time integrability.** This theorem proves interval integrability of the shifted bilinear interaction for bounded measurable curves on the allowed time window. Source: Breakdown.WeakProfile.bilinIntegrable_holds in Breakdown.Weak.BilinIntegrable, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/BilinIntegrable.lean#L100).

### Breakdown.Weak.ConstOfWeakDeriv

This file recovers an almost-everywhere integral primitive, up to one constant, from the scalar weak time-derivative identity.

Reading context: §7.10 and Corollary 7.2; recovery of time identities from weak derivatives.

**Source namespace:** Breakdown.WeakProfile.Internal.

**Enclosing compact support in an interval.** A compact subset of an open interval lies inside a smaller open interval with endpoints strictly inside the original one. Source: Breakdown.WeakProfile.Internal.exists_Ioo_cover in Breakdown.Weak.ConstOfWeakDeriv, line 12. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ConstOfWeakDeriv.lean#L12).

**A test derivative on a half-line.** The derivative of a smooth compactly supported time test integrates over `[τ,∞)` to minus its value at `τ`. Source: Breakdown.WeakProfile.Internal.integral_Ici_deriv in Breakdown.Weak.ConstOfWeakDeriv, line 24. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ConstOfWeakDeriv.lean#L24).

**Integration by parts with a primitive.** For the stated integrable forcing, pairing the derivative of a compact time test with its primitive equals minus the forcing-test integral. Source: Breakdown.WeakProfile.Internal.integral_deriv_mul_primitive in Breakdown.Weak.ConstOfWeakDeriv, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ConstOfWeakDeriv.lean#L36).

**Compact primitive of a zero-mean test.** A smooth zero-integral function supported inside the interval has a smooth compactly supported primitive whose derivative is that function. Source: Breakdown.WeakProfile.Internal.primitive_test in Breakdown.Weak.ConstOfWeakDeriv, line 65. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ConstOfWeakDeriv.lean#L65).

**Source namespace:** Breakdown.WeakProfile.

**Discharge the weak-derivative primitive.** This theorem proves that the stated weak time-derivative identity gives an almost-everywhere primitive plus one constant. Source: Breakdown.WeakProfile.constOfWeakDeriv_holds in Breakdown.Weak.ConstOfWeakDeriv, line 101. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ConstOfWeakDeriv.lean#L101).

### Breakdown.Weak.ContinuousVarConst

This file proves continuity of the variation-of-constants expression by controlling the singular terminal part of its time integral.

Reading context: §7.10 and Corollary 7.2; passage from almost-everywhere to continuous mild evolution.

**Source namespace:** Breakdown.WeakProfile.Internal.ContinuousVarConst.

**Bilinear interaction at nonpositive time.** The abstract bilinear kernel is zero for nonpositive elapsed time. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.bilinX_of_nonpos in Breakdown.Weak.ContinuousVarConst, line 14. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L14).

**A diagonal kernel bound.** The positive-time kernel estimate extends to nonnegative elapsed time with diagonal input bound `CM²σ^(-3/4)`. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.norm_bilin_le in Breakdown.Weak.ContinuousVarConst, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L18).

**Integral of the singular time kernel.** The three-quarter singularity integrates to `4(t-m)^(1/4)` between the stated endpoints. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.kernel_integral in Breakdown.Weak.ContinuousVarConst, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L35).

**An integrable singular time kernel.** The kernel `(t-τ)^(-3/4)` is interval integrable between the stated endpoints. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.kernel_intervalIntegrable in Breakdown.Weak.ContinuousVarConst, line 44. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L44).

**Integrability up to an intermediate time.** The bilinear-integrability interface gives integrability of the terminal-time kernel up to any intermediate time in the allowed window. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.integ in Breakdown.Weak.ContinuousVarConst, line 53. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L53).

**A small terminal Duhamel remainder.** Removing the last `δ` units of the bilinear time integral changes it by at most `4CM²δ^(1/4)` under the stated bounds. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.remainder in Breakdown.Weak.ContinuousVarConst, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L62).

**A bound away from the terminal time.** When elapsed time is at least `δ/2`, the diagonal interaction is bounded by `CM²(δ/2)^(-3/4)`. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.pt_bound in Breakdown.Weak.ContinuousVarConst, line 90. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L90).

**Removing an irrelevant maximum branch.** If `a < τ ≤ max(a,c)`, then `τ ≤ c`. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.le_of_le_max in Breakdown.Weak.ContinuousVarConst, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L99).

**Continuous truncated Duhamel integral.** Keeping a positive distance from the terminal singularity makes the truncated bilinear integral continuous on the closed time window. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.trunc_continuousOn in Breakdown.Weak.ContinuousVarConst, line 105. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L105).

**Continuous full Duhamel integral.** The small terminal remainder and truncated continuity give continuity of the full bilinear time integral. Source: Breakdown.WeakProfile.Internal.ContinuousVarConst.integral_continuousOn in Breakdown.Weak.ContinuousVarConst, line 179. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L179).

**Source namespace:** Breakdown.WeakProfile.

**Prove continuity of Duhamel's formula.** This theorem proves that variation of constants is continuous on the allowed half-open interval under the bilinear-integrability interface. Source: Breakdown.WeakProfile.continuousVarConst_holds in Breakdown.Weak.ContinuousVarConst, line 209. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ContinuousVarConst.lean#L209).

### Breakdown.Weak.GoodTimes

This file selects times at which the integrated weak test identities hold and controls approximations to those identities.

Reading context: §7.10 and Corollary 7.2; common good times for the weak formulation.

**Source namespace:** Breakdown.WeakProfile.Internal.GoodTimes.

**Subtracting Laplacian-pair rates.** For two valid Laplacian pairs, subtracting their rates equals the rate evaluated on the difference of their second components. Source: Breakdown.WeakProfile.Internal.GoodTimes.sspRate_sub in Breakdown.Weak.GoodTimes, line 19. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L19).

**Continuous rate against a Laplacian pair.** For a valid Laplacian pair, the rate is continuous as a function of the evolving Hilbert-space state. Source: Breakdown.WeakProfile.Internal.GoodTimes.continuous_sspRate in Breakdown.Weak.GoodTimes, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L26).

**Quantitative Laplacian-pair rate bound.** The stated trilinear bound gives `|rate| ≤ Ab + KA²(a+b)` for the stated state and test-pair norm bounds. Source: Breakdown.WeakProfile.Internal.GoodTimes.abs_sspRate_le in Breakdown.Weak.GoodTimes, line 33. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L33).

**Integrating a bounded observable.** A continuous scalar observable of a measurable curve is integrable on the finite interval when it has the stated uniform bound. Source: Breakdown.WeakProfile.Internal.GoodTimes.integrableOn_comp in Breakdown.Weak.GoodTimes, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L49).

**An integrated test identity a.e..** The weak-derivative interface converts a tensor weak solution into an almost-everywhere primitive identity for each spatial test pairing. Source: Breakdown.WeakProfile.Internal.GoodTimes.pair_identity in Breakdown.Weak.GoodTimes, line 55. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L55).

**Approximating a Laplacian pair.** Density of the stated test-pair set supplies an approximating pair within any positive tolerance in both components. Source: Breakdown.WeakProfile.Internal.GoodTimes.exists_near in Breakdown.Weak.GoodTimes, line 80. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L80).

**Error bounds for good-time identities.** The stated norm bounds control the residual weak identity for an approximating test pair by an explicit constant times the approximation tolerance. Source: Breakdown.WeakProfile.Internal.GoodTimes.approx_bound in Breakdown.Weak.GoodTimes, line 100. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L100).

**Separable space of test pairs.** The product Hilbert space of test pairs is separable. Source: Breakdown.WeakProfile.Internal.GoodTimes.separableSpace_pair in Breakdown.Weak.GoodTimes, line 144. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GoodTimes.lean#L144).

### Breakdown.Weak.GradientFreqTr

This file reconstructs a state-space gradient from weak physical derivatives through Fourier transformation and the solenoidal constraints.

Reading context: §7.10 and Corollary 7.2; the physical-gradient-to-state bridge.

**Source namespace:** Breakdown.WeakProfile.Internal.GradientFreqTr.

**L2 weak-gradient field.** The weak-slice conditions imply L2 membership of the derivative-valued gradient field. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.memLp_grad in Breakdown.Weak.GradientFreqTr, line 22. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L22).

**L2 coordinate weak gradients.** Each coordinate column of a weak slice's gradient belongs to L2. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.memLp_comp in Breakdown.Weak.GradientFreqTr, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L30).

**Weak mixed-gradient compatibility.** For a weak gradient, exchanging the two test derivative indices leaves the real integral pairing unchanged. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.sym_real in Breakdown.Weak.GradientFreqTr, line 34. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L34).

**Complex scalar on a real vector.** A complex scalar times a complexified real vector splits into its real part plus `i` times its imaginary part. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.smul_cv in Breakdown.Weak.GradientFreqTr, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L52).

**Integrating complexified vector products.** Under the two stated integrability assumptions, a complex scalar-vector integral splits into the complexified real and imaginary integrals. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.integral_smul_cv in Breakdown.Weak.GradientFreqTr, line 58. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L58).

**Complex weak-gradient compatibility.** For the stated L2 weak gradient, exchanging the two derivative indices preserves the complex test pairing. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.sym_cplx in Breakdown.Weak.GradientFreqTr, line 71. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L71).

**Compact truncation of a complex test.** The complex test cutoff multiplies the test function by the standard bump at inverse spatial scale. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.cutoff in Breakdown.Weak.GradientFreqTr, line 105. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L105).

**Smooth complex test cutoff.** Cutting off a smooth complex test function preserves smoothness. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.contDiff_cutoff in Breakdown.Weak.GradientFreqTr, line 107. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L107).

**Compact complex cutoff support.** At nonzero cutoff radius, the truncated complex test has compact support. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.hasCompactSupport_cutoff in Breakdown.Weak.GradientFreqTr, line 111. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L111).

**Cutoff derivative agrees inside the ball.** Inside a positive-radius cutoff ball, the derivative of the truncated test equals the derivative of the original test. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.fderiv_cutoff_eq in Breakdown.Weak.GradientFreqTr, line 115. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L115).

**Derivative bound for truncated tests.** For cutoff radii at least one, each truncated test derivative is bounded by the original derivative norm plus a fixed multiple of the original function norm. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.fderiv_cutoff_bound in Breakdown.Weak.GradientFreqTr, line 130. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L130).

**Removing the cutoff in gradient pairings.** For a Schwartz test and L2 gradient components, the cutoff derivative pairing tends to the untruncated derivative pairing as radius tends to infinity. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.tendsto_cut in Breakdown.Weak.GradientFreqTr, line 175. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L175).

**Schwartz weak-gradient compatibility.** The weak mixed-gradient compatibility identity extends from compact tests to Schwartz tests. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.sym_rapid in Breakdown.Weak.GradientFreqTr, line 205. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L205).

**Fourier image of a gradient component.** The transformed gradient component is the L2 Fourier transform of its complexified L2 representative. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.hatComp in Breakdown.Weak.GradientFreqTr, line 214. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L214).

**Representing a complex weak gradient.** For an L2 gradient component, the complexified class agrees almost everywhere with pointwise complexification. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.coe_comp in Breakdown.Weak.GradientFreqTr, line 217. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L217).

**Fourier derivative pairing formula.** The Fourier pairing carrying one coordinate frequency factor equals the physical derivative pairing with the factor `-2πi` shown in the statement. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.pair_deriv in Breakdown.Weak.GradientFreqTr, line 227. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L227).

**Symmetry of Fourier gradient pairings.** The weak-gradient condition makes the two coordinate-frequency test pairings equal. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.pair_sym in Breakdown.Weak.GradientFreqTr, line 248. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L248).

**Weak gradients in frequency space.** Almost everywhere, `ξ_k` times the transformed `j`th gradient component equals `ξ_j` times the transformed `k`th component. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.compat in Breakdown.Weak.GradientFreqTr, line 259. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L259).

**Zero trace of the transformed gradient.** For a valid weak slice, the sum of the diagonal coordinates of the transformed gradient components vanishes almost everywhere. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.div_hat in Breakdown.Weak.GradientFreqTr, line 293. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L293).

**Reconstructing the gradient carrier.** The gradient carrier sums the normalised gradient multipliers applied to the three transformed weak-gradient components. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.gradSum in Breakdown.Weak.GradientFreqTr, line 335. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L335).

**Pointwise gradient-carrier formula.** The reconstructed gradient carrier is represented almost everywhere by the sum of the three pointwise multiplier products. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.gradSum_ae in Breakdown.Weak.GradientFreqTr, line 338. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L338).

**No longitudinal reconstructed component.** For a valid weak slice, applying the longitudinal field operator to the reconstructed gradient carrier gives zero. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.long_gradSum in Breakdown.Weak.GradientFreqTr, line 348. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L348).

**The gradient meets its constraints.** The reconstructed gradient carrier of a weak slice belongs to the constrained Fourier subspace. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.gradSum_mem in Breakdown.Weak.GradientFreqTr, line 374. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L374).

**Recovering the weak partial derivatives.** Each partial derivative of the reconstructed Hilbert-space element equals the corresponding supplied weak-gradient column almost everywhere. Source: Breakdown.WeakProfile.Internal.GradientFreqTr.partial_gradSum in Breakdown.Weak.GradientFreqTr, line 385. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L385).

**Source namespace:** Breakdown.WeakProfile.

**Prove weak-gradient reconstruction.** This theorem proves that every valid weak slice has a Hilbert-space element realizing all of its supplied gradient columns. Source: Breakdown.WeakProfile.gradientFreqTr_holds in Breakdown.Weak.GradientFreqTr, line 425. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/GradientFreqTr.lean#L425).

### Breakdown.Weak.OrbitOfParts

This file assembles the weak-profile interfaces into a continuous abstract mild orbit and transfers the physical blow-up behavior to that orbit.

Reading context: §7.10 and Corollary 7.2; completion of the alternate weak-profile route.

**Source namespace:** Breakdown.WeakProfile.

**Rotations preserve null-set equality.** Pushing fields forward by a linear isometry preserves almost-everywhere equality. Source: Breakdown.WeakProfile.pushForward_ae_congr in Breakdown.Weak.OrbitOfParts, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L13).

**Velocity determines the state.** Two Hilbert-space states with almost-everywhere equal physical velocities are equal. Source: Breakdown.WeakProfile.eq_of_velocity_ae in Breakdown.Weak.OrbitOfParts, line 21. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L21).

**Mildness under equality on an interval.** A curve equal to a mild curve throughout the closed interval is itself mild there. Source: Breakdown.WeakProfile.isMildX_congr in Breakdown.Weak.OrbitOfParts, line 29. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L29).

**Bounded velocity before terminal time.** A uniformly bounded similarity curve becomes bounded on every stated physical interval ending at `r < 1`, with factor `(1-r)^(-1/4)`. Source: Breakdown.WeakProfile.physicalCurve_bound in Breakdown.Weak.OrbitOfParts, line 48. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L48).

**Exponential-logarithmic time identity.** For `t < 1`, the similarity-time exponential simplifies to `1-t`. Source: Breakdown.WeakProfile.exp_timeChange in Breakdown.Weak.OrbitOfParts, line 58. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L58).

**Inverse positive dilations cancel.** For positive parameter, dilation composed with dilation by its reciprocal is the identity. Source: Breakdown.WeakProfile.dilX_inv_cancel in Breakdown.Weak.OrbitOfParts, line 62. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L62).

**Joint continuity of positive dilation.** Dilation is jointly continuous in positive scale and Hilbert-space state. Source: Breakdown.WeakProfile.dilX_joint in Breakdown.Weak.OrbitOfParts, line 68. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L68).

**Continuous positive dilation.** Continuous scale and state curves with strictly positive scale give a continuous dilated curve on the same set. Source: Breakdown.WeakProfile.dilX_comp_continuousOn in Breakdown.Weak.OrbitOfParts, line 71. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L71).

**Local continuous mild representative.** The stated weak-time, good-time and integrability interfaces give a continuous representative of each physical curve that is mild on every compact inner interval. Source: Breakdown.WeakProfile.localMild in Breakdown.Weak.OrbitOfParts, line 76. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L76).

**Local representatives in similarity time.** Local physical-time representatives and the null-set time-change interface give a continuous almost-everywhere representative on every open similarity-time interval. Source: Breakdown.WeakProfile.representative in Breakdown.Weak.OrbitOfParts, line 113. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/OrbitOfParts.lean#L113).

### Breakdown.Weak.PairingDilate

This file proves how velocity pairings and test-field derivatives transform under the weak profile's dilation.

Reading context: §7.10 and Corollary 7.2; rescaled weak test pairings.

**Source namespace:** Breakdown.WeakProfile.

**Derivative of spatial rescaling.** Differentiating spatial rescaling by `b` gives `b` times the original derivative at the scaled point. Source: Breakdown.WeakProfile.fderiv_spaceScale in Breakdown.Weak.PairingDilate, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingDilate.lean#L13).

**Smoothness under spatial rescaling.** Spatial rescaling preserves smoothness of a vector field. Source: Breakdown.WeakProfile.contDiff_spaceScale in Breakdown.Weak.PairingDilate, line 22. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingDilate.lean#L22).

**Coordinate derivatives under dilation.** A coordinate derivative of the spatially rescaled field is `b` times the spatial rescaling of that derivative. Source: Breakdown.WeakProfile.partialField_spaceScale in Breakdown.Weak.PairingDilate, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingDilate.lean#L26).

**Coordinate derivatives under scaling.** Multiplication of a differentiable field by a scalar commutes with each coordinate derivative. Source: Breakdown.WeakProfile.partialField_smul in Breakdown.Weak.PairingDilate, line 31. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingDilate.lean#L31).

**Negative Laplacian under dilation.** The negative Laplacian of a smooth field rescaled by `b` is `b²` times the rescaled negative Laplacian. Source: Breakdown.WeakProfile.negSsp_spaceScale in Breakdown.Weak.PairingDilate, line 39. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingDilate.lean#L39).

**Spatial scaling preserves test fields.** Rescaling a test field by a nonzero spatial factor preserves its test-field conditions. Source: Breakdown.WeakProfile.isTestField_spaceScale in Breakdown.Weak.PairingDilate, line 53. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingDilate.lean#L53).

**Prove the dilated pairing formula.** This theorem proves the pairing-dilation interface, conditional on the velocity-pairing interface. Source: Breakdown.WeakProfile.pairingDilate_holds in Breakdown.Weak.PairingDilate, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingDilate.lean#L62).

### Breakdown.Weak.PairingVelocity

This file identifies the abstract state pairing with the physical velocity pairing against the corresponding test field.

Reading context: §7.10 and Corollary 7.2; agreement of state and velocity pairings.

**Source namespace:** Breakdown.WeakProfile.Internal.PairingVelocity.

**Velocity test pairing as an Lp pairing.** Under the stated L^(6/5) test condition, the velocity integral equals the continuous L6-L^(6/5) dual pairing. Source: Breakdown.WeakProfile.Internal.PairingVelocity.pairing_eq_lp in Breakdown.Weak.PairingVelocity, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingVelocity.lean#L17).

**Source namespace:** Breakdown.WeakProfile.

**Discharge the velocity-pairing formula.** This theorem proves that the Hilbert pairing with an embedded test equals the physical velocity pairing with its negative Laplacian. Source: Breakdown.WeakProfile.pairingVelocity_holds in Breakdown.Weak.PairingVelocity, line 30. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PairingVelocity.lean#L30).

### Breakdown.Weak.PhysicalIdentity

This file changes from profile time to physical time and derives the weak physical Navier-Stokes identity for the rescaled velocity.

Reading context: §7.10 and Corollary 7.2; the weak equation after rescaling.

**Source namespace:** Breakdown.WeakProfile.Internal.PhysicalIdentity.

**Positive similarity scale.** The similarity scale is strictly positive for all reference and similarity times. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.scale_pos in Breakdown.Weak.PhysicalIdentity, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L16).

**Square of the similarity scale.** The square of the similarity scale is `exp(-(σ-s₀))`. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.scale_sq in Breakdown.Weak.PhysicalIdentity, line 18. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L18).

**Continuous similarity scale.** The similarity scaling factor is continuous in similarity time. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.continuous_scale in Breakdown.Weak.PhysicalIdentity, line 21. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L21).

**Similarity-to-physical time map.** The physical time associated with similarity time is `1-exp(-(σ-s₀))`. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.timeChange in Breakdown.Weak.PhysicalIdentity, line 24. [Definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L24).

**Derivative of the time change.** The derivative of the similarity-to-physical time map is the square of the similarity scale. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.hasDerivAt_timeChange in Breakdown.Weak.PhysicalIdentity, line 26. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L26).

**Injective similarity time change.** The similarity-to-physical time map is injective. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.timeChange_injective in Breakdown.Weak.PhysicalIdentity, line 31. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L31).

**Range of physical time.** The time-change map sends the entire similarity-time line onto the physical interval `t < 1`. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.image_timeChange in Breakdown.Weak.PhysicalIdentity, line 37. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L37).

**Remaining time is the scale squared.** One minus the physical time equals the square of the similarity scale. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.one_sub_timeChange in Breakdown.Weak.PhysicalIdentity, line 49. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L49).

**Inverse square-root time identity.** The reciprocal of the square root of reciprocal remaining time, `1/√(1/(1-t))`, equals the similarity scale at the corresponding physical time. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.sqrt_inv_timeChange in Breakdown.Weak.PhysicalIdentity, line 52. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L52).

**Positive inverse remaining time.** The reciprocal of the remaining physical time is positive at every time-change value. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.inv_timeChange_pos in Breakdown.Weak.PhysicalIdentity, line 56. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L56).

**Physical curve at a changed time.** Evaluating the physical curve at the changed time gives the similarity state dilated by inverse remaining physical time. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.curve_timeChange in Breakdown.Weak.PhysicalIdentity, line 59. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L59).

**Rescaling solenoidal test fields.** A nonzero spatial rescaling of a test field is again a test field. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.isTestField_spaceScale in Breakdown.Weak.PhysicalIdentity, line 66. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L66).

**Scaling the negative Laplacian.** The negative Laplacian under spatial scaling gains a factor of `b²`. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.negSsp_spaceScale in Breakdown.Weak.PhysicalIdentity, line 82. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L82).

**Scalar linearity in the trilinear test.** Multiplying the physical test field by a real scalar multiplies the trilinear pairing by that scalar. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.trilinear_smul in Breakdown.Weak.PhysicalIdentity, line 99. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L99).

**Test pairing after time change.** The velocity and dilation pairing interfaces identify the physical-time test pairing with the similarity-state pairing against the scaled test. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.pairing_timeChange in Breakdown.Weak.PhysicalIdentity, line 110. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L110).

**Trilinear pairing after time change.** The weak-gradient and dilation interfaces identify the physical-time trilinear pairing with the similarity-state pairing against the scaled test. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.trilinear_timeChange in Breakdown.Weak.PhysicalIdentity, line 116. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L116).

**Weak-rate transformation.** Under the stated pairing and dilation interfaces, the physical weak rate times scale squared equals the similarity weak rate against the scaled test. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.weakRate_timeChange in Breakdown.Weak.PhysicalIdentity, line 122. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L122).

**Embedding a spatially scaled test.** For positive `b`, the embedded spatially scaled test is `b⁻¹` times dilation by `b²` of the original embedding. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.embedX_spaceScale in Breakdown.Weak.PhysicalIdentity, line 137. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L137).

**Continuous scaled-test embeddings.** Embedding a test field rescaled by the similarity factor gives a continuous Hilbert-space curve. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.continuous_embedX_spaceScale in Breakdown.Weak.PhysicalIdentity, line 148. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L148).

**Compact time support stays below one.** A compact subset of `(-1,1)` has an upper bound strictly below one. Source: Breakdown.WeakProfile.Internal.PhysicalIdentity.exists_lt_one in Breakdown.Weak.PhysicalIdentity, line 159. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/PhysicalIdentity.lean#L159).

### Breakdown.Weak.Representative

This file chooses a strongly measurable profile representative and transfers its almost-everywhere identities through logarithmic time.

Reading context: §7.10 and Corollary 7.2; measurable physical representatives.

**Source namespace:** Breakdown.WeakProfile.

**Local representatives agree on overlap.** Continuous representatives agreeing almost everywhere with the same curve agree everywhere on their common open interval. Source: Breakdown.WeakProfile.eqOn_of_ae_interval in Breakdown.Weak.Representative, line 11. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Representative.lean#L11).

**Physical-to-similarity inverse identity.** For `t < 1`, changing to logarithmic similarity time and back returns `t`. Source: Breakdown.WeakProfile.timeBack_forward in Breakdown.Weak.Representative, line 59. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Representative.lean#L59).

**Forward time always remains below one.** The physical time obtained from any real similarity time is strictly less than one. Source: Breakdown.WeakProfile.timeBack_lt in Breakdown.Weak.Representative, line 65. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Representative.lean#L65).

**Similarity-to-physical inverse identity.** Changing from similarity time to physical time and back returns the original similarity time. Source: Breakdown.WeakProfile.timeForward_back in Breakdown.Weak.Representative, line 68. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Representative.lean#L68).

**Discharge preservation of null sets.** This theorem proves equivalence of almost-everywhere statements under the logarithmic time change onto `t < 1`. Source: Breakdown.WeakProfile.timeChangeNull_holds in Breakdown.Weak.Representative, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Representative.lean#L73).

**Logarithmic time preserves null sets.** The logarithmic inverse time change preserves null sets from the restricted physical-time measure to similarity-time volume. Source: Breakdown.WeakProfile.timeChange_quasiMeasurePreserving in Breakdown.Weak.Representative, line 99. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Representative.lean#L99).

**Discharge physical-curve measurability.** This theorem proves that measurable similarity curves give measurable physical curves on `t < 1`. Source: Breakdown.WeakProfile.physicalCurveMeasurable_holds in Breakdown.Weak.Representative, line 109. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/Representative.lean#L109).

### Breakdown.Weak.ScaledTestField

This file verifies that the amplitude and spatially rescaled test fields remain smooth, compactly supported and divergence free.

Reading context: §7.10 and Corollary 7.2; admissibility of rescaled weak tests.

**Source namespace:** Breakdown.WeakProfile.

**Smooth similarity scale.** The similarity scaling factor is smooth in similarity time. Source: Breakdown.WeakProfile.contDiff_similarityScale in Breakdown.Weak.ScaledTestField, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ScaledTestField.lean#L12).

**Strictly positive similarity scale.** The similarity scaling factor is strictly positive. Source: Breakdown.WeakProfile.similarityScale_pos in Breakdown.Weak.ScaledTestField, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ScaledTestField.lean#L16).

**Divergence under the two scalings.** Scaling a smooth field by amplitude `c` and spatial factor `b` multiplies its divergence by `cb` at the scaled point. Source: Breakdown.WeakProfile.divergenceAt_scaled in Breakdown.Weak.ScaledTestField, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ScaledTestField.lean#L18).

**Discharge the scaled-test construction.** This theorem proves that a compact smooth time test and a solenoidal spatial test produce an admissible rescaled spacetime test field. Source: Breakdown.WeakProfile.scaledTestField_holds in Breakdown.Weak.ScaledTestField, line 35. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ScaledTestField.lean#L35).

### Breakdown.Weak.SliceEmbedding

This file embeds a physical slice with an L2 weak gradient into the abstract state space and computes its energy.

Reading context: §7.10 and Corollary 7.2; reconstruction of a state from each weak slice.

**Source namespace:** Breakdown.WeakProfile.

**L2 norm as an ordinary square integral.** The squared norm of a real-vector L2 element equals the integral of the squared norm of its representative. Source: Breakdown.WeakProfile.sq_norm_L2R_eq_integral in Breakdown.Weak.SliceEmbedding, line 13. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceEmbedding.lean#L13).

**Coordinate unit-vector norm.** Every coordinate unit vector has norm one. Source: Breakdown.WeakProfile.norm_unitVector_eq in Breakdown.Weak.SliceEmbedding, line 20. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceEmbedding.lean#L20).

**Embedding energy by partial energies.** The squared Hilbert norm of an embedded test field is the sum of the squared norms of its three partial derivatives. Source: Breakdown.WeakProfile.sq_norm_embed_eq_sum_partial in Breakdown.Weak.SliceEmbedding, line 23. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceEmbedding.lean#L23).

**Hilbert norm as summed partial energies.** Every Hilbert-space element has squared norm equal to the sum of its three partial-derivative squared norms. Source: Breakdown.WeakProfile.sq_norm_eq_sum_partial in Breakdown.Weak.SliceEmbedding, line 40. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceEmbedding.lean#L40).

**Partial norm from a weak-gradient bound.** If a partial derivative realizes a supplied gradient column, its squared norm is at most `max C 0` under the stated gradient-energy bound. Source: Breakdown.WeakProfile.sq_norm_partial_le in Breakdown.Weak.SliceEmbedding, line 53. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceEmbedding.lean#L53).

**L6 membership from local integrability.** A locally integrable field with finite sixth-power lower integral belongs to L6. Source: Breakdown.WeakProfile.memLp_six_of_bound in Breakdown.Weak.SliceEmbedding, line 78. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceEmbedding.lean#L78).

### Breakdown.Weak.SliceIntegrand

This file rewrites the rescaled weak time integrand as the abstract state rate paired with a test state.

Reading context: §7.10 and Corollary 7.2; identification of the weak evolution integrand.

**Source namespace:** Breakdown.WeakProfile.Internal.SliceIntegrand.

**Integrable compact test pairing.** A locally integrable vector field paired with a continuous compactly supported test field gives an integrable scalar function. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.integrable_inner_loc in Breakdown.Weak.SliceIntegrand, line 16. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L16).

**Derivative under two scalings.** Differentiating `cN(by)` gives `cb` times the original derivative evaluated at `by`. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.fderiv_scaled in Breakdown.Weak.SliceIntegrand, line 27. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L27).

**Dilation with unit amplitude.** Spatial rescaling is the general amplitude-and-space rescaling with amplitude one. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.spaceScale_eq in Breakdown.Weak.SliceIntegrand, line 36. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L36).

**Admissible nonzero test scaling.** A nonzero spatial rescaling preserves the test-field conditions. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.isTestField_scale in Breakdown.Weak.SliceIntegrand, line 41. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L41).

**Coordinate partial under two scalings.** A coordinate partial of `cN(by)` is `cb` times the corresponding original partial at `by`. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.partial_scaled in Breakdown.Weak.SliceIntegrand, line 50. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L50).

**Negative Laplacian under two scalings.** The negative Laplacian of `cN(by)` is `cb²` times the original negative Laplacian at `by`. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.negSsp_scaled in Breakdown.Weak.SliceIntegrand, line 54. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L54).

**Derivative of the similarity factor.** The similarity scale has derivative minus one half of itself. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.hasDerivAt_scale in Breakdown.Weak.SliceIntegrand, line 68. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L68).

**Time derivative of the rescaled test.** The rescaled test's time derivative splits into the motion of its spatial argument and the derivative of its time-amplitude factor. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.deriv_scaledTest in Breakdown.Weak.SliceIntegrand, line 73. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L73).

**Pointwise weak similarity integrand.** The stated scaling formulas expand the weak similarity integrand into the time-test derivative, weak-gradient and quadratic-advection terms. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.pointwise in Breakdown.Weak.SliceIntegrand, line 94. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L94).

**The gradient and Hilbert pairings agree.** The velocity-pairing interface identifies the sum of physical partial-derivative pairings with the Hilbert inner product against an embedded test. Source: Breakdown.WeakProfile.Internal.SliceIntegrand.partial_pairing in Breakdown.Weak.SliceIntegrand, line 127. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L127).

**Source namespace:** Breakdown.WeakProfile.

**Discharge the slice-integrand identity.** This theorem proves that the integrated weak similarity expression equals the abstract similarity rate under the stated slice and pairing interfaces. Source: Breakdown.WeakProfile.sliceIntegrand_holds in Breakdown.Weak.SliceIntegrand, line 183. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceIntegrand.lean#L183).

### Breakdown.Weak.SliceMeasurable

This file proves strong measurability of the reconstructed state curve through test pairings and finite-dimensional approximations.

Reading context: §7.10 and Corollary 7.2; a measurable abstract curve from weak slices.

**Source namespace:** Breakdown.WeakProfile.

**Measurable test-state pairings.** A measurable physical weak-slice field gives measurable Hilbert pairings against every embedded test through the velocity-pairing interface. Source: Breakdown.WeakProfile.pairing_test_measurable in Breakdown.Weak.SliceMeasurable, line 12. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceMeasurable.lean#L12).

**Measurable arbitrary-state pairings.** The stated weak-slice data and velocity-pairing interface give measurable pairings against every Hilbert-space vector. Source: Breakdown.WeakProfile.pairing_measurable in Breakdown.Weak.SliceMeasurable, line 27. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceMeasurable.lean#L27).

**Measurable continuous-linear observables.** If all Hilbert inner-product observables are measurable, every continuous linear scalar observable is measurable. Source: Breakdown.WeakProfile.functional_measurable in Breakdown.Weak.SliceMeasurable, line 42. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceMeasurable.lean#L42).

**Measurable finite projections.** Measurability of all continuous linear scalar observables implies measurability after any finite-dimensional continuous linear map. Source: Breakdown.WeakProfile.finiteDim_measurable in Breakdown.Weak.SliceMeasurable, line 49. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceMeasurable.lean#L49).

**Prove slice-curve measurability.** This theorem proves measurability of the abstract slice curve from measurable physical slice data and the velocity-pairing interface. Source: Breakdown.WeakProfile.sliceMeasurable_holds in Breakdown.Weak.SliceMeasurable, line 62. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/SliceMeasurable.lean#L62).

### Breakdown.Weak.StatementsOrbit

This file declares the null-set transfer and physical-curve measurability interfaces used to turn a weak profile into an orbit.

Reading context: §7.10 and Corollary 7.2; interfaces for the profile-to-orbit construction.

**Source namespace:** Breakdown.WeakProfile.

**Null sets under logarithmic time change.** This proposition asks for equivalence of almost-everywhere statements between similarity time and logarithmic physical time on `t < 1`. Source: Breakdown.WeakProfile.TimeChangeNull in Breakdown.Weak.StatementsOrbit, line 18. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsOrbit.lean#L18).

**Measurability after physical time change.** This proposition asks that every measurable similarity curve yield a measurable physical curve on `t < 1`. Source: Breakdown.WeakProfile.PhysicalCurveMeasurable in Breakdown.Weak.StatementsOrbit, line 22. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsOrbit.lean#L22).

### Breakdown.Weak.StatementsSlice

This file declares the pairing, weak-gradient, Fourier reconstruction and dilation interfaces needed to interpret weak physical slices.

Reading context: §7.10 and Corollary 7.2; interfaces for the slice-to-state bridge.

**Source namespace:** Breakdown.WeakProfile.

**Hilbert pairing from physical velocity.** This proposition identifies a Hilbert test pairing with the integral of physical velocity against the test's negative Laplacian. Source: Breakdown.WeakProfile.PairingVelocity in Breakdown.Weak.StatementsSlice, line 12. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsSlice.lean#L12).

**The velocity's prescribed weak gradient.** This proposition requires each abstract partial derivative to be the distributional derivative of the physical velocity. Source: Breakdown.WeakProfile.VelocityWeakGradient in Breakdown.Weak.StatementsSlice, line 16. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsSlice.lean#L16).

**Weak-gradient Fourier reconstruction.** This proposition asks for a Hilbert-space state realizing the three supplied gradient columns of every valid weak slice. Source: Breakdown.WeakProfile.GradientFreqTr in Breakdown.Weak.StatementsSlice, line 27. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsSlice.lean#L27).

**Weak advection integration by parts.** This proposition identifies the quadratic test-derivative integral of the physical velocity with the negative abstract trilinear pairing. Source: Breakdown.WeakProfile.AdvectionByParts in Breakdown.Weak.StatementsSlice, line 38. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsSlice.lean#L38).

**Dilating the Hilbert test pairing.** Assuming the velocity-pairing interface, this proposition transfers positive dilation of a state to inverse square-root spatial scaling of the test. Source: Breakdown.WeakProfile.PairingDilate in Breakdown.Weak.StatementsSlice, line 43. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsSlice.lean#L43).

**Dilating the trilinear test pairing.** Assuming the weak-gradient interface, this proposition transfers dilation of both state inputs to inverse square-root spatial scaling of the physical test. Source: Breakdown.WeakProfile.TrilinearDilate in Breakdown.Weak.StatementsSlice, line 47. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsSlice.lean#L47).

### Breakdown.Weak.StatementsTime

This file declares the measurability, weak-time-derivative and variation-of-constants interfaces needed to recover a mild state curve.

Reading context: §7.10 and Corollary 7.2; interfaces for weak time evolution.

**Source namespace:** Breakdown.WeakProfile.

**Measurability of the slice curve.** Assuming velocity pairing, this proposition asks that measurable physical slice data give a measurable abstract curve realizing them. Source: Breakdown.WeakProfile.SliceMeasurable in Breakdown.Weak.StatementsTime, line 12. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L12).

**Admissibility of rescaled tests.** This proposition asks that the scaled construction turn a compact smooth time test and a spatial test into an admissible spacetime test. Source: Breakdown.WeakProfile.ScaledTestField in Breakdown.Weak.StatementsTime, line 18. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L18).

**The weak integrand is the abstract rate.** Assuming velocity pairing and advection integration by parts, this proposition identifies the integrated weak similarity expression with the abstract similarity rate. Source: Breakdown.WeakProfile.SliceIntegrand in Breakdown.Weak.StatementsTime, line 22. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L22).

**Primitive from a weak time derivative.** This proposition asks that the stated distributional derivative relation yield an almost-everywhere primitive formula with one constant. Source: Breakdown.WeakProfile.ConstOfWeakDeriv in Breakdown.Weak.StatementsTime, line 49. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L49).

**Integrability of bilinear evolution.** This proposition asks for interval integrability of the shifted bilinear interaction along every bounded measurable curve in the stated time window. Source: Breakdown.WeakProfile.BilinIntegrable in Breakdown.Weak.StatementsTime, line 61. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L61).

**Variation of constants in test pairings.** Assuming bilinear integrability, this proposition asks for the heat-regularised variation-of-constants identity between good times against every Hilbert-space test. Source: Breakdown.WeakProfile.VarConstInner in Breakdown.Weak.StatementsTime, line 67. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L67).

**Variation of constants at good times.** Assuming bilinear integrability and the inner-product identity, this proposition asks that variation of constants recover the original curve at ordered good times. Source: Breakdown.WeakProfile.VarConstGood in Breakdown.Weak.StatementsTime, line 75. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L75).

**Continuity of variation of constants.** Assuming bilinear integrability, this proposition asks that variation of constants along a bounded measurable curve be continuous after its chosen initial time. Source: Breakdown.WeakProfile.ContinuousVarConst in Breakdown.Weak.StatementsTime, line 81. [Proposition definition](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/StatementsTime.lean#L81).

### Breakdown.Weak.TrilinearDilate

This file proves the scaling identity for the trilinear advection pairing used after changing from profile to physical variables.

Reading context: §7.10 and Corollary 7.2; rescaling the nonlinear weak term.

**Source namespace:** Breakdown.WeakProfile.

**Discharge trilinear dilation.** This theorem proves the trilinear-dilation interface, conditional on the weak-gradient interface. Source: Breakdown.WeakProfile.trilinearDilate_holds in Breakdown.Weak.TrilinearDilate, line 11. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/TrilinearDilate.lean#L11).

### Breakdown.Weak.VarConstGood

This file combines the scalar pairing identities to obtain variation of constants at the common good times.

Reading context: §7.10 and Corollary 7.2; a state identity on the good-time set.

**Source namespace:** Breakdown.WeakProfile.

**Discharge the good-time Duhamel identity.** This theorem proves that variation of constants equals the original curve at good times under the stated integrability and inner-product interfaces. Source: Breakdown.WeakProfile.varConstGood_holds in Breakdown.Weak.VarConstGood, line 13. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstGood.lean#L13).

### Breakdown.Weak.VarConstInner

This file derives variation of constants after pairing with arbitrary test states and applying the weak-time-derivative identity.

Reading context: §7.10 and Corollary 7.2; scalar recovery of the mild formula.

**Source namespace:** Breakdown.WeakProfile.Internal.VarConstInner.

**Heat commutes with differentiated heat.** For nonnegative first and positive second elapsed times, composing heat with differentiated heat adds the two time parameters. Source: Breakdown.WeakProfile.Internal.VarConstInner.heat_sspHeat in Breakdown.Weak.VarConstInner, line 17. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L17).

**Differentiated heat operator bound.** For positive time, the differentiated heat operator has norm at most `τ⁻¹` times the input norm. Source: Breakdown.WeakProfile.Internal.VarConstInner.norm_sspHeatX_le in Breakdown.Weak.VarConstInner, line 42. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L42).

**Lipschitz heat flow away from zero time.** On times at least `a > 0`, the difference of two heat evolutions is bounded by `a⁻¹‖φ‖` times elapsed-time difference. Source: Breakdown.WeakProfile.Internal.VarConstInner.heat_slope in Breakdown.Weak.VarConstInner, line 47. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L47).

**Quadratic increments force constancy.** On a set dense between the stated endpoints, a uniform quadratic small-increment bound forces the scalar function to have equal endpoint values. Source: Breakdown.WeakProfile.Internal.VarConstInner.chain_const in Breakdown.Weak.VarConstInner, line 57. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L57).

**Bilinear pairing through the heat flow.** At positive elapsed time, the bilinear interaction paired with a test equals the negative trilinear pairing against the differentiated heat test's velocity. Source: Breakdown.WeakProfile.Internal.VarConstInner.bilin_inner in Breakdown.Weak.VarConstInner, line 146. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L146).

**Integrating bounded-curve pairings.** A bounded measurable Hilbert curve has interval-integrable pairings against any fixed vector on each compact inner interval. Source: Breakdown.WeakProfile.Internal.VarConstInner.inner_curve_intervalIntegrable in Breakdown.Weak.VarConstInner, line 153. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L153).

**Bound on the Laplacian-pair rate.** The stated trilinear and norm bounds give `|rate| ≤ MB+KM²(P+B)`. Source: Breakdown.WeakProfile.Internal.VarConstInner.sspRate_bound in Breakdown.Weak.VarConstInner, line 166. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L166).

**Source namespace:** Breakdown.WeakProfile.

**Prove scalar variation of constants.** This theorem proves the heat-regularised variation-of-constants pairing identity at good times under the bilinear-integrability interface. Source: Breakdown.WeakProfile.varConstInner_holds in Breakdown.Weak.VarConstInner, line 190. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VarConstInner.lean#L190).

### Breakdown.Weak.VelocityWeakGradient

This file proves that the physical velocity reconstructed from a state has the prescribed distributional spatial gradient.

Reading context: §7.10 and Corollary 7.2; the weak-gradient identity for physical velocity.

**Source namespace:** Breakdown.WeakProfile.

**Dual exponents six and six-fifths.** The exponents `6/5`, `6`, and `1` form the required Hölder triple. Source: Breakdown.WeakProfile.lpProd_sixFifths_six in Breakdown.Weak.VelocityWeakGradient, line 14. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VelocityWeakGradient.lean#L14).

**Integrable dual-exponent weighted field.** A weight in the Hölder-dual Lq space times an Lp vector field is integrable. Source: Breakdown.WeakProfile.integrable_weight_smul in Breakdown.Weak.VelocityWeakGradient, line 21. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VelocityWeakGradient.lean#L21).

**Norm bound for a weighted field integral.** The norm of a weighted field integral is at most the weight's Lq norm times the vector field's Lp norm under the Hölder hypotheses. Source: Breakdown.WeakProfile.norm_integral_weight_smul_le in Breakdown.Weak.VelocityWeakGradient, line 26. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VelocityWeakGradient.lean#L26).

**Continuous weighted integral functional.** A fixed Hölder-dual weight defines a continuous vector-valued integral map on Lp. Source: Breakdown.WeakProfile.continuous_integral_weight_smul in Breakdown.Weak.VelocityWeakGradient, line 43. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VelocityWeakGradient.lean#L43).

**Weak derivative identity for test fields.** For a scalar test and solenoidal vector test, moving a coordinate derivative between them changes the integral's sign. Source: Breakdown.WeakProfile.byParts_test in Breakdown.Weak.VelocityWeakGradient, line 60. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VelocityWeakGradient.lean#L60).

**Prove the weak-gradient formula.** This theorem proves that abstract coordinate derivatives give the distributional derivatives of the physical velocity. Source: Breakdown.WeakProfile.velocityWeakGradient_holds in Breakdown.Weak.VelocityWeakGradient, line 78. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/VelocityWeakGradient.lean#L78).

### Breakdown.Weak.ZeroGradient

This file proves that an L6 vector field with zero weak gradient vanishes, using mollification to obtain constant smooth representatives.

Reading context: §7.10 and Corollary 7.2; uniqueness of velocity reconstruction from its gradient.

**Source namespace:** Breakdown.WeakProfile.

**Flipped scalar multiplication.** The flipped scalar-multiplication map accepts a vector first and a real scalar second. Source: Breakdown.WeakProfile.smulFlip in Breakdown.Weak.ZeroGradient, line 13. [Private type or notation alias](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L13).

**Evaluating flipped multiplication.** Applying the flipped scalar-multiplication map to a vector and a scalar gives the scalar multiple of that vector. Source: Breakdown.WeakProfile.smulFlip_apply in Breakdown.Weak.ZeroGradient, line 16. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L16).

**A linear map vanishes on a basis.** A linear map that kills all three coordinate unit vectors is zero. Source: Breakdown.WeakProfile.clm_eq_zero_of_unitVector in Breakdown.Weak.ZeroGradient, line 18. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L18).

**Convolution has zero derivative.** If a locally integrable field has zero weak coordinate derivatives, convolution with any scalar test function has zero Fréchet derivative everywhere. Source: Breakdown.WeakProfile.conv_fderiv_eq_zero in Breakdown.Weak.ZeroGradient, line 25. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L25).

**Mollifying a weak constant.** A locally integrable field with zero weak gradient has a convolution with each scalar test function that is constant in space. Source: Breakdown.WeakProfile.conv_const in Breakdown.Weak.ZeroGradient, line 57. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L57).

**Local Hölder bound for the convolution.** The convolution with a compactly supported continuous scalar test is bounded by its L^(6/5) norm times the field's local L6 norm. Source: Breakdown.WeakProfile.conv_enorm_le in Breakdown.Weak.ZeroGradient, line 65. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L65).

**L6 mass escapes translated balls.** For an L6 field, the sixth-power mass in fixed-radius balls translated to infinity along a coordinate axis tends to zero. Source: Breakdown.WeakProfile.ball_lintegral_tendsto in Breakdown.Weak.ZeroGradient, line 94. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L94).

**The mollified weak constant is zero.** For an L6 field with zero weak gradient, convolution with every scalar test function vanishes at the origin. Source: Breakdown.WeakProfile.conv_eq_zero in Breakdown.Weak.ZeroGradient, line 129. [Private proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/Weak/ZeroGradient.lean#L129).
<!-- /passage:sec-breakdown-weak -->

## Solution.lean

<!-- passage:sec-solution-lean -->

### Solution

This export module supplies proofs for the public challenge statements from the assembled library routes.

Reading context: Public conclusion layer; the two uncovered entries here close the earlier-certificate space route and the fractional-certificate space-and-torus route.

**Source namespace:** Breakdown.

**Certificate implies space breakdown.** The supplied theorem derives whole-space breakdown from the earlier certificate hypothesis through the weak-profile route. Source: Breakdown.certificate_breakdown_on_space in Solution, line 295. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L295).

**Fractional certificate breakdown.** For fractional power strictly between one and five quarters, the supplied theorem derives both space and torus breakdown from a fractional certificate hypothesis. Source: Breakdown.fractional_certificate_breakdown in Solution, line 301. [Proved theorem](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Solution.lean#L301).
<!-- /passage:sec-solution-lean -->

