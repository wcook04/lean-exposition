import TorusEuler.PhaseJetBounds
import TorusEuler.WaveProfile
import TorusEuler.OscillatoryHierarchySolve
import Mathlib.Analysis.Normed.Module.Normalize

/-!
The pressure estimate of the frozen Lemma 5.9, in
`paper/craik_criminale_rewrite/sections/08_exact_wave.tex`.
The primary Hessian separates the signed phase term from the terms containing
spatial derivatives of the coefficient or of the transported wave vector.
-/

open ContinuousLinearMap InnerProductSpace
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "Hess[" f "]" => fderiv ℝ (gradient f)

/-- At fixed time the coefficient of the primary pressure in the lifted cell. -/
def wavePressureCoefficient (cutoff : ℝ) (κ a : Vec3) (M : Vec3 →L[ℝ] Vec3) : ℝ :=
  2 * cutoff * ⟪κ, M a⟫_ℝ / ‖κ‖ ^ 2

theorem wavePressureCoefficient_eq_neg_oscillatoryPressureSlope
    (cutoff : ℝ) (κ a : Vec3) (M : Vec3 →L[ℝ] Vec3) :
    wavePressureCoefficient cutoff κ a M = -oscillatoryPressureSlope M κ 0 (cutoff • a) := by
  simp only [wavePressureCoefficient, oscillatoryPressureSlope, map_smul,
    inner_zero_right, zero_sub, real_inner_smul_right, neg_div, neg_neg]
  ring

/-- At each fixed label, the actual mean-zero oscillatory pressure of the
primary seed is precisely the profile used in the physical Hessian. -/
theorem oscillatoryPhasePressure_primary_eq (h cutoff : ℝ) (κ a : Vec3)
    (M : Vec3 →L[ℝ] Vec3) :
    oscillatoryPhasePressure M κ (fun _ => 0)
      (fun s => (cutoff * waveProfile h s) • a) =
      fun s => (-wavePressureCoefficient cutoff κ a M) * wavePressurePrimitive h s := by
  let c := -wavePressureCoefficient cutoff κ a M
  have hslope : (fun s => oscillatoryPressureSlope M κ 0 ((cutoff * waveProfile h s) • a)) =
      fun s => c • waveProfile h s := by
    funext s
    simp [c, oscillatoryPressureSlope, wavePressureCoefficient, real_inner_smul_right]
    ring
  unfold oscillatoryPhasePressure wavePressurePrimitive
  rw [hslope]
  funext s
  change phasePrimitive (fun r => c • waveProfile h r) s = c • phasePrimitive (waveProfile h) s
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

private theorem differentiable_gradient {f : Vec3 → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (gradient f) := by
  let R := (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact R.differentiable.comp hdf

private theorem hasGradientAt_wavePressureProduct {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {c phase : Vec3 → ℝ} {x gc κ : Vec3}
    (hc : HasGradientAt c gc x) (hphase : HasGradientAt phase κ x) :
    HasGradientAt (fun y => -(c y * wavePressurePrimitive h (phase y)))
      (-(waveProfile h (phase x) • (c x • κ) + wavePressurePrimitive h (phase x) • gc)) x := by
  have hp := (hasDerivAt_wavePressurePrimitive hh hh₁ (phase x)).comp_hasFDerivAt x
    hphase.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hc.hasFDerivAt.mul hp).neg.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [neg_apply, add_apply, smul_apply, smul_eq_mul, map_neg, map_add, map_smul,
    toDual_apply_apply, Function.comp_apply]
  ring

/-- The exact Eulerian Hessian of the leading pressure, with `phase` the
transported phase and `c` its slowly varying coefficient. -/
theorem wavePrimaryPressure_hessian {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {c phase : Vec3 → ℝ} (hc : ContDiff ℝ 2 c) (hphase : ContDiff ℝ 2 phase)
    (x : Vec3) :
    let κ := gradient phase x
    let gc := gradient c x
    Hess[fun y => -(c y * wavePressurePrimitive h (phase y))] x =
      (-(c x * waveSlope h (phase x))) • rankOne ℝ κ κ -
      waveProfile h (phase x) • (rankOne ℝ gc κ + rankOne ℝ κ gc + c x • Hess[phase] x) -
      wavePressurePrimitive h (phase x) • Hess[c] x := by
  have hc₁ (y : Vec3) := (hc.differentiable (by norm_num) y).hasGradientAt
  have hφ₁ (y : Vec3) := (hphase.differentiable (by norm_num) y).hasGradientAt
  have hgrad := gradient_eq (fun y => hasGradientAt_wavePressureProduct hh hh₁ (hc₁ y) (hφ₁ y))
  rw [hgrad]
  have hg := (differentiable_gradient hc x).hasFDerivAt
  have hk := (differentiable_gradient hphase x).hasFDerivAt
  have hF := (hasDerivAt_waveProfile hh hh₁ (phase x)).comp_hasFDerivAt x
    (hφ₁ x).hasFDerivAt
  have hP := (hasDerivAt_wavePressurePrimitive hh hh₁ (phase x)).comp_hasFDerivAt x
    (hφ₁ x).hasFDerivAt
  change fderiv ℝ (-(waveProfile h ∘ phase • c • gradient phase +
    wavePressurePrimitive h ∘ phase • gradient c)) x = _
  rw [(((hF.smul ((hc₁ x).hasFDerivAt.smul hk)).add (hP.smul hg)).neg).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, add_apply, neg_apply, _root_.smul_apply, rankOne_apply,
    smulRight_apply, smul_eq_mul, toDual_apply_apply, Function.comp_apply, Pi.smul_apply', smul_smul]
  module

/-- At the fixed center the mixed and phase-curvature terms vanish because
the primary velocity profile vanishes at phase zero. -/
theorem wavePrimaryPressure_hessian_center {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {c phase : Vec3 → ℝ} (hc : ContDiff ℝ 2 c) (hphase : ContDiff ℝ 2 phase)
    (hcenter : phase 0 = 0) :
    let κ := gradient phase 0
    Hess[fun y => -(c y * wavePressurePrimitive h (phase y))] 0 =
      (-c 0) • rankOne ℝ κ κ - wavePressurePrimitive h 0 • Hess[c] 0 := by
  have hs : waveSlope h 0 = 1 :=
    (hasDerivAt_waveProfile hh hh₁ 0).unique (hasDerivAt_waveProfile_zero hh hh₁)
  simpa only [hcenter, hs, mul_one, waveProfile_zero, zero_smul, sub_zero]
    using wavePrimaryPressure_hessian hh hh₁ hc hphase 0

/-- The remaining center term is bounded by the profile width times the
slow coefficient Hessian. -/
theorem norm_wavePrimaryPressure_center_remainder_le {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {c phase : Vec3 → ℝ} (hc : ContDiff ℝ 2 c) (hphase : ContDiff ℝ 2 phase)
    (hcenter : phase 0 = 0) :
    let κ := gradient phase 0
    ‖Hess[fun y => -(c y * wavePressurePrimitive h (phase y))] 0 -
      (-c 0) • rankOne ℝ κ κ‖ ≤ h * ‖Hess[c] 0‖ := by
  have hP : ‖wavePressurePrimitive h 0‖ ≤ h := by
    have hb := norm_phasePrimitive_le (contDiff_waveProfile hh hh₁).continuous
      (periodic_waveProfile hh hh₁) (phaseMean_waveProfile hh hh₁)
      (fun s _ => norm_waveProfile_le hh hh₁ s) 0
    change ‖wavePressurePrimitive h 0‖ ≤ 2 * (h / 2) at hb
    linarith
  dsimp only
  rw [wavePrimaryPressure_hessian_center hh hh₁ hc hphase hcenter, sub_right_comm,
    sub_self, zero_sub, norm_neg, norm_smul]
  exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)

/-- The leading Hessian at phase zero is a negative semidefinite rank-one
tensor whenever the coupling coefficient is nonnegative. -/
theorem wavePrimaryPressure_center_leading_nonpos {c : ℝ} (hc : 0 ≤ c) (κ v : Vec3) :
    ⟪v, ((-c) • rankOne ℝ κ κ) v⟫_ℝ ≤ 0 := by
  rw [smul_apply, real_inner_smul_right, rankOne_apply, real_inner_smul_right,
    real_inner_comm v κ, ← pow_two]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _)

/-- In the active support the sign of the coupling makes the upper bound
gain the factor `h` from the small negative tail of the profile slope. -/
theorem wavePrimaryPressure_leading_upper {h c : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hc : 0 ≤ c) (s : ℝ) (κ v : Vec3) :
    ⟪v, ((-(c * waveSlope h s)) • rankOne ℝ κ κ) v⟫_ℝ ≤
      (h / 2 * c * ‖κ‖ ^ 2) * ‖v‖ ^ 2 := by
  rw [smul_apply, real_inner_smul_right, rankOne_apply, real_inner_smul_right,
    real_inner_comm v κ, ← pow_two]
  have hs := (deriv_waveProfile_bounds hh hh₁ s).1
  rw [(hasDerivAt_waveProfile hh hh₁ s).deriv] at hs
  have hc' : -(c * waveSlope h s) ≤ h / 2 * c := by
    have := mul_le_mul_of_nonneg_left hs hc
    linarith
  have hi : ⟪v, κ⟫_ℝ ^ 2 ≤ ‖κ‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [mul_comm (‖κ‖ ^ 2), ← mul_pow, ← sq_abs ⟪v, κ⟫_ℝ]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm v κ) 2
  calc
    _ ≤ (h / 2 * c) * ⟪v, κ⟫_ℝ ^ 2 :=
      mul_le_mul_of_nonneg_right hc' (sq_nonneg _)
    _ ≤ (h / 2 * c) * (‖κ‖ ^ 2 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

theorem wavePressureCoefficient_mul_norm_sq_le
    {cutoff : ℝ} {κ a : Vec3} {M : Vec3 →L[ℝ] Vec3} (hκ : κ ≠ 0)
    (hcutoff : cutoff ∈ Set.Icc (0 : ℝ) 1) (hν : 0 ≤ ⟪κ, M a⟫_ℝ) :
    0 ≤ wavePressureCoefficient cutoff κ a M ∧
      wavePressureCoefficient cutoff κ a M * ‖κ‖ ^ 2 ≤ 2 * ‖κ‖ * ‖M‖ * ‖a‖ := by
  have hk := norm_pos_iff.mpr hκ
  have hcutoff₀ : 0 ≤ cutoff := hcutoff.1
  refine ⟨by unfold wavePressureCoefficient; positivity, ?_⟩
  rw [wavePressureCoefficient, div_mul_cancel₀ _ (pow_ne_zero 2 hk.ne')]
  calc
    _ ≤ 2 * ⟪κ, M a⟫_ℝ := by nlinarith [mul_le_mul_of_nonneg_right hcutoff.2 hν]
    _ ≤ 2 * (‖κ‖ * ‖M a‖) := by
      gcongr
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm κ (M a))
    _ ≤ _ := by
      rw [mul_assoc, mul_assoc]
      gcongr
      exact M.le_opNorm a

private theorem norm_wavePressureGeometricTerms_le (F P c : ℝ) (κ gc : Vec3)
    (Hφ Hc : Vec3 →L[ℝ] Vec3) :
    ‖- (F • (rankOne ℝ gc κ + rankOne ℝ κ gc + c • Hφ)) - P • Hc‖ ≤
      2 * (‖F‖ * ‖gc‖) * ‖κ‖ + (‖F‖ * ‖c‖) * ‖Hφ‖ + ‖P • Hc‖ := by
  rw [norm_sub_rev]
  calc
    _ ≤ ‖P • Hc‖ + ‖-(F • (rankOne ℝ gc κ + rankOne ℝ κ gc + c • Hφ))‖ :=
      norm_sub_le _ _
    _ = ‖P • Hc‖ + ‖F‖ * ‖rankOne ℝ gc κ + rankOne ℝ κ gc + c • Hφ‖ := by
      simp only [norm_neg, norm_smul]
    _ ≤ ‖P • Hc‖ + ‖F‖ * (‖rankOne ℝ gc κ‖ + ‖rankOne ℝ κ gc‖ + ‖c • Hφ‖) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = _ := by
      simp only [norm_rankOne, norm_smul]
      ring

/-- The four geometric terms of the primary Hessian only use one fast
phase derivative. Their individual jet bounds cost at most `√λ`, and at
most one geometric phase coefficient costs `λ`. -/
theorem norm_wavePrimaryPressure_geometricRemainder_le {N B D : ℝ}
    (hN : 1 ≤ N) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (F P c : ℝ) (κ gc : Vec3) (Hφ Hc : Vec3 →L[ℝ] Vec3)
    (hκ : ‖κ‖ ≤ D * N) (hφ : ‖Hφ‖ ≤ D * N)
    (hgc : ‖F‖ * ‖gc‖ ≤ D * Real.sqrt N * B)
    (hF : ‖F‖ * ‖c‖ ≤ D * Real.sqrt N * B)
    (hP : ‖P • Hc‖ ≤ D * B) :
    ‖- (F • (rankOne ℝ gc κ + rankOne ℝ κ gc + c • Hφ)) - P • Hc‖ ≤
      (3 * D ^ 2 + D) * (N * Real.sqrt N * B) := by
  have hroot : 1 ≤ Real.sqrt N := by
    simpa using Real.sqrt_le_sqrt hN
  have hone : 1 ≤ N * Real.sqrt N := by
    exact one_le_mul_of_one_le_of_one_le hN hroot
  have hP' : ‖P • Hc‖ ≤ D * B * (N * Real.sqrt N) :=
    hP.trans (le_mul_of_one_le_right (mul_nonneg hD hB) hone)
  calc
    _ ≤ 2 * (‖F‖ * ‖gc‖) * ‖κ‖ + (‖F‖ * ‖c‖) * ‖Hφ‖ + ‖P • Hc‖ :=
      norm_wavePressureGeometricTerms_le F P c κ gc Hφ Hc
    _ ≤ 2 * (D * Real.sqrt N * B) * (D * N) +
        (D * Real.sqrt N * B) * (D * N) + D * B * (N * Real.sqrt N) := by
      gcongr
    _ = _ := by ring

/-- An upper quadratic-form bound for the total pressure from the primary
one-sided bound and the operator-norm bounds for the primary geometric,
higher oscillatory and mean Hessians. -/
theorem wavePressure_hessian_quadratic_upper {H L G O M : Vec3 →L[ℝ] Vec3}
    {a b c d : ℝ} (hH : H = L + G + O + M)
    (hL : ∀ v, ⟪v, L v⟫_ℝ ≤ a * ‖v‖ ^ 2)
    (hG : ‖G‖ ≤ b) (hO : ‖O‖ ≤ c) (hM : ‖M‖ ≤ d) (v : Vec3) :
    ⟪v, H v⟫_ℝ ≤ (a + b + c + d) * ‖v‖ ^ 2 := by
  have hop (A : Vec3 →L[ℝ] Vec3) {q : ℝ} (hq : ‖A‖ ≤ q) :
      ⟪v, A v⟫_ℝ ≤ q * ‖v‖ ^ 2 := calc
    _ ≤ ‖v‖ * ‖A v‖ := (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    _ ≤ ‖v‖ * (q * ‖v‖) := by
      gcongr
      exact (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
    _ = _ := by ring
  rw [hH]
  simp only [add_apply, inner_add_right, add_mul]
  exact add_le_add (add_le_add (add_le_add (hL v) (hop G hG)) (hop O hO)) (hop M hM)

/-- The first physical derivative of an oscillatory pressure uses the
projected transverse source and one slow label derivative of the pressure. -/
theorem hasGradientAt_transportedOscillatoryPressure {A : Velocity}
    {p : ℝ → Vec3 → ℝ → ℝ} {t : ℝ} {x k src V : Vec3}
    {Ax M : Vec3 →L[ℝ] Vec3} {fa : Vec3 →L[ℝ] ℝ}
    (hA : HasFDerivAt (A t) Ax x)
    (hp : HasFDerivAt (fun z : Vec3 × ℝ => p t z.1 z.2)
      (fa.coprod (toSpanSingleton ℝ
        (oscillatoryPressureSlope M (Ax.adjoint k) src V))) (A t x, ⟪k, A t x⟫_ℝ)) :
    let κ := Ax.adjoint k
    HasGradientAt (transportedProfile A k p t)
      (Ax.adjoint ((InnerProductSpace.toDual ℝ Vec3).symm fa) +
        (‖κ‖ ^ 2)⁻¹ • rankOne ℝ κ κ (src - (2 : ℝ) • M V)) x := by
  let κ := Ax.adjoint k
  let g := (InnerProductSpace.toDual ℝ Vec3).symm fa
  have hg : innerSL ℝ g = fa := (InnerProductSpace.toDual ℝ Vec3).apply_symm_apply fa
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hasFDerivAt_transportedProfile hA hp).congr_fderiv ?_
  have hproj : oscillatoryPressureSlope M κ src V • κ =
      (‖κ‖ ^ 2)⁻¹ • rankOne ℝ κ κ (src - (2 : ℝ) • M V) := by
    simp only [oscillatoryPressureSlope, rankOne_apply, inner_sub_right, real_inner_smul_right,
      smul_smul, div_eq_mul_inv]
    rw [mul_comm]
  rw [← hproj]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, comp_apply, smulRight_apply, innerSL_apply_apply,
    toDual_apply_apply, inner_add_left, real_inner_smul_left, adjoint_inner_left]
  have hfa : fa (Ax v) = ⟪g, Ax v⟫_ℝ := by rw [← hg]; rfl
  rw [hfa]
  simp only [κ, adjoint_inner_left, smul_eq_mul, mul_comm, g]

/-- One physical derivative of the exact gradient profile gives the
higher oscillatory Hessian at the phase-graph point. -/
theorem norm_higherOscillatory_hessian_le {A : Velocity} {k : Vec3}
    {t ℓ h C budget : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    {p : Vec3 → ℝ} {G : ℝ → Vec3 → ℝ → Vec3}
    (hℓ : 0 < ℓ) (hh : 0 < h) (hC : 0 ≤ C) (hbudget : 0 ≤ budget)
    (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hGreg : ContDiff ℝ ∞ (Function.uncurry (G t)))
    (hcoeff : ∀ j ≤ 1, ∀ a, ℓ ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C)
    (hG : PhaseJetBound 1 budget (scaledPhaseProfile ℓ h (G t)))
    (hgrad : gradient p = transportedProfile A k G t) (x : Vec3) :
    ‖Hess[p] x‖ ≤ 6 * ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C) * budget := by
  have H := norm_iteratedFDeriv_transportedProfile_le
    (k := k) (γ := 1) (M := budget) hℓ hh hC zero_le_one hbudget hA hB hBreg hGreg 1 hcoeff
    (by simpa only [one_mul] using hG) x
  rw [norm_iteratedFDeriv_one, ← hgrad] at H
  simpa only [pow_one, one_mul, ← mul_assoc, show (3 : ℝ) * 2 = 6 by norm_num] using H

/-- The hierarchy supplies a gradient budget of order `λ^(-23/12)`.
One physical derivative costs `λ^(3/2)`, leaving the claimed negative Hessian
exponent. -/
theorem norm_higherOscillatory_hessian_le_at_hierarchy_scale {A : Velocity} {k : Vec3}
    {t ℓ h C budget N K D : ℝ} {B : Vec3 → Vec3 →L[ℝ] Vec3}
    {p : Vec3 → ℝ} {G : ℝ → Vec3 → ℝ → Vec3}
    (hN : 0 < N) (hℓ : 0 < ℓ) (hh : 0 < h) (hC : 0 ≤ C) (hbudget : 0 ≤ budget)
    (hA : ContDiff ℝ ∞ (A t))
    (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x) (hBreg : ContDiff ℝ ∞ B)
    (hGreg : ContDiff ℝ ∞ (Function.uncurry (G t)))
    (hcoeff : ∀ j ≤ 1, ∀ a, ℓ ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C)
    (hG : PhaseJetBound 1 budget (scaledPhaseProfile ℓ h (G t)))
    (hgrad : gradient p = transportedProfile A k G t)
    (hcost : 6 * ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C) ≤ D * N ^ (3 / 2 : ℝ))
    (hjet : budget ≤ K * N ^ (-23 / 12 : ℝ)) (x : Vec3) :
    ‖Hess[p] x‖ ≤ D * K * N ^ (-5 / 12 : ℝ) := by
  have hcost₀ : 0 ≤ 6 * ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C) := by positivity
  calc
    _ ≤ 6 * ((ℓ⁻¹ + h⁻¹ * ‖k‖) * C) * budget :=
      norm_higherOscillatory_hessian_le hℓ hh hC hbudget hA hB hBreg hGreg hcoeff hG hgrad x
    _ ≤ (D * N ^ (3 / 2 : ℝ)) * (K * N ^ (-23 / 12 : ℝ)) :=
      mul_le_mul hcost hjet hbudget (hcost₀.trans hcost)
    _ = _ := by
      rw [show (-5 / 12 : ℝ) = 3 / 2 + (-23 / 12) by norm_num, Real.rpow_add hN]
      ring

/-- The actual coefficient, wave vector and amplitude scales yield the
`λ^(-1/4)` one-sided bound for the primary phase term of Lemma 5.9. -/
theorem wavePrimaryPressure_leading_upper_of_scale {N D cutoff : ℝ} (hN : 1 ≤ N)
    {κ a : Vec3} {M : Vec3 →L[ℝ] Vec3} (hκ : κ ≠ 0)
    (hcutoff : cutoff ∈ Set.Icc (0 : ℝ) 1) (hν : 0 ≤ ⟪κ, M a⟫_ℝ)
    (hκScale : ‖κ‖ ≤ D ^ 2 * N) (hM : ‖M‖ ≤ D)
    (ha : ‖a‖ ≤ 2 * N ^ (-3 / 4 : ℝ)) (s : ℝ) (v : Vec3) :
    let c := wavePressureCoefficient cutoff κ a M
    let h := N ^ (-1 / 2 : ℝ)
    ⟪v, ((-(c * waveSlope h s)) • rankOne ℝ κ κ) v⟫_ℝ ≤
      (2 * D ^ 3 * N ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  let c := wavePressureCoefficient cutoff κ a M
  let h := N ^ (-1 / 2 : ℝ)
  have hN₀ : 0 < N := by linarith
  have hD : 0 ≤ D := (norm_nonneg _).trans hM
  have hh : 0 < h := Real.rpow_pos_of_pos hN₀ _
  have hh₁ : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  obtain ⟨hc, hck⟩ := wavePressureCoefficient_mul_norm_sq_le hκ hcutoff hν
  have hcScale : c * ‖κ‖ ^ 2 ≤ 4 * D ^ 3 * N ^ (1 / 4 : ℝ) := calc
    _ ≤ 2 * ‖κ‖ * ‖M‖ * ‖a‖ := hck
    _ ≤ 2 * (D ^ 2 * N) * D * (2 * N ^ (-3 / 4 : ℝ)) := by gcongr
    _ = _ := by
      rw [show (1 / 4 : ℝ) = 1 + (-3 / 4) by norm_num, Real.rpow_add hN₀, Real.rpow_one]
      ring
  have heq : h / 2 * (4 * D ^ 3 * N ^ (1 / 4 : ℝ)) =
      2 * D ^ 3 * N ^ (-1 / 4 : ℝ) := by
    rw [show (-1 / 4 : ℝ) = (-1 / 2 : ℝ) + 1 / 4 by norm_num, Real.rpow_add hN₀]
    dsimp [h]
    ring
  change ⟪v, ((-(c * waveSlope h s)) • rankOne ℝ κ κ) v⟫_ℝ ≤ _
  refine (wavePrimaryPressure_leading_upper hh hh₁ hc s κ v).trans ?_
  change h / 2 * c * ‖κ‖ ^ 2 * ‖v‖ ^ 2 ≤ _
  rw [mul_assoc (h / 2) c, ← heq]
  gcongr

/-- At the center the coefficient has the signed strength–coupling
normalization used in the central pressure identity. -/
theorem wavePressureCoefficient_center_rankOne (cutoff : ℝ) {κ a : Vec3} (hκ : κ ≠ 0) (ha : a ≠ 0)
    (M : Vec3 →L[ℝ] Vec3) :
    let kUnit := NormedSpace.normalize κ
    let aUnit := NormedSpace.normalize a
    (-wavePressureCoefficient cutoff κ a M) • rankOne ℝ κ κ =
      (-(2 * cutoff * (‖a‖ * ‖κ‖) * ⟪kUnit, M aUnit⟫_ℝ)) • rankOne ℝ kUnit kUnit := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro v
  simp only [wavePressureCoefficient, NormedSpace.normalize, smul_apply,
    rankOne_apply, map_smul, real_inner_smul_left, real_inner_smul_right, smul_smul]
  apply congrArg (fun r : ℝ => r • κ)
  field_simp [(norm_ne_zero_iff.mpr hκ), (norm_ne_zero_iff.mpr ha)]

/-- The pressure geometric remainder at the primary hierarchy scale. The
geometric terms have norm of order `λ^(-3/4)`. -/
theorem norm_wavePrimaryPressure_geometricRemainder_le_at_hierarchy_scale
    {N B D K : ℝ} (hN : 1 ≤ N) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbudget : B ≤ K * N ^ (-9 / 4 : ℝ))
    (F P c : ℝ) (κ gc : Vec3) (Hφ Hc : Vec3 →L[ℝ] Vec3)
    (hκ : ‖κ‖ ≤ D * N) (hφ : ‖Hφ‖ ≤ D * N)
    (hgc : ‖F‖ * ‖gc‖ ≤ D * Real.sqrt N * B)
    (hF : ‖F‖ * ‖c‖ ≤ D * Real.sqrt N * B)
    (hP : ‖P • Hc‖ ≤ D * B) :
    ‖- (F • (rankOne ℝ gc κ + rankOne ℝ κ gc + c • Hφ)) - P • Hc‖ ≤
      ((3 * D ^ 2 + D) * K) * N ^ (-3 / 4 : ℝ) := by
  have hN₀ : 0 < N := by linarith
  calc
    _ ≤ (3 * D ^ 2 + D) * (N * Real.sqrt N * B) :=
      norm_wavePrimaryPressure_geometricRemainder_le hN hB hD F P c κ gc Hφ Hc
        hκ hφ hgc hF hP
    _ ≤ (3 * D ^ 2 + D) * (N * Real.sqrt N * (K * N ^ (-9 / 4 : ℝ))) := by gcongr
    _ = _ := by
      rw [Real.sqrt_eq_rpow, show (-3 / 4 : ℝ) = 1 + 1 / 2 + (-9 / 4) by norm_num,
        Real.rpow_add hN₀, Real.rpow_add hN₀, Real.rpow_one]
      ring

/-- The four pressure contributions in the order of the proof of (5.49).
The higher oscillatory Hessian carries the decay from its gradient, and
the mean Hessian carries the decay from the mean equation. -/
theorem wavePressure_hessian_upper_of_scales {H L G O M : Vec3 →L[ℝ] Vec3}
    {N a b c d : ℝ} (hN : 1 ≤ N)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hH : H = L + G + O + M)
    (hL : ∀ v, ⟪v, L v⟫_ℝ ≤ (a * N ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
    (hG : ‖G‖ ≤ b * N ^ (-3 / 4 : ℝ))
    (hO : ‖O‖ ≤ c * N ^ (-5 / 12 : ℝ))
    (hM : ‖M‖ ≤ d * N ^ (-5 / 2 : ℝ)) (v : Vec3) :
    ⟪v, H v⟫_ℝ ≤ ((a + b + c + d) * N ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  have hG' := hG.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN (show (-3 / 4 : ℝ) ≤ -1 / 4 by norm_num)) hb)
  have hO' := hO.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN (show (-5 / 12 : ℝ) ≤ -1 / 4 by norm_num)) hc)
  have hM' := hM.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN (show (-5 / 2 : ℝ) ≤ -1 / 4 by norm_num)) hd)
  simpa only [add_mul] using wavePressure_hessian_quadratic_upper hH hL hG' hO' hM' v

end

end TorusEuler
