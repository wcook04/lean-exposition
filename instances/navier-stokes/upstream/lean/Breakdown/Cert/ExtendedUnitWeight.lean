import Breakdown.Cert.ExtendedNodes

open MeasureTheory

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedUnitWeight

theorem isRightSide_of_smul_actuator {k : ℕ} {W : ℝ → Space → Space}
    {b : Fin k → ℝ → Space → Space} {κ : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {g F : ℝ → Space → Space} (c : ℝ)
    (h : IsRightSide W (fun i σ y => c • b i σ y) κ v G g F) :
    IsRightSide W b (fun i => c * κ i) v G g F := by
  intro φ hφ
  rw [h φ hφ]
  have e : ∀ z : ℝ × Space, ∑ i, κ i • (c • b i z.1 z.2) = ∑ i, (c * κ i) • b i z.1 z.2 :=
    fun z => Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
  simp only [e]

theorem sum_smul_scale {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) (m : Fin k → ℝ) (x : Fin k → Space) :
    ∑ i, (μ * m i) • ((1 / μ) • x i) = ∑ i, m i • x i :=
  Finset.sum_congr rfl fun i _ => by
    rw [smul_smul]
    congr 1
    field_simp

theorem periodPairing_smul_left (c : ℝ) (F M : ℝ → Space → Space) :
    periodPairing (fun σ y => c • F σ y) M = c * periodPairing F M := by
  unfold periodPairing
  simp only [real_inner_smul_left, integral_const_mul]

theorem vecNorm_smul {k : ℕ} (c : ℝ) (x : Fin k → ℝ) : vecNorm (c • x) = |c| * vecNorm x := by
  unfold vecNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

variable {k : ℕ} (d : ExtendedCertificateData k)

theorem defect_withUnitWeight (hμ : d.multiplierWeight ≠ 0) :
    d.withUnitWeight.defect = d.defect := by
  funext q σ y
  show weakDefectField (d.period q) (d.profile q) (d.profileSecondDeriv q) (d.pressureGrad q)
      (fun i σ y => (1 / d.multiplierWeight) • d.actuator i σ y)
      (fun i => d.multiplierWeight * d.multiplier q i) σ y =
    weakDefectField (d.period q) (d.profile q) (d.profileSecondDeriv q) (d.pressureGrad q)
      d.actuator (d.multiplier q) σ y
  simp only [weakDefectField, sum_smul_scale hμ]

theorem frame_multiplier_withUnitWeight (hμ : d.multiplierWeight ≠ 0) (q : Fin k → ℝ) (j : Fin k) :
    ∑ i, d.withUnitWeight.frame i j * d.withUnitWeight.multiplier q i =
      ∑ i, d.frame i j * d.multiplier q i :=
  Finset.sum_congr rfl fun i _ => by
    show ((1 / d.multiplierWeight) • d.frame) i j * (d.multiplierWeight * d.multiplier q i) = _
    rw [Matrix.smul_apply, smul_eq_mul]
    field_simp

theorem adjustedMultiplier_withUnitWeight (hμ : d.multiplierWeight ≠ 0) :
    d.withUnitWeight.adjustedMultiplier = d.adjustedMultiplier := by
  funext q j
  unfold ExtendedCertificateData.adjustedMultiplier
  rw [frame_multiplier_withUnitWeight d hμ, defect_withUnitWeight d hμ]
  rfl

theorem actuatorAdjointError_withUnitWeight (q : Fin k → ℝ) (j : Fin k) :
    d.withUnitWeight.actuatorAdjointError q j =
      (1 / d.multiplierWeight) • d.actuatorAdjointError q j := by
  funext l
  show periodPairing (fun σ y => (1 / d.multiplierWeight) • d.actuator l σ y) (d.adjoint j q)
      - ((1 / d.multiplierWeight) • d.frame) l j =
    (1 / d.multiplierWeight) * (periodPairing (d.actuator l) (d.adjoint j q) - d.frame l j)
  rw [periodPairing_smul_left, Matrix.smul_apply, smul_eq_mul, mul_sub]

theorem actuator_norm_withUnitWeight (i : Fin k) :
    periodLIntegral (fun σ y => ‖(1 / d.multiplierWeight) • d.actuator i σ y‖ ^ 2) =
      ENNReal.ofReal ((1 / d.multiplierWeight) ^ 2) *
        periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) := by
  unfold periodLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext σ
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext y
  dsimp only
  rw [← ENNReal.ofReal_mul (sq_nonneg _), norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

end Internal.ExtendedUnitWeight

open Internal.ExtendedUnitWeight in
theorem extendedUnitWeightHolds : ExtendedUnitWeightHolds := by
  intro k d hd
  have hμ : 0 < d.multiplierWeight := hd.multiplierWeight_pos
  have hμne : d.multiplierWeight ≠ 0 := hμ.ne'
  exact
  { radius_nonneg := hd.radius_nonneg
    stiffRadius_nonneg := hd.stiffRadius_nonneg
    scale_ne_zero := hd.scale_ne_zero
    weight_pos := hd.weight_pos
    weightFn_measurable := hd.weightFn_measurable
    weightFn_lower := hd.weightFn_lower
    weightFn_upper := hd.weightFn_upper
    weightFn_invariant := hd.weightFn_invariant
    multiplierWeight_pos := one_pos
    coerciveL2_nonneg := hd.coerciveL2_nonneg
    coercivePin_nonneg := hd.coercivePin_nonneg
    rowBound_nonneg := hd.rowBound_nonneg
    gapSize_nonneg := hd.gapSize_nonneg
    formShift_nonneg := hd.formShift_nonneg
    transfer_lt := hd.transfer_lt
    coerciveTotal_ge := hd.coerciveTotal_ge
    coerciveTotal_pos := hd.coerciveTotal_pos
    actuatorBound_nonneg := div_nonneg hd.actuatorBound_nonneg hμ.le
    modelFormBound_nonneg := hd.modelFormBound_nonneg
    formBound_ge := hd.formBound_ge
    sizeBound_nonneg := hd.sizeBound_nonneg
    supBound_pos := hd.supBound_pos
    period_continuous := hd.period_continuous
    period_pos := hd.period_pos
    period_le := hd.period_le
    twist_pos := hd.twist_pos
    twist_mem := hd.twist_mem
    multiplier_continuous := by
      show ContinuousOn (fun q i => d.multiplierWeight * d.multiplier q i) d.params
      exact hd.multiplier_continuous.const_smul d.multiplierWeight
    target_continuous := hd.target_continuous
    profile_smooth := hd.profile_smooth
    profile_periodic := hd.profile_periodic
    profile_divergence := hd.profile_divergence
    profile_decay := hd.profile_decay
    profileSecondDeriv_measurable := hd.profileSecondDeriv_measurable
    profileSecondDeriv_periodic := hd.profileSecondDeriv_periodic
    profileSecondDeriv_weak := hd.profileSecondDeriv_weak
    profile_invariant := hd.profile_invariant
    pressureGrad_measurable := hd.pressureGrad_measurable
    pressureGrad_periodic := hd.pressureGrad_periodic
    pressureGrad_orthogonal := hd.pressureGrad_orthogonal
    actuator_measurable := fun i => (hd.actuator_measurable i).const_smul (1 / d.multiplierWeight)
    actuator_periodic := by
      intro i σ y
      show (1 / d.multiplierWeight) • d.actuator i (σ + 1) y =
        (1 / d.multiplierWeight) • d.actuator i σ y
      rw [hd.actuator_periodic i σ y]
    actuator_invariant := by
      intro i γ hγ
      filter_upwards [hd.actuator_invariant i γ hγ] with z hz
      show (1 / d.multiplierWeight) • d.actuator i (z.1 + γ.2) (γ.1 z.2) =
        γ.1 ((1 / d.multiplierWeight) • d.actuator i z.1 z.2)
      rw [hz, map_smul]
    actuator_norm := by
      show ∑ i, periodLIntegral (fun σ y => ‖(1 / d.multiplierWeight) • d.actuator i σ y‖ ^ 2) ≤
        ENNReal.ofReal ((d.actuatorBound / d.multiplierWeight) ^ 2)
      simp only [actuator_norm_withUnitWeight d]
      rw [← Finset.mul_sum]
      calc _ ≤ ENNReal.ofReal ((1 / d.multiplierWeight) ^ 2) * ENNReal.ofReal (d.actuatorBound ^ 2) :=
            mul_le_mul_of_nonneg_left hd.actuator_norm zero_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 1
          ring
    pin_measurable := hd.pin_measurable
    pin_finite := hd.pin_finite
    model_smooth := hd.model_smooth
    model_periodic := hd.model_periodic
    gap_transfer := hd.gap_transfer
    form_shift := hd.form_shift
    rowField_measurable := hd.rowField_measurable
    rowField_periodic := hd.rowField_periodic
    rowField_finite := hd.rowField_finite
    rowField_orthonormal := hd.rowField_orthonormal
    rowWeight_nonneg := hd.rowWeight_nonneg
    rowWeight_le := hd.rowWeight_le
    coercive := by
      intro q hq v G H g hP κ F hF hper hfin hR
      have hR' := isRightSide_of_smul_actuator (b := d.actuator) (1 / d.multiplierWeight) hR
      have h := hd.coercive q hq v G H g hP _ F hF hper hfin hR'
      show Real.sqrt (weightedEnergy d.weightFn G H + 1 ^ 2 * ∑ i, κ i ^ 2) ≤
        d.coerciveL2 * periodNorm F + d.rows F + d.coercivePin * vecNorm (fun i => pinValue (d.pin i) G)
      convert h using 3
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    frozen_form := hd.frozen_form
    defect_nonneg := hd.defect_nonneg
    defect_l2 := by
      intro q hq
      rw [defect_withUnitWeight d hμne]
      exact hd.defect_l2 q hq
    defect_rows := by
      intro q hq
      rw [defect_withUnitWeight d hμne]
      exact hd.defect_rows q hq
    defect_le := hd.defect_le
    size := hd.size
    small_first := hd.small_first
    small_second := by
      show 4 * d.sizeBound ^ 2 * ((1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound)
          + 2 * (d.periodMax / d.twist) * (d.actuatorBound / d.multiplierWeight / 1)
          + 2 * (d.periodMax / d.twist) / d.coerciveTotal) ≤ d.supBound ^ 2
      rw [div_one]
      exact hd.small_second
    small_third := by
      show 4 * (1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound) * d.sizeBound ^ 2
          + 4 * (d.periodMax / d.twist) * d.sizeBound * (d.defectMax
            + 2 * supBoundFactor d.weight * d.sizeBound * d.supBound
            + 2 * (d.actuatorBound / d.multiplierWeight / 1) * d.sizeBound) ≤ d.supBound ^ 2
      rw [div_one]
      exact hd.small_third
    frame_unit := by
      show IsUnit ((1 / d.multiplierWeight) • d.frame)
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
      exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (one_div_ne_zero hμne))).mul
        ((Matrix.isUnit_iff_isUnit_det _).mp hd.frame_unit)
    adjoint_measurable := hd.adjoint_measurable
    adjoint_periodic := hd.adjoint_periodic
    adjoint_l2 := hd.adjoint_l2
    adjointL2_nonneg := hd.adjointL2_nonneg
    adjointDefect_nonneg := hd.adjointDefect_nonneg
    adjointQuad_nonneg := hd.adjointQuad_nonneg
    adjoint_quadratic := hd.adjoint_quadratic
    adjoint_defect := by
      intro j hj q hq v G H g hP F hF hper hfin hR
      have hR' := isRightSide_of_smul_actuator (b := d.actuator) (1 / d.multiplierWeight) hR
      have h0 : (fun i => 1 / d.multiplierWeight * (0 : Fin k → ℝ) i) = 0 := by
        funext i
        simp
      rw [h0] at hR'
      exact hd.adjoint_defect j hj q hq v G H g hP F hF hper hfin hR'
    adjoint_offset := by
      intro j hj q hq
      rw [adjustedMultiplier_withUnitWeight d hμne]
      exact hd.adjoint_offset j hj q hq
    adjoint_inclusion := by
      intro j hj q hq
      show d.adjointQuad j * (2 * d.sizeBound) ^ 2 + 2 * d.sizeBound * Real.sqrt (d.adjointDefect j ^ 2
          + (vecNorm (d.withUnitWeight.actuatorAdjointError q j) / 1) ^ 2) + d.adjointOffset j ≤
        |d.scale j| * d.radius j
      rw [actuatorAdjointError_withUnitWeight, vecNorm_smul, abs_of_pos (one_div_pos.mpr hμ),
        div_one, one_div_mul_eq_div]
      exact hd.adjoint_inclusion j hj q hq
    stiffNorm_nonneg := div_nonneg hd.stiffNorm_nonneg hμ.le
    stiff_norm := by
      intro x
      have e : ∀ j, ∑ i, d.withUnitWeight.frame i j * x i =
          1 / d.multiplierWeight * ∑ i, d.frame i j * x i := by
        intro j
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show ((1 / d.multiplierWeight) • d.frame) i j * x i = _
        rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      simp only [e, mul_pow]
      rw [← Finset.mul_sum]
      show _ ≤ (d.stiffNorm / d.multiplierWeight) ^ 2 * ∑ i, x i ^ 2
      calc _ ≤ (1 / d.multiplierWeight) ^ 2 * (d.stiffNorm ^ 2 * ∑ i, x i ^ 2) :=
            mul_le_mul_of_nonneg_left (hd.stiff_norm x) (sq_nonneg _)
        _ = _ := by ring
    stiff_offset := by
      intro q hq
      simp only [frame_multiplier_withUnitWeight d hμne]
      exact hd.stiff_offset q hq
    stiff_inclusion := by
      show 2 * d.sizeBound * (d.stiffNorm / d.multiplierWeight) / 1 + d.stiffOffset ≤ d.stiffRadius
      rw [div_one, ← mul_div_assoc]
      exact hd.stiff_inclusion
    nontrivial := hd.nontrivial }

end Breakdown.Cert
