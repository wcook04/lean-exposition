import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegPhysAuxProduct
import Breakdown.Uniqueness.RegPhysAuxPressure
import Breakdown.Uniqueness.RegPhysAuxSmooth

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PowerInternal

theorem norm_freqVec_eq' (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp only [freqVec, complexifyVec, EuclideanSpace.norm_eq, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem memLp_weight_shift' {f : Space → CSpace} {k j : ℕ}
    (hf : MemLp f 1 (weightL1Measure (k + j))) :
    MemLp (fun ξ => ((1 + ‖ξ‖) ^ j : ℝ) • f ξ) 1 (weightL1Measure k) := by
  have hm : AEStronglyMeasurable f volume := hf.1.mono_ac (volume_ac_weight _)
  have hm' : AEStronglyMeasurable (fun ξ => ((1 + ‖ξ‖) ^ j : ℝ) • f ξ) volume := by
    exact (Continuous.aestronglyMeasurable (f := fun ξ : Space => ((1 + ‖ξ‖) ^ j : ℝ))
      (by fun_prop)).smul hm
  rw [memLp_weight_iff hm']
  rw [memLp_weight_iff hm] at hf
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun ξ => ?_)) hf
  have h0 : (0 : ℝ) ≤ 1 + ‖ξ‖ := by positivity
  rw [enorm_smul, Real.enorm_of_nonneg (pow_nonneg h0 j), ← mul_assoc, ← ENNReal.ofReal_mul
    (pow_nonneg h0 k), pow_add]

def unitVec : CSpace := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)

theorem inverseTransform_smul_unitVec (g : Space → ℂ) (x : Space) :
    𝓕⁻ (fun ξ => g ξ • unitVec) x = (𝓕⁻ g x) • unitVec := by
  simp only [Real.fourierInv_eq, Circle.smul_def, smul_smul]
  rw [integral_smul_const]
  simp only [smul_eq_mul]

theorem unitVec_apply_zero (z : ℂ) : (z • unitVec) (0 : Fin 3) = z := by
  simp [unitVec]

theorem aesm_of_unitVec {g : Space → ℂ}
    (h : AEStronglyMeasurable (fun ξ => g ξ • unitVec) volume) : AEStronglyMeasurable g volume := by
  have h2 := (EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable h
  refine h2.congr (Eventually.of_forall fun ξ => ?_)
  exact unitVec_apply_zero (g ξ)

def firstReal : CSpace →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).restrictScalars ℝ)

theorem physScalar_eq_firstReal (g : Space → ℂ) (x : Space) :
    physScalar g x = firstReal (𝓕⁻ (fun ξ => g ξ • unitVec) x) := by
  rw [inverseTransform_smul_unitVec]
  simp [firstReal, physScalar, unitVec]

theorem norm_smul_unitVec (z : ℂ) : ‖z • unitVec‖ = ‖z‖ := by
  rw [norm_smul]
  simp [unitVec]

theorem power_weight_le (α : ℝ) (hα : 0 ≤ α) (hα2 : α < 3 / 2) (ξ : Space) :
    (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 := by
  have hx : (1 : ℝ) ≤ 2 * π * (1 + ‖ξ‖) := by
    have h1 : (1 : ℝ) ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have h2 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    nlinarith
  calc (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π * (1 + ‖ξ‖)) ^ (2 * α) := by
        apply Real.rpow_le_rpow (by positivity) _ (by linarith)
        have : (0 : ℝ) ≤ 2 * π := by positivity
        nlinarith
    _ ≤ (2 * π * (1 + ‖ξ‖)) ^ ((3 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)
    _ = (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 := by rw [Real.rpow_natCast, mul_pow]

theorem memLp_powerSymbol' {α : ℝ} (hα : 0 ≤ α) (hα2 : α < 3 / 2) {f : Space → CSpace} {k : ℕ}
    (hf : MemLp f 1 (weightL1Measure (k + 3))) :
    MemLp (powerSymbol α f) 1 (weightL1Measure k) := by
  have hg := memLp_weight_shift' hf
  have hm : AEStronglyMeasurable f volume := hf.1.mono_ac (volume_ac_weight _)
  have hc : Measurable (fun ξ : Space => (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ)) := by
    fun_prop
  refine hg.of_le_mul (c := (2 * π) ^ 3) ?_ (Eventually.of_forall fun ξ => ?_)
  · exact AEStronglyMeasurable.mono_ac (weight_ac_volume k) (hc.aestronglyMeasurable.smul hm)
  · have h0 : (0 : ℝ) ≤ 1 + ‖ξ‖ := by positivity
    simp only [powerSymbol, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg h0 3)]
    rw [abs_of_nonneg (by positivity)]
    have hb := power_weight_le α hα hα2 ξ
    have hf0 := norm_nonneg (f ξ)
    calc (2 * π * ‖ξ‖) ^ (2 * α) * ‖f ξ‖ ≤ (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 * ‖f ξ‖ :=
          mul_le_mul_of_nonneg_right hb hf0
      _ = (2 * π) ^ 3 * ((1 + ‖ξ‖) ^ 3 * ‖f ξ‖) := by ring

section Curve

variable {T : ℝ} {F : ℝ → Space → CSpace}

theorem memLp_pressure_unitVec (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) :
    MemLp (fun ξ => pressureSymbol (F t) ξ • unitVec) 1 (weightL1Measure k) :=
  memLp_pressureSymbol_single (fun k => memLp_weight_of_curve hF ht k) (hs t ht) k

theorem memLp_gradPressure' (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) :
    MemLp (gradPressureSymbol (F t)) 1 (weightL1Measure k) ∧
      MemLp (fun ξ => pressureSymbol (F t) ξ • freqVec ξ) 1 (weightL1Measure k) := by
  have hp := memLp_pressure_unitVec hF hs ht (k + 1)
  have hg := memLp_weight_shift' (j := 1) hp
  have hm : AEStronglyMeasurable (fun ξ => pressureSymbol (F t) ξ • unitVec) volume :=
    hp.1.mono_ac (volume_ac_weight _)
  have hmp : AEStronglyMeasurable (pressureSymbol (F t)) volume := aesm_of_unitVec hm
  have hfv : Continuous freqVec := complexifyVec.continuous
  have hb : ∀ ξ, ‖pressureSymbol (F t) ξ • freqVec ξ‖ ≤
      1 * ‖((1 + ‖ξ‖) ^ 1 : ℝ) • (pressureSymbol (F t) ξ • unitVec)‖ := by
    intro ξ
    rw [norm_smul, norm_freqVec_eq', one_mul, norm_smul, norm_smul_unitVec, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), pow_one, mul_comm]
    gcongr
    linarith
  have h1 : MemLp (fun ξ => pressureSymbol (F t) ξ • freqVec ξ) 1 (weightL1Measure k) :=
    hg.of_le_mul ((hmp.smul hfv.aestronglyMeasurable).mono_ac (weight_ac_volume k))
      (Eventually.of_forall hb)
  refine ⟨?_, h1⟩
  refine MemLp.ae_eq (Eventually.of_forall fun ξ => ?_) (h1.const_smul (2 * (π : ℂ) * Complex.I))
  simp only [Pi.smul_apply, gradPressureSymbol, smul_smul]

theorem integrable_pressure' (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (pressureSymbol (F t)) := by
  have hp := integrable_of_memLp_weight (memLp_pressure_unitVec hF hs ht 0)
  have h2 := (EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).integrable_comp hp
  refine h2.congr (Eventually.of_forall fun ξ => ?_)
  exact unitVec_apply_zero _

theorem nonlinSymbol_eq' (f : Space → CSpace) (ξ : Space) :
    nonlinSymbol f ξ = -gradPressureSymbol f ξ - advectionSymbol f ξ := by
  have h := timeDerivSymbol_add_advectionSymbol f ξ
  simp only [timeDerivSymbol, sspSymbol] at h
  have h2 : nonlinSymbol f ξ = -gradPressureSymbol f ξ - advectionSymbol f ξ := by
    rw [neg_sub_left]
    rw [eq_neg_iff_add_eq_zero]
    rw [← sub_eq_zero] at h
    rw [← h]
    abel
  exact h2

theorem memLp_nonlin' (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) :
    MemLp (nonlinSymbol (F t)) 1 (weightL1Measure k) := by
  have hg := (memLp_gradPressure' hF hs ht k).1
  have ha := memLp_advectionSymbol (fun k => memLp_weight_of_curve hF ht k) k
  have he : nonlinSymbol (F t) = fun ξ => -gradPressureSymbol (F t) ξ - advectionSymbol (F t) ξ := by
    funext ξ
    exact nonlinSymbol_eq' _ ξ
  rw [he]
  exact hg.neg.sub ha

theorem memLp_powerTimeDeriv' {α : ℝ} (hα : 0 ≤ α) (hα2 : α < 3 / 2)
    (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) :
    MemLp (powerTimeDerivSymbol α (F t)) 1 (weightL1Measure k) := by
  have hp := memLp_powerSymbol' hα hα2 (memLp_weight_of_curve hF ht (k + 3))
  have hn := memLp_nonlin' hF hs ht k
  exact hp.neg.add hn

end Curve

end PowerInternal

open PowerInternal in
theorem powerPhysCurve_of (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) (h1 : PowerWeightCurveStatement α)
    (h2 : PowerPressureCurveStatement α) (h3 : PowerPhysPowerStatement α) :
    PowerPhysCurveStatement α := by
  intro T hT F hF hd hs
  have hα0 : 0 ≤ α := by linarith
  obtain ⟨hder, hsm⟩ := h1 T hT F hF hd hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := contDiffOn_freqTrInv_curve hT (fun t ht k => memLp_weight_of_curve hF ht k) hsm
    exact realVec.contDiff.comp_contDiffOn h
  · have h := contDiffOn_freqTrInv_curve hT
      (c := fun τ ξ => pressureSymbol (F τ) ξ • unitVec)
      (fun t ht k => memLp_pressure_unitVec hF hs ht k) (h2 T hT F hF hd hs)
    have h' := firstReal.contDiff.comp_contDiffOn h
    refine h'.congr fun z _ => ?_
    exact physScalar_eq_firstReal _ _
  · intro t ht x
    have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    have h := hasDerivAt_freqTrInv_curve (k := 0) ht (fun τ hτ => memLp_weight_of_curve hF hτ 0)
      (memLp_powerTimeDeriv' hα0 hα2 hF hs htc 0) (hder 0 t htc) x
    exact realVec.hasFDerivAt.comp_hasDerivAt t h
  · intro t ht
    exact ⟨integrable_of_memLp_weight (memLp_powerTimeDeriv' hα0 hα2 hF hs ht 0),
      integrable_of_memLp_weight (memLp_advectionSymbol (fun k => memLp_weight_of_curve hF ht k) 0),
      integrable_of_memLp_weight (memLp_powerSymbol' hα0 hα2 (memLp_weight_of_curve hF ht (0 + 3))),
      integrable_of_memLp_weight (memLp_gradPressure' hF hs ht 0).1⟩
  · intro t ht x
    exact h3 (F t) (memLp_weight_of_curve hF ht 3) x
  · intro t ht x
    exact gradientAt_physScalar (integrable_pressure' hF hs ht)
      (integrable_of_memLp_weight (memLp_gradPressure' hF hs ht 0).2) x

end Breakdown.SmoothFlow
