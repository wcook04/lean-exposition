import Breakdown.Uniqueness.RegPhysAuxProduct
import Breakdown.Uniqueness.RegPhysAuxPressure
import Breakdown.Uniqueness.RegPhysAuxSmooth

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem norm_freqVec_eq (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp only [freqVec, complexifyVec, EuclideanSpace.norm_eq, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem memLp_weight_shift {f : Space → CSpace} {k j : ℕ} (hf : MemLp f 1 (weightL1Measure (k + j))) :
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

private def singleVec : CSpace := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)

private theorem freqTrInv_smul_single (g : Space → ℂ) (x : Space) :
    𝓕⁻ (fun ξ => g ξ • singleVec) x = (𝓕⁻ g x) • singleVec := by
  simp only [Real.fourierInv_eq, Circle.smul_def, smul_smul]
  rw [integral_smul_const]
  simp only [smul_eq_mul]

private theorem single_apply_zero (z : ℂ) : (z • singleVec) (0 : Fin 3) = z := by
  simp [singleVec]

private theorem aesm_of_single {g : Space → ℂ}
    (h : AEStronglyMeasurable (fun ξ => g ξ • singleVec) volume) : AEStronglyMeasurable g volume := by
  have h2 := (EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable h
  refine h2.congr (Eventually.of_forall fun ξ => ?_)
  exact single_apply_zero (g ξ)

private def firstRe : CSpace →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).restrictScalars ℝ)

private theorem physScalar_eq (g : Space → ℂ) (x : Space) :
    physScalar g x = firstRe (𝓕⁻ (fun ξ => g ξ • singleVec) x) := by
  rw [freqTrInv_smul_single]
  simp [firstRe, physScalar, singleVec]

private theorem pressure_single_eq (f : Space → CSpace) :
    (fun ξ => pressureSymbol f ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) =
      fun ξ => pressureSymbol f ξ • singleVec := rfl

section Curve

variable {T : ℝ} {F : ℝ → Space → CSpace}

theorem smooth_physField_curve (hT : 0 < T) (hF : ∀ m, IsHsCurve m F 0 T)
    (hd : IsVarConstSymbol F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physField (F z.1) z.2) (Icc 0 T ×ˢ univ) := by
  have h := contDiffOn_freqTrInv_curve hT (fun t ht k => memLp_weight_of_curve hF ht k)
    (contDiffOn_toWeightL1 hT hF hd hs)
  exact realVec.contDiff.comp_contDiffOn h

theorem smooth_pressure_curve (hT : 0 < T) (hF : ∀ m, IsHsCurve m F 0 T)
    (hd : IsVarConstSymbol F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physScalar (pressureSymbol (F z.1)) z.2)
      (Icc 0 T ×ˢ univ) := by
  have h := contDiffOn_freqTrInv_curve hT
    (c := fun τ ξ => pressureSymbol (F τ) ξ • singleVec)
    (fun t ht k => memLp_pressureSymbol_single (fun k => memLp_weight_of_curve hF ht k) (hs t ht) k)
    (contDiffOn_toWeightL1_pressureSingle hT hF hd hs)
  have h2 := firstRe.contDiff.comp_contDiffOn h
  refine h2.congr fun z _ => ?_
  exact physScalar_eq _ _

private theorem memLp_sspSymbol {f : Space → CSpace} {k : ℕ} (hf : MemLp f 1 (weightL1Measure (k + 2))) :
    MemLp (sspSymbol f) 1 (weightL1Measure k) := by
  have hg := memLp_weight_shift hf
  have hm : AEStronglyMeasurable f volume := hf.1.mono_ac (volume_ac_weight _)
  refine hg.of_le_mul (c := 4 * π ^ 2) ?_ (Eventually.of_forall fun ξ => ?_)
  · refine AEStronglyMeasurable.mono_ac (weight_ac_volume k) ?_
    exact (Continuous.aestronglyMeasurable (f := fun ξ : Space => (((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ))
      (by fun_prop)).neg.smul hm
  · have h0 : (0 : ℝ) ≤ 1 + ‖ξ‖ := by positivity
    simp only [sspSymbol, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg h0 2)]
    rw [abs_of_nonneg (by positivity)]
    have : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 := by gcongr; linarith
    have hf0 := norm_nonneg (f ξ)
    have hp : 0 ≤ 4 * π ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hp]

private theorem memLp_pressure_single_curve (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) :
    MemLp (fun ξ => pressureSymbol (F t) ξ • singleVec) 1 (weightL1Measure k) :=
  memLp_pressureSymbol_single (fun k => memLp_weight_of_curve hF ht k) (hs t ht) k

private theorem norm_smul_singleVec (z : ℂ) : ‖z • singleVec‖ = ‖z‖ := by
  rw [norm_smul]
  simp [singleVec]

private theorem memLp_gradPressure_curve (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) :
    MemLp (gradPressureSymbol (F t)) 1 (weightL1Measure k) ∧
      MemLp (fun ξ => pressureSymbol (F t) ξ • freqVec ξ) 1 (weightL1Measure k) := by
  have hp := memLp_pressure_single_curve hF hs ht (k + 1)
  have hg := memLp_weight_shift (j := 1) hp
  have hm : AEStronglyMeasurable (fun ξ => pressureSymbol (F t) ξ • singleVec) volume :=
    hp.1.mono_ac (volume_ac_weight _)
  have hmp : AEStronglyMeasurable (pressureSymbol (F t)) volume := aesm_of_single hm
  have hfv : Continuous freqVec := complexifyVec.continuous
  have hb : ∀ ξ, ‖pressureSymbol (F t) ξ • freqVec ξ‖ ≤
      1 * ‖((1 + ‖ξ‖) ^ 1 : ℝ) • (pressureSymbol (F t) ξ • singleVec)‖ := by
    intro ξ
    rw [norm_smul, norm_freqVec_eq, one_mul, norm_smul, norm_smul_singleVec, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), pow_one, mul_comm]
    gcongr
    linarith
  have h1 : MemLp (fun ξ => pressureSymbol (F t) ξ • freqVec ξ) 1 (weightL1Measure k) :=
    hg.of_le_mul ((hmp.smul hfv.aestronglyMeasurable).mono_ac (weight_ac_volume k))
      (Eventually.of_forall hb)
  refine ⟨?_, h1⟩
  refine MemLp.ae_eq (Eventually.of_forall fun ξ => ?_) (h1.const_smul (2 * (π : ℂ) * Complex.I))
  simp only [Pi.smul_apply, gradPressureSymbol, smul_smul]

private theorem integrable_pressure_curve (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (pressureSymbol (F t)) := by
  have hp := integrable_of_memLp_weight (memLp_pressure_single_curve hF hs ht 0)
  have h2 := (EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).integrable_comp hp
  refine h2.congr (Eventually.of_forall fun ξ => ?_)
  exact single_apply_zero _

private theorem memLp_timeDeriv_curve (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) :
    MemLp (timeDerivSymbol (F t)) 1 (weightL1Measure k) := by
  have hl := memLp_sspSymbol (memLp_weight_of_curve hF ht (k + 2))
  have hg := (memLp_gradPressure_curve hF hs ht k).1
  have ha := memLp_advectionSymbol (fun k => memLp_weight_of_curve hF ht k) k
  have he : timeDerivSymbol (F t) = fun ξ => sspSymbol (F t) ξ - gradPressureSymbol (F t) ξ -
      advectionSymbol (F t) ξ := by
    funext ξ
    exact eq_sub_of_add_eq (timeDerivSymbol_add_advectionSymbol _ ξ)
  rw [he]
  exact (hl.sub hg).sub ha

theorem hasDerivAt_physField_curve (hT : 0 < T) (hF : ∀ m, IsHsCurve m F 0 T)
    (hd : IsVarConstSymbol F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) :
    HasDerivAt (fun τ => physField (F τ) x) (physField (timeDerivSymbol (F t)) x) t := by
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have h := hasDerivAt_freqTrInv_curve (k := 0) ht (fun τ hτ => memLp_weight_of_curve hF hτ 0)
    (memLp_timeDeriv_curve hF hs htc 0) (hasDerivWithinAt_toWeightL1 hT hF hd hs 0 htc) x
  exact realVec.hasFDerivAt.comp_hasDerivAt t h

theorem integrable_symbols_curve (_hT : 0 < T) (hF : ∀ m, IsHsCurve m F 0 T)
    (_hd : IsVarConstSymbol F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (timeDerivSymbol (F t)) ∧ Integrable (advectionSymbol (F t)) ∧
      Integrable (sspSymbol (F t)) ∧ Integrable (gradPressureSymbol (F t)) :=
  ⟨integrable_of_memLp_weight (memLp_timeDeriv_curve hF hs ht 0),
    integrable_of_memLp_weight (memLp_advectionSymbol (fun k => memLp_weight_of_curve hF ht k) 0),
    integrable_of_memLp_weight (memLp_sspSymbol (memLp_weight_of_curve hF ht (0 + 2))),
    integrable_of_memLp_weight (memLp_gradPressure_curve hF hs ht 0).1⟩

theorem advectionAt_physField_curve (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Space) :
    advectionAt (physField (F t)) x = physField (advectionSymbol (F t)) x :=
  advectionAt_physField (fun k => memLp_weight_of_curve hF ht k) (hs t ht) x

theorem sumSecondPartialsAt_physField_curve (hF : ∀ m, IsHsCurve m F 0 T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Space) :
    sumSecondPartialsAt (physField (F t)) x = physField (sspSymbol (F t)) x :=
  sumSecondPartialsAt_physField (memLp_weight_of_curve hF ht 2) x

theorem gradientAt_pressure_curve (_hT : 0 < T) (hF : ∀ m, IsHsCurve m F 0 T)
    (_hd : IsVarConstSymbol F 0 T) (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Space) :
    gradientAt (physScalar (pressureSymbol (F t))) x = physField (gradPressureSymbol (F t)) x :=
  gradientAt_physScalar (integrable_pressure_curve hF hs ht)
    (integrable_of_memLp_weight (memLp_gradPressure_curve hF hs ht 0).2) x

theorem divergenceAt_physField_curve (hF : ∀ m, IsHsCurve m F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Space) :
    divergenceAt (physField (F t)) x = 0 :=
  divergenceAt_physField (memLp_weight_of_curve hF ht 1) (fun ξ => ((hs t ht) ξ).1) x

end Curve

end Breakdown.SmoothFlow
