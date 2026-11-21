import Breakdown.FracCert.StDecay
import Breakdown.FracCert.WeakRegular

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace DecayPowerInternal

theorem inverseTransform_coord (c : Space → CSpace) (hc : Integrable c) (i : Fin 3) (y : Space) :
    (𝓕⁻ c y) i = 𝓕⁻ (fun ξ => c ξ i) y := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  have hi : Integrable (fun v : Space => 𝐞 (inner ℝ v y) • c v) volume := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) (f := c) (-y)).2 hc
    simpa [inner_neg_right] using this
  have h := (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integral_comp_comm hi
  have h' : ∀ z : CSpace, EuclideanSpace.proj i z = z i := fun z => rfl
  simp only [h'] at h
  rw [← h]
  congr 1

theorem inverseTransform_real (p : Space → ℂ) (hp : ∀ ξ, p (-ξ) = (starRingEnd ℂ) (p ξ)) (y : Space) :
    (((𝓕⁻ p y).re : ℝ) : ℂ) = 𝓕⁻ p y := by
  have h : (starRingEnd ℂ) (𝓕⁻ p y) = 𝓕⁻ p y := by
    rw [Real.fourierInv_eq', ← integral_conj]
    conv_rhs => rw [← integral_neg_eq_self]
    congr 1
    funext v
    rw [hp, inner_neg_left, smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring
  exact Complex.conj_eq_iff_re.1 h

theorem transform_of (F : Space → ℂ) (hF : Integrable F) : IsTransformOf F (𝓕⁻ F) := by
  refine ⟨hF.locallyIntegrable, fun φ => ?_⟩
  have hφ : Integrable (𝓕 (φ : Space → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 φ).integrable
  have hL : Continuous fun p : Space × Space =>
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ p.1 p.2 :=
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).continuous₂
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    Real.continuous_fourierChar hL hF hφ
  have hflip : ((-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂).flip =
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ := by
    ext v w
    simp [real_inner_comm]
  rw [hflip] at h
  have e1 : ∀ g : Space → ℂ, VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ g = 𝓕⁻ g :=
    fun g => funext fun x => (Breakdown.SmoothFlow.Internal.freqTrInv_eq_integral g x).symm
  rw [e1, e1, Continuous.fourierInv_fourier_eq φ.continuous φ.integrable hφ] at h
  simpa [smul_eq_mul] using h

theorem le_of_weighted {r e a C : ℝ} (hr : 0 ≤ r) (h : (1 + r) ^ e * a ≤ C) :
    a ≤ C * (1 + r) ^ (-e) := by
  have hp : 0 < (1 + r) ^ e := Real.rpow_pos_of_pos (by linarith) e
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hp]
  linarith [mul_comm a ((1 + r) ^ e)]

theorem weight_cancel {r e : ℝ} (hr : 0 ≤ r) : (1 + r) ^ e * (1 + r) ^ (-e) = 1 := by
  rw [Real.rpow_neg (by linarith), mul_inv_cancel₀ (Real.rpow_pos_of_pos (by linarith) _).ne']

theorem power_le {α : ℝ} (hα : 0 < α) (hα2 : α < 3 / 2) (ξ : Space) :
    (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 := by
  have h0 : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  have hb : 1 ≤ 2 * π * (1 + ‖ξ‖) := by nlinarith [Real.pi_gt_three, norm_nonneg ξ]
  calc (2 * π * ‖ξ‖) ^ (2 * α) ≤ (2 * π * (1 + ‖ξ‖)) ^ (2 * α) :=
        Real.rpow_le_rpow h0 (by nlinarith [Real.pi_gt_three]) (by linarith)
    _ ≤ (2 * π * (1 + ‖ξ‖)) ^ ((3 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb (by push_cast; linarith)
    _ = (2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 := by rw [Real.rpow_natCast, mul_pow]

theorem homogeneous_power (α : ℝ) :
    IsHomogeneousSymbol (fun ξ : Space => (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ)) (2 * α) := by
  refine ⟨fun ξ hξ => ?_, fun t ht ξ hξ => ?_⟩
  · have hξ' : ξ ≠ 0 := hξ
    have h0 : ContDiffAt ℝ ∞ (fun ξ : Space => 2 * π * ‖ξ‖) ξ :=
      contDiffAt_const.mul (contDiffAt_norm ℝ hξ')
    have h1 : ContDiffAt ℝ ∞ (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α)) ξ :=
      h0.rpow_const_of_ne (by have := norm_pos_iff.2 hξ'; positivity)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ h1).contDiffWithinAt
  · simp only [norm_smul, Real.norm_of_nonneg ht.le]
    rw [show 2 * π * (t * ‖ξ‖) = t * (2 * π * ‖ξ‖) by ring, Real.mul_rpow ht.le (by positivity)]
    push_cast
    ring

end DecayPowerInternal


open DecayPowerInternal WeakRegularInternal in
theorem powerDecay_of (h1 : HomogeneousMultiplierStatement) (h2 : SymbolL1OfMomentsStatement)
    (h3 : FieldSmoothOfMomentsStatement) : PowerDecayStatement := by
  intro α hα hα2 a U _ hM hD
  have hwm := (h2 U hM).1
  obtain ⟨c, hc⟩ : ∃ c : Space → CSpace, c = cleanSymbol (symbolX U) := ⟨_, rfl⟩
  have hcm : HasAllSymbolL1Moments c := hc ▸ moments_clean U hwm
  have hcs : AEStronglyMeasurable c volume :=
    hc ▸ (aesm_symbolX U).congr (cleanSymbol_ae (goodSet_ae U)).symm
  have hci : Integrable c := by
    refine (integrable_norm_iff hcs).1 ((hcm 0).congr (ae_of_all _ fun ξ => ?_))
    simp
  have hV : profileField U = physField c := by
    rw [hc, physField_clean]
    rfl
  have hVs : ContDiff ℝ ∞ (profileField U) := by
    rw [hV]
    exact (h3 c hcm (hc ▸ cleanSymbol_conjSym _)).1
  have hF : fractionalPowerAt α (profileField U) = physField (powerSymbol α c) := by
    funext x
    rw [hV, hc]
    exact powerPhysPower_of α hα (by linarith)
      (Periodic.planeWaveEigen_of α hα (by linarith) (symbolScalar normalizer) normalizer) _
      (memLp_clean U hwm 3) x
  have hGi : Integrable (powerSymbol α c) :=
    integrable_powerSymbol (by linarith) (by linarith) hcs (hcm 3)
  obtain ⟨σ, hσd⟩ : ∃ σ : Space → ℂ, σ = fun ξ : Space => (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hσ : IsHomogeneousSymbol σ (2 * α) := hσd ▸ homogeneous_power α
  have hσm : AEStronglyMeasurable σ volume := by
    rw [hσd]
    exact (Complex.measurable_ofReal.comp
      (by fun_prop : Measurable fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α))).aestronglyMeasurable
  have hmain : ∀ i : Fin 3,
      IsWeightedSmooth (𝓕⁻ (fun ξ => σ ξ * c ξ i)) (2 * α - 1 + 2 * α) := by
    intro i
    obtain ⟨L0, hL0⟩ : ∃ L0 : Space →L[ℝ] ℂ,
        L0 = Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ) := ⟨_, rfl⟩
    have hFi : Integrable (fun ξ => c ξ i) :=
      (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integrable_comp hci
    have heq : (fun y => L0 (profileField U y)) = 𝓕⁻ (fun ξ => c ξ i) := by
      funext y
      rw [hL0, hV]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply]
      rw [← inverseTransform_real (fun ξ => c ξ i) (fun ξ => ?_) y, ← inverseTransform_coord c hci i y]
      · rfl
      · rw [hc, cleanSymbol_conjSym]
        rfl
    have hf : IsWeightedSmooth (fun y => L0 (profileField U y)) (2 * α - 1) := by
      refine ⟨L0.contDiff.comp hVs, fun j => ?_⟩
      obtain ⟨C, hC⟩ := hD j
      refine ⟨‖L0‖ * C, fun y => ?_⟩
      have e1 : ‖iteratedFDeriv ℝ j (fun y => L0 (profileField U y)) y‖ ≤
          ‖L0‖ * ‖iteratedFDeriv ℝ j (profileField U) y‖ :=
        L0.norm_iteratedFDeriv_comp_left hVs.contDiffAt (by exact_mod_cast le_top)
      have hw : 0 ≤ (1 + ‖y‖) ^ (2 * α - 1 + (j : ℝ)) := by positivity
      calc (1 + ‖y‖) ^ (2 * α - 1 + (j : ℝ)) * ‖iteratedFDeriv ℝ j (fun y => L0 (profileField U y)) y‖
          ≤ (1 + ‖y‖) ^ (2 * α - 1 + (j : ℝ)) *
              (‖L0‖ * (C * (1 + ‖y‖) ^ (-(2 * α - 1 + (j : ℝ))))) :=
            mul_le_mul_of_nonneg_left (e1.trans (mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _))) hw
        _ = ‖L0‖ * C * ((1 + ‖y‖) ^ (2 * α - 1 + (j : ℝ)) * (1 + ‖y‖) ^ (-(2 * α - 1 + (j : ℝ)))) := by
            ring
        _ = ‖L0‖ * C := by rw [weight_cancel (norm_nonneg y), mul_one]
    have hT : IsTransformOf (fun ξ => c ξ i) (fun y => L0 (profileField U y)) := by
      rw [heq]
      exact transform_of _ hFi
    have hMo : HasMomentsInL1 (fun ξ => σ ξ * c ξ i) := by
      refine ⟨hσm.mul hFi.1, fun n => ?_⟩
      refine ((hcm (n + 3)).const_mul ((2 * π) ^ 3)).mono' ?_ (ae_of_all _ fun ξ => ?_)
      · exact ((continuous_norm.pow n).aestronglyMeasurable).mul (hσm.mul hFi.1).norm
      · have hb := power_le (by linarith : (0 : ℝ) < α) (by linarith) ξ
        have hn : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
        have hcc : ‖c ξ i‖ ≤ ‖c ξ‖ := PiLp.norm_apply_le _ _
        rw [Real.norm_of_nonneg (by positivity), norm_mul, hσd, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        calc ‖ξ‖ ^ n * ((2 * π * ‖ξ‖) ^ (2 * α) * ‖c ξ i‖)
            ≤ (1 + ‖ξ‖) ^ n * ((2 * π) ^ 3 * (1 + ‖ξ‖) ^ 3 * ‖c ξ‖) := by gcongr
          _ = (2 * π) ^ 3 * ((1 + ‖ξ‖) ^ (n + 3) * ‖c ξ‖) := by ring
    exact h1 σ (2 * α) (2 * α - 1) (by linarith) (by linarith) (by linarith) hσ _ _ hf hT hMo
  obtain ⟨Lr, hLr⟩ : ∃ Lr : Fin 3 → ℂ →L[ℝ] Space,
      Lr = fun i => Complex.reCLM.smulRight (EuclideanSpace.single i (1 : ℝ)) := ⟨_, rfl⟩
  have hsum : fractionalPowerAt α (profileField U) =
      fun y => ∑ i, Lr i (𝓕⁻ (fun ξ => σ ξ * c ξ i) y) := by
    rw [hF]
    funext y
    ext k
    have e2 : (physField (powerSymbol α c) y) k = (𝓕⁻ (fun ξ => σ ξ * c ξ k) y).re := by
      rw [show physField (powerSymbol α c) y = realVec (𝓕⁻ (powerSymbol α c) y) from rfl]
      rw [show (realVec (𝓕⁻ (powerSymbol α c) y)) k = ((𝓕⁻ (powerSymbol α c) y) k).re from rfl]
      rw [inverseTransform_coord _ hGi k y, hσd]
      rfl
    rw [e2, hLr]
    simp [Pi.single_apply]
  have hsm : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => Lr i (𝓕⁻ (fun ξ => σ ξ * c ξ i) y)) :=
    fun i => (Lr i).contDiff.comp (hmain i).1
  refine ⟨?_, fun j => ?_⟩
  · rw [hsum]
    exact ContDiff.sum fun i _ => hsm i
  · choose C hC using fun i : Fin 3 => (hmain i).2 j
    refine ⟨∑ i, ‖Lr i‖ * C i, fun y => ?_⟩
    rw [hsum, iteratedFDeriv_sum (fun i _ => (hsm i).of_le (by exact_mod_cast le_top)),
      Finset.sum_apply]
    have hw : ∀ i : Fin 3, ‖iteratedFDeriv ℝ j (fun y => Lr i (𝓕⁻ (fun ξ => σ ξ * c ξ i) y)) y‖ ≤
        ‖Lr i‖ * C i * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := by
      intro i
      have e1 : ‖iteratedFDeriv ℝ j (fun y => Lr i (𝓕⁻ (fun ξ => σ ξ * c ξ i) y)) y‖ ≤
          ‖Lr i‖ * ‖iteratedFDeriv ℝ j (𝓕⁻ (fun ξ => σ ξ * c ξ i)) y‖ :=
        (Lr i).norm_iteratedFDeriv_comp_left (hmain i).1.contDiffAt (by exact_mod_cast le_top)
      have e3 : (1 + ‖y‖) ^ (4 * α - 1 + (j : ℝ)) *
          ‖iteratedFDeriv ℝ j (𝓕⁻ (fun ξ => σ ξ * c ξ i)) y‖ ≤ C i := by
        have := hC i y
        rwa [show 2 * α - 1 + 2 * α + (j : ℝ) = 4 * α - 1 + j by ring] at this
      have e2 := le_of_weighted (norm_nonneg y) e3
      calc _ ≤ ‖Lr i‖ * ‖iteratedFDeriv ℝ j (𝓕⁻ (fun ξ => σ ξ * c ξ i)) y‖ := e1
        _ ≤ ‖Lr i‖ * (C i * (1 + ‖y‖) ^ (-(4 * α - 1 + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
        _ = _ := by ring
    calc _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => Lr i (𝓕⁻ (fun ξ => σ ξ * c ξ i) y)) y‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ‖Lr i‖ * C i * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := Finset.sum_le_sum fun i _ => hw i
      _ = _ := by rw [Finset.sum_mul]

end Breakdown.FracCert
