import Breakdown.Uniqueness.RegCurve

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private def evalWeight (k : ℕ) (ξ : Space) : ℝ := ((1 + ‖ξ‖) ^ k)⁻¹

private theorem evalWeight_pos (k : ℕ) (ξ : Space) : 0 < evalWeight k ξ := by
  unfold evalWeight; positivity

private theorem evalWeight_le_one (k : ℕ) (ξ : Space) : evalWeight k ξ ≤ 1 := by
  unfold evalWeight
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg ξ]))

private theorem continuous_evalWeight (k : ℕ) : Continuous (evalWeight k) := by
  unfold evalWeight
  exact ((continuous_const.add continuous_norm).pow k).inv₀ fun ξ =>
    (pow_pos (by positivity : (0 : ℝ) < 1 + ‖ξ‖) k).ne'

private theorem evalIntegrand_norm_le (k : ℕ) (x : Space) (g : Space → CSpace) (ξ : Space) :
    ‖evalWeight k ξ • ((𝐞 (inner ℝ ξ x)) • g ξ)‖ ≤ ‖g ξ‖ := by
  rw [norm_smul, Circle.norm_smul, Real.norm_of_nonneg (evalWeight_pos k ξ).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (evalWeight_le_one k ξ)

private theorem evalIntegrand_integrable (k : ℕ) (x : Space)
    (g : Lp CSpace 1 (weightL1Measure k)) :
    Integrable (fun ξ => evalWeight k ξ • ((𝐞 (inner ℝ ξ x)) • (g : Space → CSpace) ξ))
      (weightL1Measure k) := by
  refine (L1.integrable_coeFn g).mono ?_
    (Eventually.of_forall fun ξ => evalIntegrand_norm_le k x _ ξ)
  exact (continuous_evalWeight k).aestronglyMeasurable.smul
    (((Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable g))

private def evalLin (k : ℕ) (x : Space) : Lp CSpace 1 (weightL1Measure k) →ₗ[ℝ] CSpace where
  toFun g := ∫ ξ, evalWeight k ξ • ((𝐞 (inner ℝ ξ x)) • (g : Space → CSpace) ξ)
    ∂weightL1Measure k
  map_add' f g := by
    rw [← integral_add (evalIntegrand_integrable k x f) (evalIntegrand_integrable k x g)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with ξ hξ
    rw [hξ, Pi.add_apply, smul_add, smul_add]
  map_smul' r g := by
    rw [RingHom.id_apply, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul r g] with ξ hξ
    rw [hξ, Pi.smul_apply, smul_comm (𝐞 (inner ℝ ξ x)) r, smul_comm (evalWeight k ξ) r]

private def evalCLM (k : ℕ) (x : Space) : Lp CSpace 1 (weightL1Measure k) →L[ℝ] CSpace :=
  (evalLin k x).mkContinuous 1 fun g => by
    rw [one_mul, L1.norm_eq_integral_norm]
    exact norm_integral_le_of_norm_le (L1.integrable_coeFn g).norm
      (Eventually.of_forall fun ξ => evalIntegrand_norm_le k x _ ξ)

private theorem evalCLM_apply (k : ℕ) (x : Space) (g : Lp CSpace 1 (weightL1Measure k)) :
    evalCLM k x g = ∫ ξ, evalWeight k ξ • ((𝐞 (inner ℝ ξ x)) • (g : Space → CSpace) ξ)
      ∂weightL1Measure k := rfl

private theorem evalCLM_toWeightL1 (k : ℕ) (x : Space) {f : Space → CSpace}
    (hf : MemLp f 1 (weightL1Measure k)) : evalCLM k x (toWeightL1 k f) = 𝓕⁻ f x := by
  have h1 : toWeightL1 k f = hf.toLp f := by
    unfold toWeightL1
    rw [dif_pos hf]
  rw [evalCLM_apply, h1]
  have h2 : ∫ ξ, evalWeight k ξ • ((𝐞 (inner ℝ ξ x)) • (hf.toLp f : Space → CSpace) ξ)
      ∂weightL1Measure k = ∫ ξ, evalWeight k ξ • ((𝐞 (inner ℝ ξ x)) • f ξ) ∂weightL1Measure k := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hf] with ξ hξ
    rw [hξ]
  rw [h2, weightL1Measure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ k))
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), fourierInv_eq]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have hp : (0 : ℝ) < (1 + ‖ξ‖) ^ k := by positivity
  simp only
  rw [ENNReal.toReal_ofReal hp.le, smul_smul, evalWeight, mul_inv_cancel₀ hp.ne', one_smul]

theorem hasDerivAt_freqTrInv_curve {T : ℝ} {c : ℝ → Space → CSpace} {d : Space → CSpace} {k : ℕ}
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hm : ∀ τ ∈ Icc 0 T, MemLp (c τ) 1 (weightL1Measure k))
    (hd : MemLp d 1 (weightL1Measure k))
    (hc : HasDerivWithinAt (fun τ => toWeightL1 k (c τ)) (toWeightL1 k d) (Icc 0 T) t) (x : Space) :
    HasDerivAt (fun τ => 𝓕⁻ (c τ) x) (𝓕⁻ d x) t := by
  have hmem : Icc 0 T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have h1 := ((evalCLM k x).hasFDerivAt.comp_hasDerivWithinAt t hc).hasDerivAt hmem
  rw [evalCLM_toWeightL1 k x hd] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with τ hτ
  exact (evalCLM_toWeightL1 k x (hm τ hτ)).symm

end Breakdown.SmoothFlow
