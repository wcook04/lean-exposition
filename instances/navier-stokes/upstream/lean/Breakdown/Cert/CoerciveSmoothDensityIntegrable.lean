import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoerciveSmoothEnergyIdentityRest

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothDensity

open PairingSplitInternal (periodMeasure)
open ModeL2Internal (IsSquareField)
open EnergyIdentityInternal SmoothEnergyIdentityInternal.Rest

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {W v : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem slice_square_integrable (hv : IsSmoothPerturbation P v) :
    Integrable (fun z : ℝ × Space => ‖fderiv ℝ (v z.1) z.2‖ ^ 2) periodMeasure ∧
    Integrable (fun z : ℝ × Space => ‖fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2‖ ^ 2) periodMeasure ∧
    Integrable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) periodMeasure := by
  have h0 := hv.smooth
  have j1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    joint_partial v h0 (by simp) (by simp)
  have j2 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    joint_partial (fun σ x => fderiv ℝ (v σ) x) j1 (by simp) (by simp)
  have e1 : (fun σ y => ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2) = fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2 := by
    funext σ y
    rw [norm_iteratedFDeriv_one]
  have e2 : (fun σ y => ‖iteratedFDeriv ℝ 2 (v σ) y‖ ^ 2) =
      fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2 := by
    funext σ y
    rw [norm_iter_two]
  have p1 := hv.derivatives_finite 1 le_rfl
  have p2 := hv.derivatives_finite 2 (by norm_num)
  rw [e1] at p1
  rw [e2] at p2
  refine ⟨joint_integrable (fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) ((continuous_norm.comp j1.continuous).pow 2)
      (fun σ y => by positivity) p1,
    joint_integrable (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2)
      ((continuous_norm.comp j2.continuous).pow 2) (fun σ y => by positivity) p2,
    joint_integrable (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) ?_ (fun σ y => by positivity) hv.weighted_finite⟩
  exact Continuous.div ((continuous_norm.comp h0.continuous).pow 2)
    ((continuous_const.add (continuous_norm.comp continuous_snd)).pow 2) (fun z => by positivity)

theorem vorticity_integrable (hv : IsSmoothPerturbation P v) :
    Integrable (fun z : ℝ × Space => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2)
      + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v z.1) z.2)‖ ^ 2) periodMeasure := by
  obtain ⟨i1, i2, -⟩ := slice_square_integrable hv
  have h0 := hv.smooth
  have j1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    joint_partial v h0 (by simp) (by simp)
  have j3 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => curlCLM (fderiv ℝ (v z.1) x)) z.2) :=
    joint_partial (fun σ x => curlCLM (fderiv ℝ (v σ) x)) (curlCLM.contDiff.comp j1) (by simp) (by simp)
  have c1 := j1.continuous
  have c3 := j3.continuous
  set c := ‖curlCLM‖ with hc
  have hdv : ∀ σ y, fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y =
      curlCLM.comp (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y) := by
    intro σ y
    have hd : DifferentiableAt ℝ (fun x => fderiv ℝ (v σ) x) y := by
      have hs : ContDiff ℝ ∞ (v σ) := h0.comp (contDiff_const.prodMk contDiff_id)
      exact ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
    exact fderiv_clm_left curlCLM hd
  refine Integrable.mono' ((i2.const_mul (3 * c ^ 2)).add (i1.const_mul (c ^ 2 / 4))) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    simp only [matSq, ← curlCLM_apply]
    fun_prop
  · refine Eventually.of_forall (fun z => ?_)
    obtain ⟨σ, y⟩ := z
    simp only
    have fr : matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        ≤ 3 * c ^ 2 * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2 := by
      rw [hdv]
      refine (matNorm_le _).trans ?_
      have h1 := ContinuousLinearMap.opNorm_comp_le curlCLM (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y)
      have h2 : ‖curlCLM.comp (fderiv ℝ (fun x => fderiv ℝ (v σ) x) y)‖ ^ 2
          ≤ (c * ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith
    have cu : ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 ≤ c ^ 2 * ‖fderiv ℝ (v σ) y‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (curl_norm_le (fderiv ℝ (v σ) y)) 2
      nlinarith
    have hfr0 := matNorm_nonneg (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith

theorem stretch_integrable (hv : IsSmoothPerturbation P v)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    Integrable (fun z : ℝ × Space => stretchForm W v (gradField v) z.1 z.2) periodMeasure := by
  obtain ⟨i1, -, i0⟩ := slice_square_integrable hv
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 : 0 ≤ D := by
    have := hD 0 0 0 (by norm_num)
    simp at this
    exact (norm_nonneg _).trans this
  have h0 := hv.smooth
  have j1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    joint_partial v h0 (by simp) (by simp)
  have c0 : Continuous (fun z : ℝ × Space => v z.1 z.2) := h0.continuous
  have c1 := j1.continuous
  obtain ⟨w0, w1, w2⟩ := joint_continuous_weight hW
  set c := ‖curlCLM‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set Mc : ℝ := 81 * c + 729 / 2 with hMc
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  refine Integrable.mono' ((i1.const_mul (9 * c ^ 2 * D + Mc * D / 2)).add (i0.const_mul (Mc * D / 2))) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    simp only [stretchForm, vortGrad, gradField, ← curlCLM_apply]
    fun_prop
  · refine Eventually.of_forall (fun z => ?_)
    obtain ⟨σ, y⟩ := z
    simp only
    have hWσ1 := hD σ y 1 (by norm_num)
    have hWσ2 := hD σ y 2 (by norm_num)
    rw [norm_iteratedFDeriv_one] at hWσ1
    rw [norm_iter_two] at hWσ2
    set A := ‖v σ y‖ / (1 + ‖y‖) with hA
    set B := ‖fderiv ℝ (v σ) y‖ with hB
    set dW := ‖fderiv ℝ (W σ) y‖ with hdW
    set hW2 := ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ with hhW2
    have hy1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have hA0 : 0 ≤ A := by positivity
    have hB0 : 0 ≤ B := norm_nonneg _
    have dWle : dW ≤ D := by
      refine hWσ1.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ (1 + ‖y‖) ^ (1 + 1) := one_le_pow₀ hy1
      nlinarith
    have hWle : hW2 * ‖v σ y‖ ≤ D * A := by
      have h3 : hW2 ≤ D / (1 + ‖y‖) := by
        refine hWσ2.trans ?_
        apply div_le_div_of_nonneg_left hD0 (by positivity)
        calc 1 + ‖y‖ = (1 + ‖y‖) ^ 1 := (pow_one _).symm
          _ ≤ (1 + ‖y‖) ^ (2 + 1) := pow_le_pow_right₀ hy1 (by norm_num)
      rw [hA, mul_div_assoc']
      calc hW2 * ‖v σ y‖ ≤ D / (1 + ‖y‖) * ‖v σ y‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = D * ‖v σ y‖ / (1 + ‖y‖) := by ring
    have sF := stretch_le (fderiv ℝ (v σ) y) (fderiv ℝ (W σ) y)
      (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) (v σ y)
    have eX : 3 * (3 * (‖v σ y‖ * (3 * (3 * (1 * hW2)))) * (c * B))
        + (1 / 2 : ℝ) * (3 * (3 * (3 * (3 * (1 * (3 * (3 * (1 * hW2))) * B * ‖v σ y‖)))))
        = Mc * (hW2 * ‖v σ y‖) * B := by rw [hMc]; ring
    have sF' : |stretchForm W v (gradField v) σ y| ≤
        3 * (3 * (c * B * dW * (c * B))) + Mc * (hW2 * ‖v σ y‖) * B := by
      have e0 : |stretchForm W v (gradField v) σ y| = |-(∑ i : Fin 3, ∑ j : Fin 3,
          curlVec (fderiv ℝ (v σ) y) i * ((fderiv ℝ (W σ) y (unitVector j) i
            + fderiv ℝ (W σ) y (unitVector i) j) / 2) * curlVec (fderiv ℝ (v σ) y) j)
          + ∑ j : Fin 3, (∑ m : Fin 3, v σ y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) j m)
            * curlVec (fderiv ℝ (v σ) y) j
          + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
            alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ (W σ) x) y) j m
              * fderiv ℝ (v σ) y (unitVector j) i * v σ y l| := rfl
      rw [e0]
      linarith
    have hAB : A * B ≤ (A ^ 2 + B ^ 2) / 2 := by nlinarith [sq_nonneg (A - B)]
    have hA2 : A ^ 2 = ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 := by rw [hA, div_pow]
    have q1 : 3 * (3 * (c * B * dW * (c * B))) ≤ 9 * c ^ 2 * D * B ^ 2 := by
      have e : c * B * dW * (c * B) = c ^ 2 * B ^ 2 * dW := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left dWle (by positivity : 0 ≤ c ^ 2 * B ^ 2)
      nlinarith
    have q2 : Mc * (hW2 * ‖v σ y‖) * B ≤ Mc * D * ((A ^ 2 + B ^ 2) / 2) := by
      have h1 := mul_le_mul_of_nonneg_right hWle hB0
      have h2 : Mc * (hW2 * ‖v σ y‖) * B ≤ Mc * (D * A * B) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hMc0
      have h3 : D * A * B ≤ D * ((A ^ 2 + B ^ 2) / 2) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hAB hD0
      nlinarith
    rw [Real.norm_eq_abs]
    refine sF'.trans ?_
    simp only [Pi.add_apply]
    rw [← hA2]
    linarith [q1, q2]

end Internal.SmoothDensity

end Coercive

end Breakdown
