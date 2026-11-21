import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoercivePieceAbsorbMeasure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothDensity

open PairingSplitInternal (periodMeasure)
open ModeL2Internal (IsSquareField)

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {W v : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem smoothRight_square (hv : IsSmoothPerturbation P v)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    IsSquareField (smoothRight P W v) := by
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hD 0 0 0 (by norm_num))
    simpa using h
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.of_le (by norm_cast)
  have cv : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv.smooth.continuous
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have cDv := Internal.PieceAbsorb.continuous_fderiv_slice hv2
  have cDW := Internal.PieceAbsorb.continuous_fderiv_slice hW
  have mH := Internal.PieceAbsorb.measurable_secondDeriv_slice hv2
  have mT : Measurable (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) := by
    have h := measurable_deriv_with_param (f := fun (y : Space) (s : ℝ) => v s y)
      (by exact cv.comp continuous_swap)
    exact h.comp measurable_swap
  have mHt : Measurable (fun z : ℝ × Space => secondDerivTrace (secondDerivField v z.1 z.2)) := by
    unfold secondDerivTrace secondDerivField
    exact Finset.measurable_sum _ fun j _ => (ContinuousLinearMap.measurable_apply (unitVector j)).comp
      ((ContinuousLinearMap.measurable_apply (unitVector j)).comp mH)
  have mSR : Measurable (fun z : ℝ × Space => smoothRight P W v z.1 z.2) := by
    unfold smoothRight
    have m3 : Measurable (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 z.2) :=
      (cDv.clm_apply continuous_snd).measurable
    have m5 : Measurable (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 (W z.1 z.2)) :=
      (cDv.clm_apply cW).measurable
    have m6 : Measurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
      (cDW.clm_apply cv).measurable
    exact (((((mT.const_smul (1 / P)).add (cv.measurable.const_smul (1 / 2 : ℝ))).add
      (m3.const_smul (1 / 2 : ℝ))).sub mHt).add m5).add m6
  have hper : IsTimePeriodic (smoothRight P W v) := by
    intro σ y
    have hvσ : v (σ + 1) = v σ := funext (hv.periodic σ)
    have hWσ : W (σ + 1) = W σ := funext (hWp σ)
    have hd : deriv (fun s => v s y) (σ + 1) = deriv (fun s => v s y) σ := by
      rw [← deriv_comp_add_const (fun s => v s y) 1 σ]
      have e : (fun s => v (s + 1) y) = fun s => v s y := funext fun s => hv.periodic s y
      exact congrArg (fun f => deriv f σ) e
    unfold smoothRight secondDerivField
    rw [hd, hvσ, hWσ]
  refine ⟨mSR.aestronglyMeasurable, hper, ?_⟩
  have aesl : ∀ {f : ℝ × Space → ℝ}, Measurable f → AEStronglyMeasurable f ModeL2Internal.slab :=
    fun h => h.aestronglyMeasurable
  have iT : Integrable (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 0 (transportPart P v z.1) z.2‖ ^ 2)
      ModeL2Internal.slab := by
    refine ModeL2Internal.integrable_of_periodLIntegral
      (fun σ y => ‖iteratedFDeriv ℝ 0 (transportPart P v σ) y‖ ^ 2) ?_ (fun σ y => sq_nonneg _)
      (hv.transport_finite 0)
    have e : (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 0 (transportPart P v z.1) z.2‖ ^ 2) =
        fun z => ‖transportPart P v z.1 z.2‖ ^ 2 := by
      funext z
      rw [norm_iteratedFDeriv_zero]
    show AEStronglyMeasurable (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 0 (transportPart P v z.1) z.2‖ ^ 2)
      ModeL2Internal.slab
    rw [e]
    unfold transportPart
    have m3 : Measurable (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 z.2) :=
      (cDv.clm_apply continuous_snd).measurable
    exact aesl ((((mT.const_smul (1 / P)).add (cv.measurable.const_smul (1 / 2 : ℝ))).add
      (m3.const_smul (1 / 2 : ℝ))).norm.pow_const 2)
  have iH : Integrable (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 2 (v z.1) z.2‖ ^ 2) ModeL2Internal.slab := by
    refine ModeL2Internal.integrable_of_periodLIntegral
      (fun σ y => ‖iteratedFDeriv ℝ 2 (v σ) y‖ ^ 2) ?_ (fun σ y => sq_nonneg _)
      (hv.derivatives_finite 2 (by norm_num))
    have e : (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 2 (v z.1) z.2‖ ^ 2) =
        fun z => ‖fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2‖ ^ 2 := by
      funext z
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    show AEStronglyMeasurable (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 2 (v z.1) z.2‖ ^ 2) ModeL2Internal.slab
    rw [e]
    exact aesl (mH.norm.pow_const 2)
  have iG : Integrable (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 1 (v z.1) z.2‖ ^ 2) ModeL2Internal.slab := by
    refine ModeL2Internal.integrable_of_periodLIntegral
      (fun σ y => ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2) ?_ (fun σ y => sq_nonneg _)
      (hv.derivatives_finite 1 le_rfl)
    have e : (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 1 (v z.1) z.2‖ ^ 2) =
        fun z => ‖fderiv ℝ (v z.1) z.2‖ ^ 2 := by
      funext z
      rw [norm_iteratedFDeriv_one]
    show AEStronglyMeasurable (fun z : ℝ × Space => ‖iteratedFDeriv ℝ 1 (v z.1) z.2‖ ^ 2) ModeL2Internal.slab
    rw [e]
    exact aesl (cDv.measurable.norm.pow_const 2)
  have iV : Integrable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) ModeL2Internal.slab :=
    ModeL2Internal.integrable_of_periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
      (aesl ((cv.measurable.norm.pow_const 2).div ((measurable_const.add measurable_snd.norm).pow_const 2)))
      (fun σ y => div_nonneg (sq_nonneg _) (sq_nonneg _)) hv.weighted_finite
  have hb : ∀ σ y, ‖smoothRight P W v σ y‖ ^ 2 ≤
      4 * ‖iteratedFDeriv ℝ 0 (transportPart P v σ) y‖ ^ 2 + 36 * ‖iteratedFDeriv ℝ 2 (v σ) y‖ ^ 2
        + 4 * D ^ 2 * ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2 + 4 * D ^ 2 * (‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
    intro σ y
    set t := ‖iteratedFDeriv ℝ 0 (transportPart P v σ) y‖ with htdef
    set h := ‖iteratedFDeriv ℝ 2 (v σ) y‖ with hhdef
    set g := ‖iteratedFDeriv ℝ 1 (v σ) y‖ with hgdef
    set u := ‖v σ y‖ / (1 + ‖y‖) with hudef
    have hy : 0 < 1 + ‖y‖ := by positivity
    have e0 : smoothRight P W v σ y = transportPart P v σ y - secondDerivTrace (secondDerivField v σ y)
        + fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y) := rfl
    have b1 : ‖transportPart P v σ y‖ = t := by rw [htdef, norm_iteratedFDeriv_zero]
    have b2 : ‖secondDerivTrace (secondDerivField v σ y)‖ ≤ 3 * h := by
      have hh : ‖secondDerivField v σ y‖ = h := by
        rw [hhdef, ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
        rfl
      have hj : ∀ j : Fin 3, ‖secondDerivField v σ y (unitVector j) (unitVector j)‖ ≤ h := by
        intro j
        have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
        calc ‖secondDerivField v σ y (unitVector j) (unitVector j)‖
            ≤ ‖secondDerivField v σ y (unitVector j)‖ * ‖unitVector j‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖secondDerivField v σ y‖ * ‖unitVector j‖ * ‖unitVector j‖ := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
          _ = h := by rw [hu, hh]; ring
      unfold secondDerivTrace
      calc ‖∑ j : Fin 3, secondDerivField v σ y (unitVector j) (unitVector j)‖
          ≤ ∑ j : Fin 3, ‖secondDerivField v σ y (unitVector j) (unitVector j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin 3, h := Finset.sum_le_sum fun j _ => hj j
        _ = 3 * h := by simp
    have b3 : ‖fderiv ℝ (v σ) y (W σ y)‖ ≤ D * g := by
      have hWb : ‖W σ y‖ ≤ D := by
        have h0 := hD σ y 0 (by norm_num)
        rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
        exact h0.trans (div_le_self hD0 (by linarith [norm_nonneg y]))
      have hg : ‖fderiv ℝ (v σ) y‖ = g := by rw [hgdef, norm_iteratedFDeriv_one]
      calc ‖fderiv ℝ (v σ) y (W σ y)‖ ≤ ‖fderiv ℝ (v σ) y‖ * ‖W σ y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (v σ) y‖ * D := mul_le_mul_of_nonneg_left hWb (norm_nonneg _)
        _ = D * g := by rw [hg]; ring
    have b4 : ‖fderiv ℝ (W σ) y (v σ y)‖ ≤ D * u := by
      have hDW : ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) := by
        have h1 := hD σ y 1 (by norm_num)
        rw [norm_iteratedFDeriv_one] at h1
        exact h1.trans (div_le_div_of_nonneg_left hD0 hy
          (le_self_pow₀ (by linarith [norm_nonneg y]) (by norm_num)))
      calc ‖fderiv ℝ (W σ) y (v σ y)‖ ≤ ‖fderiv ℝ (W σ) y‖ * ‖v σ y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ D / (1 + ‖y‖) * ‖v σ y‖ := mul_le_mul_of_nonneg_right hDW (norm_nonneg _)
        _ = D * u := by rw [hudef]; ring
    have hn : ‖smoothRight P W v σ y‖ ≤ t + 3 * h + D * g + D * u := by
      rw [e0]
      have s1 := norm_add_le (transportPart P v σ y - secondDerivTrace (secondDerivField v σ y)
        + fderiv ℝ (v σ) y (W σ y)) (fderiv ℝ (W σ) y (v σ y))
      have s2 := norm_add_le (transportPart P v σ y - secondDerivTrace (secondDerivField v σ y))
        (fderiv ℝ (v σ) y (W σ y))
      have s3 := norm_sub_le (transportPart P v σ y) (secondDerivTrace (secondDerivField v σ y))
      linarith
    have hnn : 0 ≤ ‖smoothRight P W v σ y‖ := norm_nonneg _
    have hsq : ‖smoothRight P W v σ y‖ ^ 2 ≤ (t + 3 * h + D * g + D * u) ^ 2 := pow_le_pow_left₀ hnn hn 2
    have hu2 : ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 = u ^ 2 := by rw [hudef, div_pow]
    rw [hu2]
    nlinarith [sq_nonneg (t - 3 * h), sq_nonneg (t - D * g), sq_nonneg (t - D * u), sq_nonneg (3 * h - D * g),
      sq_nonneg (3 * h - D * u), sq_nonneg (D * g - D * u)]
  have hint : Integrable (fun z : ℝ × Space => ‖smoothRight P W v z.1 z.2‖ ^ 2) ModeL2Internal.slab := by
    refine Integrable.mono' ((((iT.const_mul 4).add (iH.const_mul 36)).add (iG.const_mul (4 * D ^ 2))).add
      (iV.const_mul (4 * D ^ 2))) (aesl (mSR.norm.pow_const 2)) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb z.1 z.2
  rw [ModeL2Internal.periodLIntegral_eq_slab _ (aesl (mSR.norm.pow_const 2))]
  exact hint.lintegral_lt_top

end Internal.SmoothDensity

end Coercive

end Breakdown
