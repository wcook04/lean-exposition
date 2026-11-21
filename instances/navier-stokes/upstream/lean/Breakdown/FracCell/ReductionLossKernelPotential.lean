import Breakdown.FracCell.ReductionLossKernelPotentialApprox
import Breakdown.FracCell.ReductionLossKernelPotentialTest

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

private theorem entrySq_nonneg_aux (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem kernelBound_const_nonneg {V : Space → ℝ} {Λ : ℝ} (hK : KernelBound V Λ) : 0 ≤ Λ := by
  obtain ⟨h0, -, hx⟩ := hK
  refine le_trans (integral_nonneg fun y => ?_) (hx 0).2
  have := h0 y
  positivity

private theorem kernel_of_approx (V : Space → ℝ) (Λ : ℝ) (hK : KernelBound V Λ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space))
    (hv : AEStronglyMeasurable v volume) (u : ℕ → Space → Space)
    (hu : ∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n))
    (hlim : ∀ᵐ y ∂volume, Tendsto (fun n => u n y) atTop (𝓝 (v y)))
    (hE : ∀ n, ∫ y, entrySq (fderiv ℝ (u n) y) ≤ (∫ y, entrySq (G y)) + 1 / ((n : ℝ) + 1)) :
    Integrable (fun y => V y * ‖v y‖ ^ 2) ∧ ∫ y, V y * ‖v y‖ ^ 2 ≤ Λ * ∫ y, entrySq (G y) := by
  have hΛ := kernelBound_const_nonneg hK
  have hVpos := hK.1
  set A := ∫ y, entrySq (G y) with hA
  set d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hd
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set f : ℕ → Space → ℝ := fun n y => V y * ‖u n y‖ ^ 2 with hf
  have hT := fun n => kernelPotentialTest V Λ hK (u n) (hu n).1 (hu n).2
  have hfi : ∀ n, Integrable (f n) := fun n => (hT n).1
  have hfn : ∀ n y, 0 ≤ f n y := fun n y => by
    have := hVpos y
    simp only [hf]
    positivity
  have hbound : ∀ n, ∫ y, f n y ≤ Λ * (A + d n) := fun n =>
    (hT n).2.trans (mul_le_mul_of_nonneg_left (hE n) hΛ)
  have hpt : ∀ᵐ y ∂volume, Tendsto (fun n => f n y) atTop (𝓝 (V y * ‖v y‖ ^ 2)) := by
    filter_upwards [hlim] with y hy
    exact ((hy.norm).pow 2).const_mul (V y)
  have hgm : AEStronglyMeasurable (fun y => V y * ‖v y‖ ^ 2) volume :=
    hK.2.1.aestronglyMeasurable.mul (hv.norm.pow 2)
  have hg0 : 0 ≤ᵐ[volume] fun y => V y * ‖v y‖ ^ 2 := ae_of_all _ fun y => by
    have := hVpos y
    positivity
  have hlimB : Tendsto (fun n => Λ * (A + d n)) atTop (𝓝 (Λ * A)) := by
    have := (tendsto_const_nhds (x := A)).add hdlim
    rw [add_zero] at this
    exact this.const_mul Λ
  have hfm : ∀ n, AEMeasurable (fun y => ENNReal.ofReal (f n y)) volume := fun n =>
    (hfi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfat : ∫⁻ y, ENNReal.ofReal (V y * ‖v y‖ ^ 2) ≤ ENNReal.ofReal (Λ * A) := by
    calc ∫⁻ y, ENNReal.ofReal (V y * ‖v y‖ ^ 2)
        = ∫⁻ y, liminf (fun n => ENNReal.ofReal (f n y)) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [hpt] with y hy
          exact ((ENNReal.tendsto_ofReal hy).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (f n y)) atTop := lintegral_liminf_le' hfm
      _ ≤ liminf (fun n => ENNReal.ofReal (Λ * (A + d n))) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hfn n))]
          exact ENNReal.ofReal_le_ofReal (hbound n)
      _ = ENNReal.ofReal (Λ * A) := (ENNReal.tendsto_ofReal hlimB).liminf_eq
  have hint : Integrable (fun y => V y * ‖v y‖ ^ 2) :=
    ⟨hgm, (hasFiniteIntegral_iff_ofReal hg0).2 (lt_of_le_of_lt hfat ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have hA0 : 0 ≤ A := integral_nonneg fun y => entrySq_nonneg_aux _
  rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm]
  calc (∫⁻ y, ENNReal.ofReal (V y * ‖v y‖ ^ 2)).toReal ≤ (ENNReal.ofReal (Λ * A)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfat
    _ = Λ * A := ENNReal.toReal_ofReal (mul_nonneg hΛ hA0)

theorem kernelPotential : KernelPotentialStatement := by
  intro V Λ hK v G hvG
  obtain ⟨hv, h6, hGm, hG, hw⟩ := hvG
  have hGc : ∀ j : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector j)) volume := fun j =>
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hGm
  obtain ⟨u, hu, hlim, hE⟩ := FracInternal.KernelPotentialApprox.smoothCompactApprox v G h6 hG hGc hw
  exact kernel_of_approx V Λ hK v G hv u hu hlim hE

end Reduction

end CellCert

end Breakdown
