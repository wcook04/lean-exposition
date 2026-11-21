import Breakdown.Frac.StSpaceReg

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem powerHeatSymbol_enorm_le_one (α : ℝ) {a t : ℝ} (ht : a ≤ t) (ξ : Space) :
    ‖((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ)‖ₑ ≤ 1 := by
  unfold powerHeatSymbol
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
  exact neg_nonpos.2 (mul_nonneg (sub_nonneg.2 ht) (Real.rpow_nonneg (by positivity) _))

private theorem powerHeatPart_enorm_le (α : ℝ) {a t : ℝ} (ht : a ≤ t) (f : Space → CSpace)
    (ξ : Space) : ‖powerHeatPart α a f t ξ‖ₑ ≤ ‖f ξ‖ₑ := by
  calc ‖powerHeatPart α a f t ξ‖ₑ = ‖((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ)‖ₑ * ‖f ξ‖ₑ :=
        enorm_smul _ _
    _ ≤ 1 * ‖f ξ‖ₑ := by gcongr; exact powerHeatSymbol_enorm_le_one α ht ξ
    _ = ‖f ξ‖ₑ := one_mul _

private theorem aestronglyMeasurable_powerHeatPart (α : ℝ) {f : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (a t : ℝ) :
    AEStronglyMeasurable (powerHeatPart α a f t) volume := by
  have hc : Measurable fun ξ : Space => ((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ) := by
    unfold powerHeatSymbol
    exact Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp
        ((measurable_const.mul ((measurable_const.mul measurable_norm).pow_const _)).neg))
  exact hc.aestronglyMeasurable.smul hf

private theorem fracNormSq_powerHeatPart_le (α r : ℝ) {a t : ℝ} (ht : a ≤ t)
    (f : Space → CSpace) : fracNormSq r (powerHeatPart α a f t) ≤ fracNormSq r f := by
  unfold fracNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr
  exact powerHeatPart_enorm_le α ht f ξ

private theorem tendsto_hsNormSq_powerHeatPart (α : ℝ) {m : ℕ} {f : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (h : hsNormSq m f < ⊤) {a b : ℝ} (t₀ : ℝ)
    (ht₀ : t₀ ∈ Icc a b) :
    Tendsto (fun t => hsNormSq m (powerHeatPart α a f t - powerHeatPart α a f t₀))
      (𝓝[Icc a b] t₀) (𝓝 0) := by
  have hw : Measurable fun ξ : Space => ENNReal.ofReal (hsWeight m ξ) := by
    unfold hsWeight
    exact ((measurable_const.add (measurable_norm.pow_const 2)).pow_const m).ennreal_ofReal
  have hcont : ∀ ξ, Continuous fun t => ENNReal.ofReal (hsWeight m ξ) *
      ‖(powerHeatPart α a f t - powerHeatPart α a f t₀) ξ‖ₑ ^ 2 := by
    intro ξ
    have hh : Continuous fun t => powerHeatPart α a f t ξ := by
      unfold powerHeatPart powerHeatSymbol
      fun_prop
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hh.sub continuous_const)))
  have hlim := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume)
    (l := 𝓝[Icc a b] t₀)
    (F := fun t ξ => ENNReal.ofReal (hsWeight m ξ) *
      ‖(powerHeatPart α a f t - powerHeatPart α a f t₀) ξ‖ₑ ^ 2)
    (f := fun ξ => ENNReal.ofReal (hsWeight m ξ) *
      ‖(powerHeatPart α a f t₀ - powerHeatPart α a f t₀) ξ‖ₑ ^ 2)
    (fun ξ => 4 * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2))
    (Eventually.of_forall fun t => hw.aemeasurable.mul
      (((aestronglyMeasurable_powerHeatPart α hf a t).sub
        (aestronglyMeasurable_powerHeatPart α hf a t₀)).enorm.pow_const 2))
    ?_ ?_ (Eventually.of_forall fun ξ => ((hcont ξ).tendsto t₀).mono_left nhdsWithin_le_nhds)
  · simpa [hsNormSq] using hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    refine Eventually.of_forall fun ξ => ?_
    have h3 : ‖(powerHeatPart α a f t - powerHeatPart α a f t₀) ξ‖ₑ ≤ 2 * ‖f ξ‖ₑ :=
      (enorm_sub_le).trans ((add_le_add (powerHeatPart_enorm_le α ht.1 f ξ)
        (powerHeatPart_enorm_le α ht₀.1 f ξ)).trans_eq (two_mul _).symm)
    calc ENNReal.ofReal (hsWeight m ξ) *
          ‖(powerHeatPart α a f t - powerHeatPart α a f t₀) ξ‖ₑ ^ 2
        ≤ ENNReal.ofReal (hsWeight m ξ) * (2 * ‖f ξ‖ₑ) ^ 2 := by gcongr
      _ = 4 * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) := by ring
  · rw [lintegral_const_mul' _ _ (by norm_num)]
    exact ENNReal.mul_ne_top (by norm_num) h.ne

theorem powerHeatPart_holds (α : ℝ) (_hα : 1 < α) : PowerHeatPartStatement α :=
  ⟨fun _ hf a t => aestronglyMeasurable_powerHeatPart α hf a t,
    fun r _ _ ht f => fracNormSq_powerHeatPart_le α r ht f,
    fun _ _ hf h _ _ t₀ ht₀ => tendsto_hsNormSq_powerHeatPart α hf h t₀ ht₀⟩

end Breakdown.SmoothFlow
