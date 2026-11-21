import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem applyNorm_aemeasurable {A : ℝ → Space → (Space →L[ℝ] Space)} {x : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hx : AEStronglyMeasurable (fun z : ℝ × Space => x z.1 z.2) volume) :
    AEMeasurable (fun z : ℝ × Space => ‖A z.1 z.2 (x z.1 z.2)‖) volume := by
  have hc : Continuous (fun p : (Space →L[ℝ] Space) × Space => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.comp_aestronglyMeasurable (hA.prodMk hx)).norm.aemeasurable

theorem gapGradCoeff_nonneg (w₀ : ℝ) (b : Bool) : 0 ≤ gapGradCoeff w₀ b := by
  unfold gapGradCoeff supBoundFactor
  split <;> positivity

theorem pairSum_le (hsum : PeriodSumBoundHolds) (f₀ f₁ : ℝ → Space → ℝ) (c₀ c₁ E : ℝ)
    (hE : 0 ≤ E) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hm₀ : AEMeasurable (fun z : ℝ × Space => f₀ z.1 z.2) volume)
    (hm₁ : AEMeasurable (fun z : ℝ × Space => f₁ z.1 z.2) volume)
    (hn₀ : ∀ σ y, 0 ≤ f₀ σ y) (hn₁ : ∀ σ y, 0 ≤ f₁ σ y)
    (hb₀ : periodLIntegral (fun σ y => f₀ σ y ^ 2) ≤ ENNReal.ofReal (c₀ ^ 2 * E))
    (hb₁ : periodLIntegral (fun σ y => f₁ σ y ^ 2) ≤ ENNReal.ofReal (c₁ ^ 2 * E)) :
    periodLIntegral (fun σ y => (f₀ σ y + f₁ σ y) ^ 2) ≤ ENNReal.ofReal ((c₀ + c₁) ^ 2 * E) := by
  have hc : ∀ a, 0 ≤ (![c₀, c₁] : Fin 2 → ℝ) a := Fin.forall_fin_two.2 ⟨hc₀, hc₁⟩
  have hm : ∀ a, AEMeasurable (fun z : ℝ × Space => (![f₀, f₁] : Fin 2 → ℝ → Space → ℝ) a z.1 z.2)
      volume := Fin.forall_fin_two.2 ⟨hm₀, hm₁⟩
  have hn : ∀ a σ y, 0 ≤ (![f₀, f₁] : Fin 2 → ℝ → Space → ℝ) a σ y :=
    Fin.forall_fin_two.2 ⟨hn₀, hn₁⟩
  have hF : ∀ σ y, 0 ≤ f₀ σ y + f₁ σ y := fun σ y => add_nonneg (hn₀ σ y) (hn₁ σ y)
  have hle : ∀ σ y, f₀ σ y + f₁ σ y ≤ ∑ a, (![f₀, f₁] : Fin 2 → ℝ → Space → ℝ) a σ y := by
    intro σ y
    simp [Fin.sum_univ_two]
  have hb : ∀ a, periodLIntegral (fun σ y => (![f₀, f₁] : Fin 2 → ℝ → Space → ℝ) a σ y ^ 2) ≤
      ENNReal.ofReal ((![c₀, c₁] : Fin 2 → ℝ) a ^ 2 * E) := Fin.forall_fin_two.2 ⟨hb₀, hb₁⟩
  have h := hsum 2 (fun σ y => f₀ σ y + f₁ σ y) ![f₀, f₁] ![c₀, c₁] E hE hc hm hn hF hle hb
  simpa [Fin.sum_univ_two] using h

end Internal

theorem gapTransferBridge_of (hsup : GapSupTermHolds) (hgrad : GapGradTermHolds)
    (hglue : PeriodGlueHolds) : GapTransferBridgeHolds := by
  obtain ⟨hsum, -, -, -⟩ := hglue
  intro k d r hst hcert q hq v G H g hpert
  have hv := hcert.valid
  have hw : 0 < d.weight := hst.weight_pos
  rw [hst.weightFn_const]
  set E := weightedEnergy (fun _ => d.weight) G H with hE
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  set c : Fin r.count → ℝ := fun a =>
    gapGradCoeff d.weight (r.cubicForm a) * r.gradNum a + r.supNum a / Real.sqrt d.weight with hc
  have hc0 : ∀ a, 0 ≤ c a := fun a =>
    add_nonneg (mul_nonneg (Internal.gapGradCoeff_nonneg _ _) (hv.gradNum_nonneg a))
      (div_nonneg (hv.supNum_nonneg a) (Real.sqrt_nonneg _))
  have hpiece : ∀ a, periodLIntegral (fun σ y =>
      (‖r.pieceGrad a q σ y (v σ y)‖ + ‖G σ y (r.piece a q σ y)‖) ^ 2) ≤
      ENNReal.ofReal (c a ^ 2 * E) := by
    intro a
    exact Internal.pairSum_le hsum _ _ _ _ E hE0
      (mul_nonneg (Internal.gapGradCoeff_nonneg _ _) (hv.gradNum_nonneg a))
      (div_nonneg (hv.supNum_nonneg a) (Real.sqrt_nonneg _))
      (Internal.applyNorm_aemeasurable (hv.pieceGrad_measurable a q hq).aestronglyMeasurable
        hpert.measurable_velocity)
      (Internal.applyNorm_aemeasurable hpert.measurable_gradient
        (hv.piece_measurable a q hq).aestronglyMeasurable)
      (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      (hgrad d.symmetries (d.period q) d.weight (r.gradNum a) (r.cubicForm a) v G H g
        (fun σ y => r.pieceGrad a q σ y) hw (hv.gradNum_nonneg a) hpert
        (hv.pieceGrad_measurable a q hq) (fun σ => hv.piece_grad a q hq σ))
      (hsup d.symmetries (d.period q) d.weight (r.supNum a) v G H g
        (fun σ y => r.piece a q σ y) hw (hv.supNum_nonneg a) hpert
        (fun σ y => hv.piece_sup a q hq σ y))
  have hmain := hsum r.count
    (fun σ y => ‖G σ y (d.profile q σ y - d.model q σ y)
      + (fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.model q σ) y) (v σ y)‖)
    (fun a σ y => ‖r.pieceGrad a q σ y (v σ y)‖ + ‖G σ y (r.piece a q σ y)‖) c E hE0 hc0
    (fun a => (Internal.applyNorm_aemeasurable (hv.pieceGrad_measurable a q hq).aestronglyMeasurable
        hpert.measurable_velocity).add
      (Internal.applyNorm_aemeasurable hpert.measurable_gradient
        (hv.piece_measurable a q hq).aestronglyMeasurable))
    (fun _ _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ _ => norm_nonneg _)
    (fun σ y => by
      rw [hv.decompose q hq σ y, hv.decompose_grad q hq σ y, map_sum,
        sum_apply, ← Finset.sum_add_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      exact (norm_add_le _ _).trans (le_of_eq (add_comm _ _)))
    hpiece
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hs0 : 0 ≤ ∑ a, c a := Finset.sum_nonneg fun a _ => hc0 a
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hcert.sum_le 2) hE0


end CertReduction

end Breakdown
