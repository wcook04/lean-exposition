import Breakdown.Uniqueness.RegAprioriAuxEnergyPart1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem aestronglyMeasurable_uncurry_of_continuousOn {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Space → CSpace} (hc : ∀ ξ, ContinuousOn (fun t => G t ξ) (Icc a b))
    (hm : ∀ t ∈ Icc a b, AEStronglyMeasurable (G t) volume) :
    AEStronglyMeasurable (Function.uncurry G) ((volume.restrict (Icc a b)).prod volume) := by
  classical
  set H : ℝ → Space → CSpace := fun t ξ => G (projIcc a b hab t) ξ with hH
  have hHc : ∀ ξ, Continuous fun t => H t ξ := fun ξ =>
    (hc ξ).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (projIcc a b hab t).2)
  have hHm : ∀ t, AEStronglyMeasurable (H t) volume := fun t => hm _ (projIcc a b hab t).2
  set E : Set Space := toMeasurable volume (⋃ q : ℚ, {ξ | H q ξ ≠ (hHm q).mk (H q) ξ}) with hEdef
  have hE0 : volume E = 0 := by
    rw [hEdef, measure_toMeasurable]
    exact measure_iUnion_null fun q => ae_iff.1 (hHm q).ae_eq_mk
  have hEm : MeasurableSet E := measurableSet_toMeasurable _ _
  have hsub : ∀ q : ℚ, ∀ ξ ∉ E, H q ξ = (hHm q).mk (H q) ξ := fun q ξ hξ => by
    by_contra h
    exact hξ (subset_toMeasurable _ _ (mem_iUnion.2 ⟨q, h⟩))
  set H' : ℝ → Space → CSpace := fun t ξ => if ξ ∈ E then 0 else H t ξ with hH'
  have hH'c : ∀ ξ, Continuous fun t => H' t ξ := fun ξ => by
    by_cases h : ξ ∈ E
    · simp only [H', h, if_true]; exact continuous_const
    · simp only [H', h, if_false]; exact hHc ξ
  have hH'q : ∀ q : ℚ, StronglyMeasurable (H' q) := fun q => by
    have e : H' q = fun ξ => if ξ ∈ E then 0 else (hHm q).mk (H q) ξ := by
      funext ξ
      by_cases h : ξ ∈ E
      · simp [H', h]
      · simp [H', h, hsub q ξ h]
    rw [e]
    exact StronglyMeasurable.ite hEm stronglyMeasurable_const (hHm q).stronglyMeasurable_mk
  have hH'm : ∀ t, StronglyMeasurable (H' t) := fun t => by
    obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 (Rat.denseRange_cast t)
    choose q hq using hx
    have hx' : x = fun n => ((q n : ℚ) : ℝ) := funext fun n => (hq n).symm
    refine stronglyMeasurable_of_tendsto atTop (fun n => hH'q (q n)) ?_
    rw [tendsto_pi_nhds]
    intro ξ
    have := ((hH'c ξ).tendsto t).comp hlim
    rw [hx'] at this
    exact this
  have hU : StronglyMeasurable (Function.uncurry H') :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hH'c hH'm
  refine ⟨Function.uncurry H', hU, ?_⟩
  have hs : MeasurableSet {p : ℝ × Space | p.1 ∈ Icc a b ∧ p.2 ∉ E} :=
    (measurableSet_Icc.preimage measurable_fst).inter (hEm.compl.preimage measurable_snd)
  have hae : ∀ᵐ p ∂((volume.restrict (Icc a b)).prod volume),
      p ∈ {p : ℝ × Space | p.1 ∈ Icc a b ∧ p.2 ∉ E} := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem hs]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    filter_upwards [compl_mem_ae_iff.2 hE0] with ξ hξ
    exact ⟨ht, hξ⟩
  filter_upwards [hae] with p hp
  obtain ⟨ht, hξ⟩ := hp
  simp only [Function.uncurry, H', hξ, if_false, H, projIcc_of_mem hab ht]

theorem aemeasurable_enorm_apply_of_varConst {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace}
    (hF : IsHsCurve 1 F 0 T) (hd : IsVarConstSymbol F 0 T) :
    AEMeasurable (fun p : ℝ × Space => ‖F p.1 p.2‖ₑ) ((volume.restrict (Icc 0 T)).prod volume) := by
  have hN := continuousOn_nonlinSymbol_of_hsCurve hF
  have hc : ∀ ξ, ContinuousOn (fun t => F t ξ) (Icc 0 T) := fun ξ t ht =>
    (hasDerivWithinAt_apply_of_varConst hT hd (hN ξ) ht).continuousWithinAt
  have hm : ∀ t ∈ Icc 0 T, AEStronglyMeasurable (F t) volume := fun t ht => (hF.1 t ht).1
  exact (aestronglyMeasurable_uncurry_of_continuousOn hT.le hc hm).enorm

end Breakdown.SmoothFlow
