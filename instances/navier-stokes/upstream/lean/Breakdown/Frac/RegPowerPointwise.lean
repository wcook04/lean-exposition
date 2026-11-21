import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegAprioriAuxEnergyPart1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem power_hasDerivWithinAt_apply {T : ℝ} (hT : 0 < T) {α : ℝ} {F : ℝ → Space → CSpace}
    (hd : IsPowerMildSymbol α F 0 T) {ξ : Space}
    (hc : ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => F τ ξ) (powerTimeDerivSymbol α (F t) ξ) (Icc 0 T) t := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (2 * π * ‖ξ‖) ^ (2 * α) := ⟨_, rfl⟩
  have hps : powerTimeDerivSymbol α (F t) ξ = -(((c : ℝ) : ℂ) • F t ξ) + nonlinSymbol (F t) ξ := by
    simp only [powerTimeDerivSymbol, powerSymbol, hcdef]
  rw [hps]
  have hheat : ∀ u : ℝ, powerHeatSymbol α u ξ = Real.exp (-(u * c)) := by
    intro u
    simp only [powerHeatSymbol, hcdef]
  let g : ℝ → CSpace := fun s => ((Real.exp (c * s) : ℝ) : ℂ) • nonlinSymbol (F s) ξ
  have hg : ContinuousOn g (Icc 0 T) := by
    have h0 : ContinuousOn (fun s : ℝ => ((Real.exp (c * s) : ℝ) : ℂ)) (Icc 0 T) :=
      (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
    exact h0.smul hc
  let p : ℝ → ℝ := fun s => (projIcc 0 T hT.le s : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  let g' : ℝ → CSpace := fun s => g (p s)
  have hg' : Continuous g' := hg.comp_continuous hp (fun s => (projIcc 0 T hT.le s).2)
  let e : ℝ → ℂ := fun τ => ((Real.exp (-c * τ) : ℝ) : ℂ)
  let G : ℝ → CSpace := fun τ => F 0 ξ + ∫ s in (0 : ℝ)..τ, g' s
  have hpeq : ∀ τ ∈ Icc 0 T, p τ = τ := fun τ hτ => by simp [p, projIcc_of_mem _ hτ]
  have hrep : ∀ τ ∈ Icc 0 T, F τ ξ = e τ • G τ := by
    intro τ hτ
    rw [hd τ hτ ξ]
    have h1 : ∫ s in (0 : ℝ)..τ, ((powerHeatSymbol α (τ - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ =
        ∫ s in (0 : ℝ)..τ, e τ • g' s := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [uIcc_of_le hτ.1] at hs
      have hps' : p s = s := hpeq s ⟨hs.1, hs.2.trans hτ.2⟩
      simp only [g', g, hps', e, hheat, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 4
      ring
    rw [h1, intervalIntegral.integral_smul, smul_add]
    congr 3
    rw [hheat]
    ring_nf
  have he : HasDerivAt e ((Real.exp (-c * t) * (-c) : ℝ) : ℂ) t := by
    have : HasDerivAt (fun τ => Real.exp (-c * τ)) (Real.exp (-c * t) * (-c)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-c)).exp
    exact this.ofReal_comp
  have hG : HasDerivAt G (g' t) t :=
    ((hg'.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (F 0 ξ)
  have hder := (he.smul hG).hasDerivWithinAt (s := Icc 0 T)
  refine (hder.congr_of_mem hrep ht).congr_deriv ?_
  have h1 : e t • g' t = nonlinSymbol (F t) ξ := by
    simp only [g', g, hpeq t ht, e, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -c * t + c * t = 0 by ring]
    simp
  have h2 : ((Real.exp (-c * t) * (-c) : ℝ) : ℂ) • G t = -(((c : ℝ) : ℂ) • (e t • G t)) := by
    rw [smul_smul, ← neg_smul]
    congr 1
    simp only [e]
    push_cast
    ring
  rw [h1, h2, ← hrep t ht, add_comm]

theorem powerPointwiseDeriv (α : ℝ) (_hα : 1 < α) : PowerPointwiseDerivStatement α :=
  fun _ hT _ hd _ hc _ ht => power_hasDerivWithinAt_apply hT hd hc ht

private theorem power_aesm_uncurry_of_continuousOn {a b : ℝ} (hab : a ≤ b)
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

theorem powerAEMeas_of (α : ℝ) (_hα : 1 < α) (h1 : PowerPointwiseDerivStatement α) :
    PowerAEMeasStatement α := by
  intro T hT F hF hd
  have hN := continuousOn_nonlinSymbol_of_hsCurve hF
  have hc : ∀ ξ, ContinuousOn (fun t => F t ξ) (Icc 0 T) := fun ξ t ht =>
    (h1 T hT F hd ξ (hN ξ) t ht).continuousWithinAt
  have hm : ∀ t ∈ Icc 0 T, AEStronglyMeasurable (F t) volume := fun t ht => (hF.1 t ht).1
  exact (power_aesm_uncurry_of_continuousOn hT.le hc hm).enorm

end Breakdown.SmoothFlow
