import Breakdown.Frac.StSpaceReg
import Breakdown.Frac.StSpaceBlowup
import Breakdown.Transfer.Exports
import Breakdown.FreqTr.Realization
import Breakdown.Uniqueness.RegEmbed
import Breakdown.Uniqueness.RegBounds
import Breakdown.Uniqueness.RegInitial
import Breakdown.Uniqueness.RegGlueAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown

open Breakdown.Freq Breakdown.SmoothFlow

private theorem embedX_physField_eq_of_powerFlow {α : ℝ} (h1 : SmoothFlow.PowerFlowStatement α)
    (h2 : SmoothFlow.PowerIdentifyStatement α) (F : ScaledMildFramework Freq.X (dilExponent α))
    (hG : F.G = Freq.fracHeatX α) (hK : F.K = Freq.fracBilinX α) {φ : Space → Space}
    (hφ : IsTestField φ) {u : ℝ → Freq.X} {T : ℝ} (hu : F.IsMildOnIcc u 0 T)
    (hu0 : u 0 = Freq.embedX φ) {s : ℝ} (hs : s ∈ Icc 0 T) {W : ℝ → Space → CSpace}
    (hW : SmoothFlow.IsPowerSymbolFlow α 3 W (symbolOf φ) s) :
    ∀ t ∈ Icc 0 s, embedX (physField (W t)) = u t := by
  have hall := h1.1 W (symbolOf φ) s hW (fun m => hsNormSq_symbolOf_lt_top hφ m)
  have hv0 : embedX (physField (W 0)) = u 0 := by
    rw [hW.2.2.2, physField_symbolOf hφ, hu0]
  rcases eq_or_lt_of_le hs.1 with h | h
  · intro t ht
    have ht0 : t = 0 := le_antisymm (h ▸ ht.2) ht.1
    rw [ht0]
    exact hv0
  · have hmild : IsFracMildX α (fun t => embedX (physField (W t))) 0 s :=
      h2 s h W hall hW.2.1 hW.2.2.1
    obtain ⟨hc, hm⟩ := hmild
    have hmild' : F.IsMildOnIcc (fun t => embedX (physField (W t))) 0 s := by
      refine ⟨hc, fun t ht => ?_⟩
      simp only [hG, hK]
      exact hm t ht
    have hus : F.IsMildOnIcc u 0 s :=
      ⟨hu.1.mono (Icc_subset_Icc le_rfl hs.2), fun t ht => hu.2 t ⟨ht.1, ht.2.trans hs.2⟩⟩
    have huniq := (mildUnique Freq.X F.toHeatBilinear (fun t => embedX (physField (W t))) u 0 s).2
    exact huniq ((F.isMildOnIcc_iff _ _ _).1 hmild') ((F.isMildOnIcc_iff _ _ _).1 hus) hv0

theorem fracMildRegular_of (α : ℝ) (_hα : 1 < α) (_hα2 : α < 3 / 2)
    (h1 : SmoothFlow.PowerFlowStatement α) (h2 : SmoothFlow.PowerIdentifyStatement α)
    (h3 : SmoothFlow.PowerSolutionOnStatement α) (_hB : Freq.FracBilinBound α) :
    FracMildRegularStatement α := by
  intro F hG hK φ hφ u T hT hu hu0
  have h0 : ∀ m, hsNormSq m (symbolOf φ) < ⊤ := fun m => hsNormSq_symbolOf_lt_top hφ m
  have hid : ∀ s ∈ Icc 0 T, ∀ W, SmoothFlow.IsPowerSymbolFlow α 3 W (symbolOf φ) s →
      ∀ t ∈ Icc 0 s, embedX (physField (W t)) = u t := fun s hs W hW =>
    embedX_physField_eq_of_powerFlow h1 h2 F hG hK hφ hu hu0 hs hW
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.1
  have hH' : ∀ s ∈ Icc 0 T, ∀ W, SmoothFlow.IsPowerSymbolFlow α 3 W (symbolOf φ) s →
      ∀ t ∈ Icc 0 s, homNormSq 1 (W t) ≤ ENNReal.ofReal (C ^ 2 / (4 * π ^ 2)) := by
    intro s hs W hW t ht
    have hall := h1.1 W (symbolOf φ) s hW h0
    have heq := hid s hs W hW t ht
    have hn := norm_embedX_physField_sq fieldOpRealized_holds ((hall 0).1 t ht).1 (hW.2.2.1 t ht)
      (fun m => ((hall m).1 t ht).2)
    rw [heq] at hn
    have hfin : homNormSq 1 (W t) < ⊤ :=
      (homNormSq_one_le_hsNormSq (W t)).trans_lt ((hall 1).1 t ht).2
    have hpi : 0 < 4 * π ^ 2 := by positivity
    have hr : (homNormSq 1 (W t)).toReal = ‖u t‖ ^ 2 / (4 * π ^ 2) := by
      rw [hn]
      field_simp
    rw [← ENNReal.ofReal_toReal hfin.ne, hr]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hpi.le)
    exact pow_le_pow_left₀ (norm_nonneg _) (hC t ⟨ht.1, ht.2.trans hs.2⟩) 2
  obtain ⟨W, hW⟩ := h1.2 (symbolOf φ) (aestronglyMeasurable_symbolOf hφ)
    (isSolenoidalSymbol_symbolOf hφ) (h0 3) T _ hT hH'
  have hall := h1.1 W (symbolOf φ) T hW h0
  refine ⟨fun t => physField (W t), fun t => physScalar (pressureSymbol (W t)),
    h3 T hT W hall hW.2.1 hW.2.2.1, ?_, energyBoundedOn_physField (hall 3) hW.2.2.1,
    gradientBoundedOn_physField (hall 4), ?_⟩
  · show physField (W 0) = φ
    rw [hW.2.2.2]
    exact physField_symbolOf hφ
  · intro t ht
    rw [← hid T ⟨hT.le, le_rfl⟩ W hW t ht]
    exact (h1Consistency_holds _ (isH1Field_physField ((hall 0).1 t ht).1 (hW.2.2.1 t ht)
      (fun m => ((hall m).1 t ht).2))).2.1

end Breakdown
