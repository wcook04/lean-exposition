import Breakdown.Uniqueness.RegGlueAux
import Breakdown.Uniqueness.RegLocal
import Breakdown.Uniqueness.RegPersist
import Breakdown.Uniqueness.RegUnique
import Breakdown.Uniqueness.RegConcat
import Breakdown.Uniqueness.RegApriori
import Breakdown.Uniqueness.RegPhys
import Breakdown.Uniqueness.RegBounds
import Breakdown.Uniqueness.RegInitial
import Breakdown.Uniqueness.RegIdentify
import Breakdown.Uniqueness.MildUnique

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem hsNormSq_symbolOf_all {φ : Space → Space} (hφ : IsTestField φ) :
    ∀ m, hsNormSq m (symbolOf φ) < ⊤ := fun m => hsNormSq_symbolOf_lt_top hφ m

set_option maxHeartbeats 2000000 in
private theorem norm_kernel_le (Rlz : Realization X) (hK : ∀ τ, Rlz.F.K τ = bilinX τ)
    (hBB : BilinBound) : ∀ τ, 0 < τ → ‖Rlz.F.K τ‖ ≤ hBB.choose * τ ^ (-(3 / 4 : ℝ)) := by
  intro τ hτ
  rw [hK]
  exact ContinuousLinearMap.opNorm_le_bound₂ _
    (mul_nonneg hBB.choose_spec.1 (Real.rpow_nonneg hτ.le _)) (hBB.choose_spec.2 τ hτ)

private theorem embedX_physField_eq_of_flow (Rlz : Realization X) (hG : ∀ t, Rlz.F.G t = heatX t)
    (hK : ∀ τ, Rlz.F.K τ = bilinX τ) (hE : ∀ f, Rlz.embed f = embedX f) (hH : HeatSemigroup)
    (hR : FieldOpRealized) (hH1 : H1Consistency) (hB : BilinH1Formula) (hBE : BilinExists)
    (hBB : BilinBound) {φ : Space → Space} (hφ : IsTestField φ) {u : ℝ → X} {T : ℝ}
    (hu : Rlz.F.IsMildOnIcc u 0 T) (hu0 : u 0 = Rlz.embed φ) {s : ℝ} (hs : s ∈ Icc 0 T)
    {F : ℝ → Space → CSpace} (hF : IsSymbolFlow 3 F (symbolOf φ) s) :
    ∀ t ∈ Icc 0 s, embedX (physField (F t)) = u t := by
  have hall := isHsCurve_of_flow hF (hsNormSq_symbolOf_all hφ)
  have hv0 : embedX (physField (F 0)) = u 0 := by
    rw [hF.2.2.2, physField_symbolOf hφ, hu0, hE]
  rcases eq_or_lt_of_le hs.1 with h | h
  · intro t ht
    have ht0 : t = 0 := le_antisymm (h ▸ ht.2) ht.1
    rw [ht0]
    exact hv0
  · have hmild := isMildX_embedX_physField hH hR hH1 hB hBE h hall hF.2.1 hF.2.2.1
    have hmild' : Rlz.F.IsMildOnIcc (fun t => embedX (physField (F t))) 0 s := by
      refine ⟨hmild.1, fun t ht => ?_⟩
      simp only [hG, hK]
      exact hmild.2 t ht
    have hus : Rlz.F.IsMildOnIcc u 0 s :=
      ⟨hu.1.mono (Icc_subset_Icc le_rfl hs.2), fun t ht => hu.2 t ⟨ht.1, ht.2.trans hs.2⟩⟩
    exact Rlz.F.eq_of_isMildOnIcc (norm_kernel_le Rlz hK hBB) hmild' hus hv0

theorem mildRegular_of_freq (Rlz : Realization X) (hG : ∀ t, Rlz.F.G t = heatX t)
    (hK : ∀ τ, Rlz.F.K τ = bilinX τ) (hE : ∀ f, Rlz.embed f = embedX f) (hH : HeatSemigroup)
    (hR : FieldOpRealized) (hH1 : H1Consistency) (hB : BilinH1Formula) (hBE : BilinExists)
    (hBB : BilinBound) : MildRegular Rlz velocity := by
  intro φ hφ u T hT hu hu0
  have h0 := hsNormSq_symbolOf_all hφ
  have hid : ∀ s ∈ Icc 0 T, ∀ F, IsSymbolFlow 3 F (symbolOf φ) s → ∀ t ∈ Icc 0 s,
      embedX (physField (F t)) = u t := fun s hs F hF =>
    embedX_physField_eq_of_flow Rlz hG hK hE hH hR hH1 hB hBE hBB hφ hu hu0 hs hF
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.1
  have hH' : ∀ s ∈ Icc 0 T, ∀ F, IsSymbolFlow 3 F (symbolOf φ) s → ∀ t ∈ Icc 0 s,
      homNormSq 1 (F t) ≤ ENNReal.ofReal (C ^ 2 / (4 * π ^ 2)) := by
    intro s hs F hF t ht
    have hall := isHsCurve_of_flow hF h0
    have heq := hid s hs F hF t ht
    have hn := norm_embedX_physField_sq hR ((hall 0).1 t ht).1 (hF.2.2.1 t ht)
      (fun m => ((hall m).1 t ht).2)
    rw [heq] at hn
    have hfin : homNormSq 1 (F t) < ⊤ :=
      (homNormSq_one_le_hsNormSq (F t)).trans_lt ((hall 1).1 t ht).2
    have hpi : 0 < 4 * π ^ 2 := by positivity
    have hr : (homNormSq 1 (F t)).toReal = ‖u t‖ ^ 2 / (4 * π ^ 2) := by
      rw [hn]
      field_simp
    rw [← ENNReal.ofReal_toReal hfin.ne, hr]
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hpi.le)
    exact pow_le_pow_left₀ (norm_nonneg _) (hC t ⟨ht.1, ht.2.trans hs.2⟩) 2
  obtain ⟨F, hF⟩ := exists_symbolFlow_of_homBound (aestronglyMeasurable_symbolOf hφ)
    (isSolenoidalSymbol_symbolOf hφ) (h0 3) hT hH'
  have hall := isHsCurve_of_flow hF h0
  refine ⟨fun t => physField (F t), fun t => physScalar (pressureSymbol (F t)),
    isSolutionOn_physField hT hall hF.2.1 hF.2.2.1, ?_, energyBoundedOn_physField (hall 3) hF.2.2.1,
    gradientBoundedOn_physField (hall 4), ?_⟩
  · show physField (F 0) = φ
    rw [hF.2.2.2]
    exact physField_symbolOf hφ
  · intro t ht
    rw [← hid T ⟨hT.le, le_rfl⟩ F hF t ht]
    exact (hH1 _ (isH1Field_physField ((hall 0).1 t ht).1 (hF.2.2.1 t ht)
      (fun m => ((hall m).1 t ht).2))).2.1

end Breakdown.SmoothFlow
