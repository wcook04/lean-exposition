import Breakdown.Profile.StatementsPhysical
import Breakdown.Profile.StatementsFlow

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem physicalMild_holds (hdil : DecayFieldDilate) (hslice : SliceDecay) (hl2 : PhysicalL2)
    (hweak : PhysicalWeak) (hjoint : DilateJointContinuous) : PhysicalMild := by
  intro X _ _ _ Rlz W q C h hw s₀ T hT hT1
  have hlt : ∀ t ∈ Icc (0 : ℝ) T, t < 1 := fun t ht => lt_of_le_of_lt ht.2 hT1
  have hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < (1 - t)⁻¹ := fun t ht =>
    inv_pos.mpr (sub_pos.mpr (hlt t ht))
  have hne : ∀ t ∈ Icc (0 : ℝ) T, (1 - t) ≠ 0 := fun t ht =>
    (sub_pos.mpr (hlt t ht)).ne'
  have hdec : ∀ t ∈ Icc (0 : ℝ) T, IsDecayField (physicalField W s₀ t) := fun t ht =>
    hdil _ _ (hpos t ht) (hslice W q C h _)
  have hsub : ContinuousOn (fun t : ℝ => 1 - t) (Icc 0 T) :=
    continuousOn_const.sub continuousOn_id
  have hg : ContinuousOn (fun t : ℝ => ((1 - t)⁻¹, Rlz.embed (W (physicalTime s₀ t))))
      (Icc 0 T) := by
    refine ContinuousOn.prodMk (hsub.inv₀ hne) ?_
    refine hw.comp_continuousOn ?_
    exact continuousOn_const.sub (hsub.log hne)
  have hmaps : MapsTo (fun t : ℝ => ((1 - t)⁻¹, Rlz.embed (W (physicalTime s₀ t))))
      (Icc 0 T) (Ioi 0 ×ˢ univ) := fun t ht => ⟨hpos t ht, mem_univ _⟩
  have hcont : ContinuousOn (fun t => Rlz.embed (physicalField W s₀ t)) (Icc 0 T) := by
    refine ((hjoint X Rlz.F).comp hg hmaps).congr ?_
    intro t ht
    exact (Rlz.embed_dilate _ _ (hpos t ht) (hslice W q C h _)).symm
  obtain ⟨hint, htend⟩ := hl2 W q C h s₀ T hT1
  refine Rlz.mild_of_weak (physicalField W s₀) 0 T hT hdec hcont hint htend ?_ ?_
  · intro φ hφ t ht
    exact hweak W q C h s₀ t (lt_trans ht.2 hT1) φ hφ
  · intro φ hφ t ht
    exact (hweak W q C h s₀ t (hlt t ht) φ hφ).continuousAt.continuousWithinAt

end Breakdown
