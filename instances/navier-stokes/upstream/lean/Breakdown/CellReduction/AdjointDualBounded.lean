import Breakdown.CellReduction.AdjointStatements

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace AdjointDefect

theorem dualBoundedBound_of_parts (h1 : RemainderPlainHolds) (h2 : RemainderAzimuthalHolds) :
    DualBoundedBoundHolds := by
  intro R ρ hR
  obtain ⟨R₁, R₂, ρ₁, ρ₂, hsplit, hA, hP, hρ⟩ := hR
  intro v G hv hG hweak hsix hfin
  obtain ⟨hi₁, ho₁, hb₁⟩ := h2 R₁ ρ₁ hA v G hv hG hweak hsix hfin
  obtain ⟨hi₂, ho₂, hb₂⟩ := h1 R₂ ρ₂ hP v G hv hG hweak hsix hfin
  have hpt : ∀ σ y, inner ℝ (v σ y) (R σ y) = inner ℝ (v σ y) (R₁ σ y) + inner ℝ (v σ y) (R₂ σ y) := by
    intro σ y
    rw [hsplit σ y, inner_add_right]
  have hae : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      Integrable (fun y => inner ℝ (v σ y) (R σ y)) ∧
        ∫ y, inner ℝ (v σ y) (R σ y) =
          (∫ y, inner ℝ (v σ y) (R₁ σ y)) + ∫ y, inner ℝ (v σ y) (R₂ σ y) := by
    filter_upwards [hi₁, hi₂] with σ hσ₁ hσ₂
    have hfun : (fun y => inner ℝ (v σ y) (R σ y)) =
        fun y => inner ℝ (v σ y) (R₁ σ y) + inner ℝ (v σ y) (R₂ σ y) := funext (hpt σ)
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hσ₁.add hσ₂
    · rw [hfun]
      exact integral_add hσ₁ hσ₂
  have hsum : IntegrableOn (fun σ => (∫ y, inner ℝ (v σ y) (R₁ σ y)) + ∫ y, inner ℝ (v σ y) (R₂ σ y))
      (Set.Icc (0 : ℝ) 1) := ho₁.add ho₂
  have heq : (fun σ => ∫ y, inner ℝ (v σ y) (R σ y)) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      fun σ => (∫ y, inner ℝ (v σ y) (R₁ σ y)) + ∫ y, inner ℝ (v σ y) (R₂ σ y) := by
    filter_upwards [hae] with σ hσ
    exact hσ.2
  refine ⟨hae.mono fun σ hσ => hσ.1, hsum.congr_fun_ae heq.symm, ?_⟩
  have hsplitInt : periodInnerIntegral v R = periodInnerIntegral v R₁ + periodInnerIntegral v R₂ := by
    unfold periodInnerIntegral
    rw [integral_congr_ae heq]
    exact integral_add ho₁ ho₂
  have hnn : 0 ≤ gradientNorm G := Real.sqrt_nonneg _
  rw [hsplitInt]
  calc |periodInnerIntegral v R₁ + periodInnerIntegral v R₂|
      ≤ |periodInnerIntegral v R₁| + |periodInnerIntegral v R₂| := abs_add_le _ _
    _ ≤ ρ₁ * gradientNorm G + ρ₂ * gradientNorm G := add_le_add hb₁ hb₂
    _ = (ρ₁ + ρ₂) * gradientNorm G := by ring
    _ ≤ ρ * gradientNorm G := mul_le_mul_of_nonneg_right hρ hnn

end AdjointDefect

end Breakdown
