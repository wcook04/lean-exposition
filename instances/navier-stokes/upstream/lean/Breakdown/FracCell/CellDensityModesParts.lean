import Breakdown.FracCell.StCellBound
import Breakdown.FracCell.CellDensityModesSolid

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def DensityIntegrableStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox), IsCellBox K → IsAxisymmetricWeight c K → IsModelMirror c K → K.solid ⊆ c.cellRegion →
    ∀ x : FieldTuple k, IsAdmissible c x →
      IntegrableOn (CellSplit.localDensity c α x) K.solid ∧
        ∀ i, IntegrableOn (fun y => entryInner (x.2.1 y) (c.modelPinField i y)) K.solid

def DensityMirrorStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox), IsCellBox K → IsAxisymmetricWeight c K → IsModelMirror c K → K.solid ⊆ c.cellRegion →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ᵐ y ∂volume, y ∈ K.solid → CellSplit.localDensity c α x (mirror y) = CellSplit.localDensity c α x y) ∧
        ∀ i, ∀ᵐ y ∂volume, y ∈ K.solid → entryInner (x.2.1 (mirror y)) (c.modelPinField i (mirror y))
          = entryInner (x.2.1 y) (c.modelPinField i y)

def DensitySliceStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox), IsCellBox K → IsAxisymmetricWeight c K → IsModelMirror c K → K.solid ⊆ c.cellRegion →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ᵐ p ∂(volume.restrict K.rect),
        (∫ θ in (0 : ℝ)..(2 * π), CellSplit.localDensity c α x (cylPoint p.1 θ p.2))
          = 2 * π * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
            + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p)) ∧
      ∀ i, ∀ᵐ p ∂(volume.restrict K.rect),
        (∫ θ in (0 : ℝ)..(2 * π), entryInner (x.2.1 (cylPoint p.1 θ p.2)) (c.modelPinField i (cylPoint p.1 θ p.2)))
          = 2 * π * modeFieldPair c x.2.1 (c.modelPinField i) p

theorem cellDensityModes_of_parts (h₁ : DensityIntegrableStatement) (h₂ : DensityMirrorStatement)
    (h₃ : DensitySliceStatement) : CellDensityModesStatement := by
  intro α hα₁ hα₂ k N c hc K hK hw hmm hsub x hx
  obtain ⟨hi₁, hi₂⟩ := h₁ α hα₁ hα₂ c hc K hK hw hmm hsub x hx
  obtain ⟨hm₁, hm₂⟩ := h₂ α hα₁ hα₂ c hc K hK hw hmm hsub x hx
  obtain ⟨hs₁, hs₂⟩ := h₃ α hα₁ hα₂ c hc K hK hw hmm hsub x hx
  refine ⟨?_, fun i => ?_⟩
  · rw [FracInternal.CellDensityModesSolid.solid_formula K hK _ hi₁ hm₁,
      integral_congr_ae (hs₁.mono fun p hp => congrArg (fun t => p.1 * t) hp)]
    have e : ∀ p : ℝ × ℝ, ∀ t : ℝ, p.1 * (2 * π * t) = 2 * π * (p.1 * t) := fun p t => by ring
    simp only [e]
    rw [integral_const_mul]
    ring
  · rw [FracInternal.CellDensityModesSolid.solid_formula K hK _ (hi₂ i) (hm₂ i),
      integral_congr_ae ((hs₂ i).mono fun p hp => congrArg (fun t => p.1 * t) hp)]
    have e : ∀ p : ℝ × ℝ, ∀ t : ℝ, p.1 * (2 * π * t) = 2 * π * (p.1 * t) := fun p t => by ring
    simp only [e]
    rw [integral_const_mul]
    ring


end CellAnalysis

end CellCert

end Breakdown
