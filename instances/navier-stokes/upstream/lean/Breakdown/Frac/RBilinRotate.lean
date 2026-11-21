import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.BilinRotate

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

open Internal.BilinRotate

private theorem radialOp_rot (c : Space → ℝ) (hc : ∀ (R : Space ≃ₗᵢ[ℝ] Space) ξ, c (R.symm ξ) = c ξ)
    (R : Space ≃ₗᵢ[ℝ] Space) (g : L2C) :
    fieldOp id (fun ξ => c ξ • ContinuousLinearMap.id ℝ CSpace) (rotL2 R g) =
      rotL2 R (fieldOp id (fun ξ => c ξ • ContinuousLinearMap.id ℝ CSpace) g) := by
  by_cases h : ∃ T, IsRealizedBy T id (fun ξ => c ξ • ContinuousLinearMap.id ℝ CSpace)
  · have e : fieldOp id (fun ξ => c ξ • ContinuousLinearMap.id ℝ CSpace) = h.choose := dif_pos h
    have hs := h.choose_spec
    rw [e]
    apply Lp.ext
    filter_upwards [hs (rotL2 R g), rotL2_ae fieldOpRealized_holds R g,
      rotL2_ae fieldOpRealized_holds R (h.choose g), ae_comp_symm R (hs g)] with ξ h1 h2 h4 h5
    rw [h1, h4, id, h2, h5]
    simp [hc R ξ, map_smul]
  · have e : fieldOp id (fun ξ => c ξ • ContinuousLinearMap.id ℝ CSpace) = 0 := dif_neg h
    rw [e]
    simp

private theorem fracPhiFactor_rot (α τ : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) :
    fracPhiFactor α τ (R.symm ξ) = fracPhiFactor α τ ξ := by
  simp [fracPhiFactor]

private theorem fracPhiX_rot (α τ : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (ψ : X) :
    (fracPhiX α τ (rotX R ψ) : Space → Space) =ᵐ[volume]
      pushForward R (fracPhiX α τ ψ : Space → Space) := by
  have e : fracPhiX α τ (rotX R ψ) = toPhys (rotL2 R
      (fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C))) := by
    rw [← radialOp_rot (fracPhiFactor α τ) (fracPhiFactor_rot α τ) R]
    simp only [fracPhiX, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      (rotation_holds R).1 ψ]
  rw [e]
  exact toPhys_rotL2 fieldOpRealized_holds R _

private theorem fracBilinForm_rot (α τ : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (u v ψ : X) :
    fracBilinForm α τ (rotX R u) (rotX R v) (rotX R ψ) = fracBilinForm α τ u v ψ := by
  unfold fracBilinForm
  rw [trilinear_congr _ _ (fracPhiX_rot α τ R ψ), trilinear_congr _ _ (fracPhiX_rot α τ R ψ),
    trilinear_rot rotation_holds fieldOpRealized_holds velocityCov_holds.1,
    trilinear_rot rotation_holds fieldOpRealized_holds velocityCov_holds.1]

theorem fracBilinRotate (α : ℝ) (h1 : FracBilinExists α) (_h2 : FracRotationAlgebra α) :
    FracBilinRotate α := by
  intro R τ u v
  by_cases hτ : 0 < τ
  · have h : 0 < τ ∧ ∃ B, FracBilinSpec α τ B := ⟨hτ, h1 τ hτ⟩
    have hs : FracBilinSpec α τ (fracBilinX α τ) := by
      have e : fracBilinX α τ = h.2.choose := dif_pos h
      rw [e]
      exact h.2.choose_spec
    refine ext_inner_right ℝ fun ψ => ?_
    obtain ⟨φ, rfl⟩ : ∃ φ, rotX R φ = ψ := ⟨(rotX R).symm ψ, (rotX R).apply_symm_apply ψ⟩
    rw [LinearIsometryEquiv.inner_map_map, hs, hs, fracBilinForm_rot]
  · have h0 : fracBilinX α τ = 0 := dif_neg (fun h => hτ h.1)
    simp [h0]

end Breakdown.Freq
