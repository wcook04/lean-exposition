import Breakdown.CertCell.StatementDefs

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem modelPlaneValues_eq_zero_of_not_mem (D : CellLayerData k C nE nM) (K : Fin D.mesh.count)
    (α : ℤ × ℤ)
    (hv : α ∉ D.model.velocity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
      D.model.velocity.planeValue D.mesh.box K α a p = 0)
    (hw : α ∉ D.model.vorticity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
      D.model.vorticity.planeValue D.mesh.box K α a p = 0)
    (hs : α ∉ D.model.strain.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
      D.model.strain.planeValue D.mesh.box K α a b p = 0)
    (hg : α ∉ D.model.vorticityGrad.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
      D.model.vorticityGrad.planeValue D.mesh.box K α a b p = 0)
    (hm : α ∉ modelLabels D K) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    (∀ a, D.model.velocity.planeValue D.mesh.box K α a p = 0) ∧
      (∀ a, D.model.vorticity.planeValue D.mesh.box K α a p = 0) ∧
      (∀ a b, D.model.strain.planeValue D.mesh.box K α a b p = 0) ∧
      (∀ a b, D.model.vorticityGrad.planeValue D.mesh.box K α a b p = 0) := by
  classical
  by_cases hu : α ∈ D.model.velocity.labels K ∪ D.model.vorticity.labels K ∪ D.model.strain.labels K
      ∪ D.model.vorticityGrad.labels K
  · have h : ¬ ∃ q ∈ (D.mesh.box K).rect,
        (∃ a, D.model.velocity.planeValue D.mesh.box K α a q ≠ 0) ∨
        (∃ a, D.model.vorticity.planeValue D.mesh.box K α a q ≠ 0) ∨
        (∃ a b, D.model.strain.planeValue D.mesh.box K α a b q ≠ 0) ∨
        (∃ a b, D.model.vorticityGrad.planeValue D.mesh.box K α a b q ≠ 0) := fun h =>
      hm (by unfold modelLabels; exact Finset.mem_filter.2 ⟨hu, h⟩)
    push_neg at h
    exact h p hp
  · simp only [Finset.mem_union, not_or] at hu
    exact ⟨hv hu.1.1.1 p hp, hw hu.1.1.2 p hp, hs hu.1.2 p hp, hg hu.2 p hp⟩

end Assembly

end CertCell

end Breakdown
