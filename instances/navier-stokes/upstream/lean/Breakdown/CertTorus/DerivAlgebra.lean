import Breakdown.CertTorus.RegularStatements

open MeasureTheory Filter

noncomputable section

namespace Breakdown.FarField

open Freq

private theorem symX_add_smul_ae (x x' : X) (c : ℝ) :
    symX (x + c • x') =ᵐ[volume] fun ξ => symX x ξ + c • symX x' ξ := by
  unfold symX
  rw [Submodule.coe_add, Submodule.coe_smul]
  filter_upwards [Lp.coeFn_add (x : L2C) (c • (x' : L2C)), Lp.coeFn_smul c (x' : L2C)] with ξ h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply]

private theorem monoSymbol_fin_zero (α : Fin 0 → Fin 3) (ξ : Space) : monoSymbol α ξ = 1 := by
  simp [monoSymbol]

private theorem monoSymbol_comp_perm {n : ℕ} (α : Fin n → Fin 3) (σ : Equiv.Perm (Fin n)) (ξ : Space) :
    monoSymbol (α ∘ σ) ξ = monoSymbol α ξ := by
  unfold monoSymbol
  exact Equiv.prod_comp σ (fun i => (((2 * Real.pi * ξ (α i) : ℝ) : ℂ) * Complex.I))

private theorem monoSymbol_append {m n : ℕ} (α : Fin m → Fin 3) (β : Fin n → Fin 3) (ξ : Space) :
    monoSymbol (Fin.append α β) ξ = monoSymbol α ξ * monoSymbol β ξ := by
  unfold monoSymbol
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem derivAlgebra_holds : DerivAlgebra := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n α x y y' hy hy'
    unfold IsDerivX at hy hy'
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hy, hy'] with ξ h h'
    exact h.trans h'.symm
  · intro α x
    unfold IsDerivX
    exact Filter.Eventually.of_forall fun ξ => by rw [monoSymbol_fin_zero, one_smul]
  · intro n α x y x' y' c hy hy'
    unfold IsDerivX at hy hy' ⊢
    filter_upwards [symX_add_smul_ae x x' c, symX_add_smul_ae y y' c, hy, hy'] with ξ h1 h2 h3 h4
    rw [h2, h1, h3, h4, smul_add, smul_comm (monoSymbol α ξ) c]
  · intro n α σ x y hy
    unfold IsDerivX at hy ⊢
    filter_upwards [hy] with ξ h
    rw [h, monoSymbol_comp_perm]
  · intro m n α β x y z hy hz
    unfold IsDerivX at hy hz ⊢
    filter_upwards [hy, hz] with ξ h1 h2
    rw [h2, h1, smul_smul, monoSymbol_append, mul_comm]

end Breakdown.FarField
