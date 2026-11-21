import Mathlib
import Breakdown.FracCell.StatementDefs

open Matrix

noncomputable section

namespace Breakdown.CellCert.Finite

def IsStateBound {V : Type*} {a b : ℕ} (Q : V → ℝ) (z₀ : V → Fin a → ℝ) (L : Matrix (Fin a) (Fin b) ℝ)
    (Ψ : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ) : Prop :=
  ∀ (x : V) (u : Fin b → ℝ), quadValue Ψ (Sum.elim (z₀ x + L *ᵥ u) u) ≤ Q x

namespace TreeCertificate

variable {a b : ℕ} (T : TreeCertificate a b)

end TreeCertificate

end Breakdown.CellCert.Finite
