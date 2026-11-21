import Breakdown.FracCell.StSpectral

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def BlockFamilyStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      ∃ (ψ : ℕ → Space → Space) (Dψ : ℕ → Space → (Space →L[ℝ] Space)),
        (∀ β, MemLp (ψ β) 2 volume ∧ AEStronglyMeasurable (Dψ β) volume ∧
          Integrable (fun y => entrySq (Dψ β y)) ∧ IsWeakGradientOf (ψ β) (Dψ β)) ∧
        (∀ β, MemLp (fun y => ∑ b, (if c.blockIndex b = β then x b else 0) • c.row b y - ψ β y) 2 volume) ∧
        (∀ β β', β ≠ β' →
          ∫ y, inner ℝ (∑ b, (if c.blockIndex b = β then x b else 0) • c.row b y - ψ β y)
            (∑ b, (if c.blockIndex b = β' then x b else 0) • c.row b y - ψ β' y) = 0) ∧
        (∀ β β', β ≠ β' → ∫ y, entryInner (Dψ β y) (Dψ β' y) = 0) ∧
        ∀ β, (∫ y, ‖∑ b, (if c.blockIndex b = β then x b else 0) • c.row b y - ψ β y‖ ^ 2)
            + (1 / lam) * ∫ y, entrySq (Dψ β y)
          ≤ sd.blockSpectral β lam * ∑ b, (if c.blockIndex b = β then x b ^ 2 else 0)

end Spectral

end CellCert

end Breakdown
