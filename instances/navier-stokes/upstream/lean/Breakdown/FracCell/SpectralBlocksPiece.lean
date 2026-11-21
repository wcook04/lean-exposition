import Breakdown.FracCell.StSpectral

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def blockPart {k N : ℕ} (c : FracCellData k N) (x : Fin N → ℝ) (β : ℕ) (y : Space) : Space :=
  ∑ b ∈ Finset.univ.filter (fun b => c.blockIndex b = β), x b • c.row b y

def BlockPieceStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      ∃ (ψ : ℕ → Space → Space) (Dψ : ℕ → Space → (Space →L[ℝ] Space)),
        (∀ β, MemLp (ψ β) 2 volume ∧ AEStronglyMeasurable (Dψ β) volume ∧
          Integrable (fun y => entrySq (Dψ β y)) ∧ IsWeakGradientOf (ψ β) (Dψ β) ∧
          MemLp (fun y => blockPart c x β y - ψ β y) 2 volume) ∧
        (∀ β β', β ≠ β' →
          (∫ y, inner ℝ (blockPart c x β y - ψ β y) (blockPart c x β' y - ψ β' y)) = 0 ∧
            ∫ y, entryInner (Dψ β y) (Dψ β' y) = 0) ∧
        ∀ β, (∫ y, ‖blockPart c x β y - ψ β y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ β y)
          ≤ sd.blockSpectral β lam * ∑ b ∈ Finset.univ.filter (fun b => c.blockIndex b = β), x b ^ 2


def blockInnerValue (sd : SpectralData) (β : ℕ) (lam : ℝ) : ℝ :=
  if (sd.block β).onAxis then
    sd.axisUpper (sd.block β).degree (lam * ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2)
      + sd.intervalUpper (sd.block β).degree
          (lam * ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2 / 4)
  else
    (sd.block β).outerRadius / (sd.block β).innerRadius
      * (sd.intervalUpper (sd.block β).degree
            (lam * ((sd.block β).outerRadius - (sd.block β).innerRadius) ^ 2 / 4)
        + sd.intervalUpper (sd.block β).degree
            (lam * ((sd.block β).upperHeight - (sd.block β).lowerHeight) ^ 2 / 4)
        + ratioFn lam (((sd.block β).mode + 1 : ℝ) ^ 2 / (sd.block β).innerRadius ^ 2))

theorem blockSpectral_eq_min_inner (sd : SpectralData) (β : ℕ) (lam : ℝ) :
    sd.blockSpectral β lam = min 1 (blockInnerValue sd β lam) := by
  unfold SpectralData.blockSpectral blockInnerValue
  split <;> rfl

def BlockApproxStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ,
      ∃ (ψ : ℕ → Space → Space) (Dψ : ℕ → Space → (Space →L[ℝ] Space)),
        (∀ β, MemLp (ψ β) 2 volume ∧ AEStronglyMeasurable (Dψ β) volume ∧
          Integrable (fun y => entrySq (Dψ β y)) ∧ IsWeakGradientOf (ψ β) (Dψ β)) ∧
        (∀ β β', β ≠ β' →
          (∫ y, inner ℝ (blockPart c x β y) (ψ β' y)) = 0 ∧ (∫ y, inner ℝ (ψ β y) (ψ β' y)) = 0 ∧
            ∫ y, entryInner (Dψ β y) (Dψ β' y) = 0) ∧
        ∀ β ∈ Finset.univ.image c.blockIndex, blockInnerValue sd β lam < 1 →
          (∫ y, ‖blockPart c x β y - ψ β y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ β y)
            ≤ blockInnerValue sd β lam * ∫ y, ‖blockPart c x β y‖ ^ 2

end Spectral

end CellCert

end Breakdown
