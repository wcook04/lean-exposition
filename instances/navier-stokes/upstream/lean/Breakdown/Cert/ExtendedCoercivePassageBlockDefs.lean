import Breakdown.Cert.ExtendedCoerciveMinorant

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

namespace Internal.PieceDensityPassageWeak

open Internal.Minorant

section Block

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)

def blockGain (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ :=
  ∑ β : Fin nE, (m.epsP β).wt y * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.velAmp v κ σ y)
    * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y)

def pieceBlockLower (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ :=
  pieceBlockWith m W 0 v G H σ y - vortGradSupLower HW y * blockGain m v G σ y

theorem vortGradSupWith_zero (y : Space) :
    vortGradSupWith (0 : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) y = 0 := by
  have hz : ∀ p : ℝ × ℝ, ‖vortGradMap ((0 : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) p.1
      (axialRot p.2 y))‖ = 0 := fun p => by
    simp [vortGradMap, vortGrad]
  unfold vortGradSupWith
  simp only [hz, ciSup_const]

theorem blockGain_nonneg (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : 0 ≤ blockGain m v G σ y :=
  Finset.sum_nonneg fun β _ => mul_nonneg (mul_nonneg (hE β y) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem pieceBlockWith_eq (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    pieceBlockWith m W HW v G H σ y
      = -(-pieceBlockWith m W 0 v G H σ y + vortGradSupWith HW y * blockGain m v G σ y) := by
  have e : ∀ β, pieceEpsBlockWith m W HW v G H β σ y = pieceEpsBlockWith m W 0 v G H β σ y
      - vortGradSupWith HW y * ((m.epsP β).wt y
        * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.velAmp v κ σ y)
        * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y)) := by
    intro β
    unfold pieceEpsBlockWith
    rw [vortGradSupWith_zero]
    ring
  unfold pieceBlockWith blockGain
  rw [Finset.sum_congr rfl fun β _ => e β, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end Block

end Internal.PieceDensityPassageWeak

end CoerciveWeak

end Breakdown
