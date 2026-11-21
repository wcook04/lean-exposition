import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

def IsH1Field (f : Space → Space) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x, divergenceAt f x = 0) ∧ MemLp f 2 volume ∧
    ∀ k, MemLp (partialField f k) 2 volume

def H1Consistency : Prop :=
  ∀ f, IsH1Field f → ofGrad f ∈ Sig ∧
    (velocity (embedX f) : Space → Space) =ᵐ[volume] f ∧
    ∀ j, (partialX j (embedX f) : Space → Space) =ᵐ[volume] partialField f j

end Breakdown.Freq
