import Breakdown.Profile.StatementsOrbit

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def EmbeddedProfileOrbit : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (C : ℝ),
    0 < P → IsSimilarityProfile W q C → (∀ s y, W (s + P) y = R (W s (R.symm y))) →
    (∃ s y, W s y ≠ 0) →
    Rlz.F.IsOrbit (Rlz.rot R) (fun s => Rlz.embed (W s)) P

def EmbeddedOrbitOfParts : Prop :=
  DecayFieldSub → SliceDecay → SliceGradientContinuous → PhysicalMild → FlowOfMild →
    EmbeddedProfileOrbit

end Breakdown
