import Breakdown.FracCell.VelocityTailSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

def LineProjSpecStatement : Prop :=
  ∀ (a b : ℝ) (ρ : ℝ → ℝ), 0 ≤ a → a < b → (ρ = (fun _ => 1) ∨ (a = 0 ∧ ρ = id)) →
    ∀ (d : ℕ) (f : ℝ → ℂ), AEStronglyMeasurable f (volume.restrict (Set.Icc a b)) →
      IntegrableOn (fun r => ρ r * ‖f r‖ ^ 2) (Set.Icc a b) →
      (∀ t : Fin (d + 1), ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - lineProj ρ a b d f r)
          * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0) ∧
      ∀ c : Fin (d + 1) → ℂ, (∀ t : Fin (d + 1), ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
          * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0) →
        ∀ x, lineProj ρ a b d f x = ∑ j, c j * (x : ℂ) ^ (j : ℕ)

def ProjRCoeffStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (d : ℕ) (s : ℝ × ℝ → ℂ),
    AEStronglyMeasurable s (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2) K.rect →
      ∃ c : Fin (d + 1) → ℝ → ℂ,
        (∀ j, AEStronglyMeasurable (c j) (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
          IntegrableOn (fun z => ‖c j z‖ ^ 2) (Set.Icc K.z₁ K.z₂)) ∧
        ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)), ∀ r : ℝ, K.projR d s (r, z) = ∑ j, c j z * (r : ℂ) ^ (j : ℕ)

def RadialTopBoundStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (Q : ℕ), 5 ≤ Q → ∀ s : ℝ × ℝ → ℂ,
    AEStronglyMeasurable s (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2) K.rect →
      K.normSqOn K.lineWeightFn (fun p => K.projR (Q - 1) s p - K.proj (Q - 1) (Q - 2) s p)
        ≤ (K.normSqOn K.lineWeightFn (K.proj (Q - 1) Q s) - K.normSqOn K.lineWeightFn (K.proj (Q - 1) (Q - 2) s))
          + K.tailNormSq Q s

def ProjOrthStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (d d' : ℕ) (s : ℝ × ℝ → ℂ),
    AEStronglyMeasurable s (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2) K.rect →
      ∀ j l : ℕ, j ≤ d → l ≤ d' →
        K.pairOn K.lineWeightFn (fun p => s p - K.proj d d' s p) (fun p => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) = 0

end CellAnalysis

end CellCert

end Breakdown
