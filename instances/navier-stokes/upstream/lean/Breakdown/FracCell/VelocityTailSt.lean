import Breakdown.FracCell.CellDataDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

open Classical in
def lineProj (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if h : ∃ c : Fin (d + 1) → ℂ, ∀ t : Fin (d + 1),
      ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0
  then ∑ j, h.choose j * (x : ℂ) ^ (j : ℕ) else 0

def OneVarTailStatement : Prop :=
  ∀ (a b : ℝ) (ρ : ℝ → ℝ), 0 ≤ a → a < b → (ρ = (fun _ => 1) ∨ (a = 0 ∧ ρ = id)) →
    ∀ d : ℕ, 2 ≤ d → ∀ F f g : ℝ → ℂ,
      (∀ x ∈ Set.Ioc a b, ∀ y ∈ Set.Ioc a b, f y = f x + ∫ t in x..y, g t) →
      ContinuousOn f (Set.Ioc a b) →
      AEStronglyMeasurable g (volume.restrict (Set.Icc a b)) →
      IntegrableOn (fun r => ρ r * ‖g r‖ ^ 2) (Set.Icc a b) →
      IntegrableOn (fun r => ρ r * ‖f r‖ ^ 2) (Set.Icc a b) →
      F =ᵐ[volume.restrict (Set.Icc a b)] f →
      ∫ r in Set.Icc a b, ρ r * (1 - ((2 * r - a - b) / (b - a)) ^ 2) *
          ‖deriv (fun x => F x - lineProj ρ a b (d - 1) F x) r‖ ^ 2
        ≤ ∫ r in Set.Icc a b, ρ r * ‖g r - lineProj ρ a b (d - 2) g r‖ ^ 2

def OneVarTailGoodStatement : Prop :=
  ∀ (a b : ℝ) (ρ : ℝ → ℝ), 0 ≤ a → a < b → (ρ = (fun _ => 1) ∨ (a = 0 ∧ ρ = id)) →
    ∀ d : ℕ, 2 ≤ d → ∀ f g : ℝ → ℂ,
      (∀ x ∈ Set.Ioc a b, ∀ y ∈ Set.Ioc a b, f y = f x + ∫ t in x..y, g t) →
      ContinuousOn f (Set.Ioc a b) →
      AEStronglyMeasurable g (volume.restrict (Set.Icc a b)) →
      IntegrableOn (fun r => ρ r * ‖g r‖ ^ 2) (Set.Icc a b) →
      IntegrableOn (fun r => ρ r * ‖f r‖ ^ 2) (Set.Icc a b) →
      IntegrableOn (fun r => ρ r * (1 - ((2 * r - a - b) / (b - a)) ^ 2) *
          ‖deriv (fun x => f x - lineProj ρ a b (d - 1) f x) r‖ ^ 2) (Set.Icc a b) ∧
      ∫ r in Set.Icc a b, ρ r * (1 - ((2 * r - a - b) / (b - a)) ^ 2) *
          ‖deriv (fun x => f x - lineProj ρ a b (d - 1) f x) r‖ ^ 2
        ≤ ∫ r in Set.Icc a b, ρ r * ‖g r - lineProj ρ a b (d - 2) g r‖ ^ 2

def ModeRadialLineStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ (n : ℤ) (a : Fin 3),
        ∀ᵐ z ∂(volume.restrict (Set.Icc K.z₁ K.z₂)), ∃ f : ℝ → ℂ,
          (∀ x ∈ Set.Ioc K.r₁ K.r₂, ∀ y ∈ Set.Ioc K.r₁ K.r₂,
            f y = f x + ∫ t in x..y, gradMode m n G a 0 (t, z)) ∧
          ContinuousOn f (Set.Ioc K.r₁ K.r₂) ∧
          AEStronglyMeasurable (fun r => gradMode m n G a 0 (r, z)) (volume.restrict (Set.Icc K.r₁ K.r₂)) ∧
          IntegrableOn (fun r => K.lineWeight r * ‖gradMode m n G a 0 (r, z)‖ ^ 2) (Set.Icc K.r₁ K.r₂) ∧
          IntegrableOn (fun r => K.lineWeight r * ‖f r‖ ^ 2) (Set.Icc K.r₁ K.r₂) ∧
          (fun r => modeVec m n v r z a) =ᵐ[volume.restrict (Set.Icc K.r₁ K.r₂)] f

def RadialProjBoundStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (Q : ℕ), 5 ≤ Q → ∀ s : ℝ × ℝ → ℂ,
    AEStronglyMeasurable s (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2) K.rect →
      Integrable (fun z => ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖s (r, z) - K.projR (Q - 2) s (r, z)‖ ^ 2)
          (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
      ∫ z in Set.Icc K.z₁ K.z₂, ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ‖s (r, z) - K.projR (Q - 2) s (r, z)‖ ^ 2
        ≤ (K.normSqOn K.lineWeightFn (K.proj Q Q s) - K.normSqOn K.lineWeightFn (K.proj (Q - 2) Q s))
          + K.tailNormSq Q s

def ModeGradSquareStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ (n : ℤ) (a b : Fin 3),
        AEStronglyMeasurable (gradMode m n G a b) (volume.restrict K.rect) ∧
        IntegrableOn (fun p => K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2) K.rect

def ModeVelSquareStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ (n : ℤ) (a : Fin 3),
        AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (volume.restrict K.rect) ∧
        IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2) K.rect

def ModeHeightLineStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ (n : ℤ) (a : Fin 3) (Q : ℕ) (r : ℝ), ∃ f : ℝ → ℂ,
        (∀ x ∈ Set.Ioc K.z₁ K.z₂, ∀ y ∈ Set.Ioc K.z₁ K.z₂,
          f y = f x + ∫ t in x..y, K.projR (Q - 1) (gradMode m n G a 2) (r, t)) ∧
        ContinuousOn f (Set.Ioc K.z₁ K.z₂) ∧
        AEStronglyMeasurable (fun z => K.projR (Q - 1) (gradMode m n G a 2) (r, z)) (volume.restrict (Set.Icc K.z₁ K.z₂)) ∧
        IntegrableOn (fun z => (1 : ℝ) * ‖K.projR (Q - 1) (gradMode m n G a 2) (r, z)‖ ^ 2) (Set.Icc K.z₁ K.z₂) ∧
        IntegrableOn (fun z => (1 : ℝ) * ‖f z‖ ^ 2) (Set.Icc K.z₁ K.z₂) ∧
        (fun z => K.projR (Q - 1) (fun p => modeVec m n v p.1 p.2 a) (r, z))
          =ᵐ[volume.restrict (Set.Icc K.z₁ K.z₂)] f

def ProjComposeStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (d : ℕ) (F : ℝ × ℝ → ℂ),
    AEStronglyMeasurable F (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect →
      ∀ r z : ℝ, lineProj (fun _ => 1) K.z₁ K.z₂ d (fun z => K.projR d F (r, z)) z = K.proj d d F (r, z)

def HeightProjBoundStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (Q : ℕ), 5 ≤ Q → ∀ s : ℝ × ℝ → ℂ,
    AEStronglyMeasurable s (volume.restrict K.rect) →
    IntegrableOn (fun p => K.lineWeight p.1 * ‖s p‖ ^ 2) K.rect →
      Integrable (fun r => K.lineWeight r * ∫ z in Set.Icc K.z₁ K.z₂, (1 : ℝ) * ‖K.projR (Q - 1) s (r, z)
            - lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => K.projR (Q - 1) s (r, z)) z‖ ^ 2)
          (volume.restrict (Set.Icc K.r₁ K.r₂)) ∧
      ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∫ z in Set.Icc K.z₁ K.z₂, (1 : ℝ) * ‖K.projR (Q - 1) s (r, z)
            - lineProj (fun _ => 1) K.z₁ K.z₂ (Q - 2) (fun z => K.projR (Q - 1) s (r, z)) z‖ ^ 2
        ≤ (K.normSqOn K.lineWeightFn (K.proj (Q - 1) Q s) - K.normSqOn K.lineWeightFn (K.proj (Q - 1) (Q - 2) s))
          + K.tailNormSq Q s

def RadialTailPartStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (Q : ℕ), 5 ≤ Q →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ (n : ℤ) (a : Fin 3),
        K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
            (CellBox.radialDeriv (fun p => modeVec m n v p.1 p.2 a
              - K.projR (Q - 1) (fun p => modeVec m n v p.1 p.2 a) p))
          ≤ (K.normSqOn K.lineWeightFn (K.proj Q Q (gradMode m n G a 0))
              - K.normSqOn K.lineWeightFn (K.proj (Q - 2) Q (gradMode m n G a 0)))
            + K.tailNormSq Q (gradMode m n G a 0)

def HeightTailPartStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (Q : ℕ), 5 ≤ Q →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ (n : ℤ) (a : Fin 3),
        K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
            (CellBox.heightDeriv (fun p => K.projR (Q - 1) (fun p => modeVec m n v p.1 p.2 a) p
              - K.proj (Q - 1) (Q - 1) (fun p => modeVec m n v p.1 p.2 a) p))
          ≤ (K.normSqOn K.lineWeightFn (K.proj (Q - 1) Q (gradMode m n G a 2))
              - K.normSqOn K.lineWeightFn (K.proj (Q - 1) (Q - 2) (gradMode m n G a 2)))
            + K.tailNormSq Q (gradMode m n G a 2)

end CellAnalysis

end CellCert

end Breakdown
