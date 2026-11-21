import Breakdown.CertCell.MeanStretchModeSum

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

def pairSesq (M : Matrix (Fin 12) (Fin 12) ℂ) (U U' : Fin 12 → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (U i) * M i j * U' j

def torusMean (f : ℝ → ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), f τ φ

def IsTorusIntegrable (f : ℝ → ℝ → ℂ) : Prop :=
  Integrable (fun z : ℝ × ℝ => f z.1 z.2) boxMeasure

def waveSum (m : ℕ) (S : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) : Fin 12 → ℂ :=
  fun j => ∑ ι ∈ S, labelPhase m ι τ φ * X ι j

def torusCoef (m : ℕ) (M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ) (α : ℤ × ℤ) : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * M τ φ i j)

def TorusMeanAddStatement : Prop :=
  ∀ f g : ℝ → ℝ → ℂ, IsTorusIntegrable f → IsTorusIntegrable g →
    torusMean (fun τ φ => f τ φ + g τ φ) = torusMean f + torusMean g

def TorusMeanSumStatement : Prop :=
  ∀ (S : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℝ → ℝ → ℂ), (∀ s ∈ S, IsTorusIntegrable (f s)) →
    torusMean (fun τ φ => ∑ s ∈ S, f s τ φ) = ∑ s ∈ S, torusMean (f s)

def TorusMeanReMonoStatement : Prop :=
  ∀ f g : ℝ → ℝ → ℂ, IsTorusIntegrable f → IsTorusIntegrable g →
    (∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi → (f τ φ).re ≤ (g τ φ).re) →
    (torusMean f).re ≤ (torusMean g).re

def TorusBoundedIntegrableStatement : Prop :=
  ∀ f : ℝ → ℝ → ℂ, AEStronglyMeasurable (fun z : ℝ × ℝ => f z.1 z.2) boxMeasure →
    (∃ C : ℝ, ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi → ‖f τ φ‖ ≤ C) → IsTorusIntegrable f

def TorusHarmonicMeanStatement : Prop :=
  ∀ β : ℤ × ℤ, torusMean (fun τ φ => phase β τ φ) = if β = 0 then 1 else 0

def TorusLabelMeanStatement : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ α : ℤ × ℤ, torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ)) = if α = 0 then 1 else 0

def TorusProductStatement : Prop :=
  ∀ (m : ℕ) (M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ) (S T : Finset (ℤ × ℤ)) (X Y : ℤ × ℤ → Fin 12 → ℂ),
    (∀ i j, IsTorusIntegrable (fun τ φ => M τ φ i j)) →
    torusMean (fun τ φ => pairSesq (M τ φ) (waveSum m S X τ φ) (waveSum m T Y τ φ))
      = ∑ ι ∈ S, ∑ ι' ∈ T, pairSesq (torusCoef m M (ι - ι')) (X ι) (Y ι')

structure TorusFacts : Prop where
  add : TorusMeanAddStatement
  sum : TorusMeanSumStatement
  re_mono : TorusMeanReMonoStatement
  bounded : TorusBoundedIntegrableStatement
  harmonic_mean : TorusHarmonicMeanStatement
  label_mean : TorusLabelMeanStatement
  product : TorusProductStatement

end Internal

end Assembly

end CertCell

end Breakdown
