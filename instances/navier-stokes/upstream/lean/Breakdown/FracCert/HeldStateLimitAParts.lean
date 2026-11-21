import Breakdown.FracCert.HeldLimitParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

def HeldFreeBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ R : ℝ, ∃ C : ℝ, ∀ p ∈ box d.radius, ∀ u G H P κ, d.IsHeldSolution α p u G H P κ →
      d.size G H κ ≤ R → ∫ y, ‖driftField α (d.rotationRate p) u G y + P y‖ ^ 2 ≤ C

def LinearStateWeakLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (B : ℝ),
        (∀ n, d.IsLinearState α (p n) (u n) (G n) (H n) (P n)) →
        (∀ n, d.energy (G n) (H n) ≤ B) →
        (∀ n, ∫ y, ‖driftField α (d.rotationRate (p n)) (u n) (G n) y‖ ^ 2 ≤ B) →
        (∀ n, ∫ y, ‖P n y‖ ^ 2 ≤ B) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ G₀ H₀ P₀, d.IsLinearState α q u₀ G₀ H₀ P₀ ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, d.energy G₀ H₀ ≤ d.energy (G (φ n)) (H (φ n)) + ε) ∧
          (∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
            Integrable (fun y => entrySq (E y)) →
            Filter.Tendsto (fun n => ∫ y, entryInner (G (φ n) y) (E y)) Filter.atTop
              (nhds (∫ y, entryInner (G₀ y) (E y)))) ∧
          (∀ r : ℝ, Filter.Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖u (φ n) y - u₀ y‖ ^ 2)
            Filter.atTop (nhds 0)) ∧
          ∀ ζ : Space → Space, MemLp ζ 2 volume →
            Filter.Tendsto (fun n => ∫ y, inner ℝ
              (driftField α (d.rotationRate (p (φ n))) (u (φ n)) (G (φ n)) y + P (φ n) y) (ζ y))
              Filter.atTop (nhds (∫ y, inner ℝ (driftField α (d.rotationRate q) u₀ G₀ y + P₀ y) (ζ y)))

def CrossPairingLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u₀ : Space → Space)
        (G₀ : Space → (Space →L[ℝ] Space)) (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (B : ℝ),
        (∀ n, IsSecondOrderField d.order (u n) (G n) (H n)) → IsSecondOrderField d.order u₀ G₀ H₀ →
        (∀ n, d.energy (G n) (H n) ≤ B) →
        (∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
          Integrable (fun y => entrySq (E y)) →
          Filter.Tendsto (fun n => ∫ y, entryInner (G n y) (E y)) Filter.atTop
            (nhds (∫ y, entryInner (G₀ y) (E y)))) →
        (∀ r : ℝ, Filter.Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖u n y - u₀ y‖ ^ 2)
          Filter.atTop (nhds 0)) →
        ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
          Filter.Tendsto (fun n => ∫ y, inner ℝ
            (d.gradProfile (p n) y (u n y) + G n y (d.profile (p n) y) + G n y (u n y)) (ζ y))
            Filter.atTop
            (nhds (∫ y, inner ℝ (d.gradProfile q y (u₀ y) + G₀ y (d.profile q y) + G₀ y (u₀ y)) (ζ y)))

def DefectPairingLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
        Filter.Tendsto (fun n => ∫ y, inner ℝ (d.defect α (p n) y) (ζ y)) Filter.atTop
          (nhds (∫ y, inner ℝ (d.defect α q y) (ζ y)))

end SteadyCert

end Breakdown
