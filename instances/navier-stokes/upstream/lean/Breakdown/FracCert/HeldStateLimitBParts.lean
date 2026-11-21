import Breakdown.FracCert.HeldLimitParts
import Breakdown.FracCert.StFree

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

def HeldUniformBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d → ∀ R : ℝ, ∃ B : ℝ,
    ∀ p ∈ box d.radius, ∀ u G H P κ, d.IsHeldSolution α p u G H P κ → d.size G H κ ≤ R →
      l2Norm P ≤ B ∧ l2Norm (driftField α (d.rotationRate p) u G) ≤ B

def HeldBoundedLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ)
        (R B : ℝ) (κ₀ : Fin k → ℝ), (∀ n, d.IsHeldSolution α (p n) (u n) (G n) (H n) (P n) (κ n)) →
        (∀ n, d.size (G n) (H n) (κ n) ≤ R) →
        (∀ n, l2Norm (P n) ≤ B ∧ l2Norm (driftField α (d.rotationRate (p n)) (u n) (G n)) ≤ B) →
        Filter.Tendsto κ Filter.atTop (nhds κ₀) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ G₀ H₀ P₀, d.IsLinearState α q u₀ G₀ H₀ P₀ ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, d.energy G₀ H₀ ≤ d.energy (G (φ n)) (H (φ n)) + ε) ∧
          (∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
            Integrable (fun y => entrySq (E y)) →
            Filter.Tendsto (fun n => ∫ y, entryInner (G (φ n) y) (E y)) Filter.atTop
              (nhds (∫ y, entryInner (G₀ y) (E y)))) ∧
          ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
            ∫ y, inner ℝ (d.heldResidual α q u₀ G₀ H₀ P₀ κ₀ y) (ζ y) = 0

def HeldLimitIdentifyStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ)
        (R B : ℝ) (κ₀ : Fin k → ℝ), (∀ n, d.IsHeldSolution α (p n) (u n) (G n) (H n) (P n) (κ n)) →
        (∀ n, d.size (G n) (H n) (κ n) ≤ R) →
        (∀ n, l2Norm (P n) ≤ B ∧ l2Norm (driftField α (d.rotationRate (p n)) (u n) (G n)) ≤ B) →
        Filter.Tendsto κ Filter.atTop (nhds κ₀) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ G₀ H₀ P₀, d.IsLinearState α q u₀ G₀ H₀ P₀ ∧
          (∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
            Filter.Tendsto (fun n => ∫ y, inner ℝ (G (φ n) y (unitVector i)) (g y)) Filter.atTop
              (nhds (∫ y, inner ℝ (G₀ y (unitVector i)) (g y)))) ∧
          (∀ g : Space → Space, MemLp g 2 volume →
            Filter.Tendsto (fun n => ∫ y, inner ℝ (secondTrace (H (φ n) y)) (g y)) Filter.atTop
              (nhds (∫ y, inner ℝ (secondTrace (H₀ y)) (g y)))) ∧
          ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
            ∫ y, inner ℝ (d.heldResidual α q u₀ G₀ H₀ P₀ κ₀ y) (ζ y) = 0

def HeldLimitClosureStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ)
        (R B : ℝ) (κ₀ : Fin k → ℝ), (∀ n, d.IsHeldSolution α (p n) (u n) (G n) (H n) (P n) (κ n)) →
        (∀ n, d.size (G n) (H n) (κ n) ≤ R) →
        (∀ n, l2Norm (P n) ≤ B ∧ l2Norm (driftField α (d.rotationRate (p n)) (u n) (G n)) ≤ B) →
        Filter.Tendsto κ Filter.atTop (nhds κ₀) →
      ∀ (w₀ : Space → Space) (G₀ : Space → (Space →L[ℝ] Space))
        (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P₀ D₀ : Space → Space),
        AEStronglyMeasurable G₀ volume → AEStronglyMeasurable H₀ volume →
        (∀ i : Fin 3, MemLp (fun y => G₀ y (unitVector i)) 2 volume) →
        (∀ i j : Fin 3, MemLp (fun y => H₀ y (unitVector i) (unitVector j)) 2 volume) →
        MemLp w₀ 2 volume → MemLp P₀ 2 volume → MemLp D₀ 2 volume →
        (∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (G n y (unitVector i)) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (G₀ y (unitVector i)) (g y)))) →
        (∀ i j : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (H n y (unitVector i) (unitVector j)) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (H₀ y (unitVector i) (unitVector j)) (g y)))) →
        (∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (w₀ y) (g y)))) →
        (∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (P n y) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (P₀ y) (g y)))) →
        (∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (driftField α (d.rotationRate (p n)) (u n) (G n) y) (g y))
            Filter.atTop (nhds (∫ y, inner ℝ (D₀ y) (g y)))) →
        d.IsLinearState α q (fun y => ‖y‖ • w₀ y) G₀ H₀ P₀ ∧
          ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
            ∫ y, inner ℝ (d.heldResidual α q (fun y => ‖y‖ • w₀ y) G₀ H₀ P₀ κ₀ y) (ζ y) = 0

def SecondOrderWeakLimitStatement : Prop :=
  ∀ (m : ℕ) (K : ℝ) (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
    (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (w₀ : Space → Space) (G₀ : Space → (Space →L[ℝ] Space))
    (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    (∀ n, IsSecondOrderField m (u n) (G n) (H n)) → (∀ n, ∫ y, entrySq (G n y) ≤ K) →
    (∀ n, ∫ y, fullSecondSq (H n y) ≤ K) → AEStronglyMeasurable G₀ volume → AEStronglyMeasurable H₀ volume →
    MemLp w₀ 2 volume → (∀ i : Fin 3, MemLp (fun y => G₀ y (unitVector i)) 2 volume) →
    (∀ i j : Fin 3, MemLp (fun y => H₀ y (unitVector i) (unitVector j)) 2 volume) →
    (∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (G n y (unitVector i)) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (G₀ y (unitVector i)) (g y)))) →
    (∀ i j : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (H n y (unitVector i) (unitVector j)) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (H₀ y (unitVector i) (unitVector j)) (g y)))) →
    (∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (w₀ y) (g y)))) →
    IsSecondOrderField m (fun y => ‖y‖ • w₀ y) G₀ H₀

def WeakPowerLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (u P : ℕ → Space → Space) (w₀ P₀ : Space → Space),
    (∀ n, IsWeakFractionalPower α (u n) (P n)) → (∀ n, MemLp (fun y => ‖y‖⁻¹ • u n y) 2 volume) →
    MemLp w₀ 2 volume → MemLp P₀ 2 volume →
    (∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (w₀ y) (g y)))) →
    (∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (P n y) (g y)) Filter.atTop (nhds (∫ y, inner ℝ (P₀ y) (g y)))) →
    IsWeakFractionalPower α (fun y => ‖y‖ • w₀ y) P₀

def DriftWeakLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (m : ℕ) (a : ℕ → ℝ) (a₀ : ℝ) (u : ℕ → Space → Space)
    (G : ℕ → Space → (Space →L[ℝ] Space)) (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ : Space → Space) (G₀ : Space → (Space →L[ℝ] Space)) (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (D₀ : Space → Space), Filter.Tendsto a Filter.atTop (nhds a₀) →
    (∀ n, IsSecondOrderField m (u n) (G n) (H n)) → IsSecondOrderField m (fun y => ‖y‖ • w₀ y) G₀ H₀ →
    (∀ n, MemLp (driftField α (a n) (u n) (G n)) 2 volume) → (∀ n, MemLp (fun y => ‖y‖⁻¹ • u n y) 2 volume) →
    MemLp D₀ 2 volume →
    (∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (G n y (unitVector i)) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (G₀ y (unitVector i)) (g y)))) →
    (∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (w₀ y) (g y)))) →
    (∀ g : Space → Space, MemLp g 2 volume →
      Filter.Tendsto (fun n => ∫ y, inner ℝ (driftField α (a n) (u n) (G n) y) (g y)) Filter.atTop
        (nhds (∫ y, inner ℝ (D₀ y) (g y)))) →
    MemLp (driftField α a₀ (fun y => ‖y‖ • w₀ y) G₀) 2 volume

def HeldResidualLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ)
        (R B : ℝ) (κ₀ : Fin k → ℝ), (∀ n, d.IsHeldSolution α (p n) (u n) (G n) (H n) (P n) (κ n)) →
        (∀ n, d.size (G n) (H n) (κ n) ≤ R) →
        (∀ n, l2Norm (P n) ≤ B ∧ l2Norm (driftField α (d.rotationRate (p n)) (u n) (G n)) ≤ B) →
        Filter.Tendsto κ Filter.atTop (nhds κ₀) →
      ∀ (w₀ : Space → Space) (G₀ : Space → (Space →L[ℝ] Space))
        (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P₀ D₀ : Space → Space),
        d.IsLinearState α q (fun y => ‖y‖ • w₀ y) G₀ H₀ P₀ → MemLp D₀ 2 volume →
        (∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (G n y (unitVector i)) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (G₀ y (unitVector i)) (g y)))) →
        (∀ i j : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (H n y (unitVector i) (unitVector j)) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (H₀ y (unitVector i) (unitVector j)) (g y)))) →
        (∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (w₀ y) (g y)))) →
        (∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (P n y) (g y)) Filter.atTop
            (nhds (∫ y, inner ℝ (P₀ y) (g y)))) →
        (∀ g : Space → Space, MemLp g 2 volume →
          Filter.Tendsto (fun n => ∫ y, inner ℝ (driftField α (d.rotationRate (p n)) (u n) (G n) y) (g y))
            Filter.atTop (nhds (∫ y, inner ℝ (D₀ y) (g y)))) →
        ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
          ∫ y, inner ℝ (d.heldResidual α q (fun y => ‖y‖ • w₀ y) G₀ H₀ P₀ κ₀ y) (ζ y) = 0

end SteadyCert

end Breakdown
