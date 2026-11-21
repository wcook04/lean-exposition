import Breakdown.FracCert.StHeld
import Breakdown.FreqTr.Basic

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

def GradientOrthogonalStatement : Prop :=
  ∀ Q ζ : Space → Space, IsGradientField Q → MemLp Q 2 volume → IsSolenoidalL2 ζ → ∫ y, inner ℝ (Q y) (ζ y) = 0

def SecondTraceSolenoidalStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → IsSolenoidalL2 (negSecondTrace H) ∧ IsClassField m (negSecondTrace H)

def SolenoidalSplitStatement : Prop :=
  ∀ (m : ℕ) (F : Space → Space), MemLp F 2 volume → IsClassField m F →
    ∃ F₀ Q : Space → Space, IsSolenoidalL2 F₀ ∧ IsClassField m F₀ ∧ IsGradientField Q ∧ MemLp Q 2 volume ∧
      ∀ᵐ y ∂volume, F y = F₀ y + Q y

def SplitFormBoundsStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ v G H P, IsSecondOrderField d.order v G H → IsWeakFractionalPower α v P →
      -d.lowLoss * ((∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y)) ≤
        l2Pair (d.splitField P H) (negSecondTrace H) ∧
      0 ≤ l2Pair (d.splitField P H) (negSecondTrace H) +
        d.reducedCoercivity * ((∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y)) ∧
      Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) ≤ d.formScale * d.splitEnergy P G H

def LinearStateClosedStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ (v : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
      (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P F : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ)
      (F₀ : Space → Space), (∀ n, d.IsLinearState α p (v n) (G n) (H n) (P n)) →
      (∀ n, ∃ Q : Space → Space, IsGradientField Q ∧
        ∀ᵐ y ∂volume, d.fullField α p (v n) (G n) (H n) (P n) (κ n) y = F n y + Q y) →
      (∀ n, MemLp (F n) 2 volume) → MemLp F₀ 2 volume →
      Filter.Tendsto (fun n => ∫ y, ‖F n y - F₀ y‖ ^ 2) Filter.atTop (nhds 0) →
      (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n ≥ M, ∀ n' ≥ M,
        d.size (fun y => G n y - G n' y) (fun y => H n y - H n' y) (fun i => κ n i - κ n' i) < ε) →
      ∃ v₀ G₀ H₀ P₀, ∃ κ₀ : Fin k → ℝ, d.IsLinearState α p v₀ G₀ H₀ P₀ ∧
        (∃ Q : Space → Space, IsGradientField Q ∧
          ∀ᵐ y ∂volume, d.fullField α p v₀ G₀ H₀ P₀ κ₀ y = F₀ y + Q y) ∧
        Filter.Tendsto (fun n => d.size (fun y => G n y - G₀ y) (fun y => H n y - H₀ y)
          (fun i => κ n i - κ₀ i)) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun n => ∫ y, ‖v n y - v₀ y‖ ^ 6) Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun n => d.pins (G n)) Filter.atTop (nhds (d.pins G₀))

def HeldLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ),
        (∀ n, d.IsHeldSolution α (p n) (u n) (G n) (H n) (P n) (κ n)) →
        (∀ n, d.size (G n) (H n) (κ n) ≤ d.heldRadius) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ G₀ H₀ P₀, ∃ κ₀ : Fin k → ℝ,
          d.IsHeldSolution α q u₀ G₀ H₀ P₀ κ₀ ∧ d.size G₀ H₀ κ₀ ≤ d.heldRadius ∧
          Filter.Tendsto (fun n => κ (φ n)) Filter.atTop (nhds κ₀)

def EmbedWeakStatement : Prop :=
  ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable v volume →
    MemLp v 6 volume → AEStronglyMeasurable G volume → Integrable (fun y => entrySq (G y)) →
    IsWeakGradientOf v G → (∀ᵐ y ∂volume, ∑ i : Fin 3, inner ℝ (G y (unitVector i)) (unitVector i) = 0) →
    ∃ U : Freq.X, ((Freq.velocity U : Space → Space) =ᵐ[volume] v) ∧
      ∀ j : Fin 3, ((Freq.partialX j U : Space → Space) =ᵐ[volume] fun y => G y (unitVector j))

end SteadyCert

end Breakdown
