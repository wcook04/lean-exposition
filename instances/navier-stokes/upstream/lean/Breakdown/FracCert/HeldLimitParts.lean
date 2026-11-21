import Breakdown.FracCert.StHeldParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FracCertData

variable {k N : ℕ} (d : FracCertData k N)

def heldResidual (α : ℝ) (p : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space) (κ : Fin k → ℝ) (y : Space) : Space :=
  d.fullField α p v G H P κ y + G y (v y) + d.defect α p y

end FracCertData

def HeldResidualSquareStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ v G H P, d.IsLinearState α p v G H P → ∀ κ : Fin k → ℝ,
      MemLp (d.heldResidual α p v G H P κ) 2 volume ∧ IsClassField d.order (d.heldResidual α p v G H P κ)

def HeldWeakLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ)
        (R : ℝ), (∀ n, d.IsHeldSolution α (p n) (u n) (G n) (H n) (P n) (κ n)) →
        (∀ n, d.size (G n) (H n) (κ n) ≤ R) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ G₀ H₀ P₀, ∃ κ₀ : Fin k → ℝ,
          d.IsLinearState α q u₀ G₀ H₀ P₀ ∧ d.size G₀ H₀ κ₀ ≤ R ∧
          Filter.Tendsto (fun n => κ (φ n)) Filter.atTop (nhds κ₀) ∧
          Filter.Tendsto (fun n => d.pins (G (φ n))) Filter.atTop (nhds (d.pins G₀)) ∧
          ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
            Filter.Tendsto (fun n => ∫ y, inner ℝ
              (d.heldResidual α (p (φ n)) (u (φ n)) (G (φ n)) (H (φ n)) (P (φ n)) (κ (φ n)) y) (ζ y))
              Filter.atTop (nhds (∫ y, inner ℝ (d.heldResidual α q u₀ G₀ H₀ P₀ κ₀ y) (ζ y)))

def WeakPowerClassStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (m : ℕ) (v P : Space → Space), AEStronglyMeasurable v volume →
    MemLp v 6 volume → IsClassField m v → IsWeakFractionalPower α v P → IsClassField m P

def GradientClassStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable v volume →
    MemLp v 6 volume → AEStronglyMeasurable G volume → Integrable (fun y => entrySq (G y)) →
    IsWeakGradientOf v G → IsClassField m v →
    (∀ᵐ y ∂volume, ∀ w, G (turnStep m y) (turnStep m w) = turnStep m (G y w)) ∧
      ∀ᵐ y ∂volume, ∀ w, G (mirror y) (mirror w) = mirror (G y w)

def HeldResidualClassStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ v G H P, d.IsLinearState α p v G H P → ∀ κ : Fin k → ℝ,
      IsClassField d.order (d.heldResidual α p v G H P κ)

def HeldStateLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Filter.Tendsto p Filter.atTop (nhds q) →
      ∀ (u : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
        (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space) (κ : ℕ → Fin k → ℝ)
        (R : ℝ), (∀ n, d.IsHeldSolution α (p n) (u n) (G n) (H n) (P n) (κ n)) →
        (∀ n, d.size (G n) (H n) (κ n) ≤ R) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ G₀ H₀ P₀, d.IsLinearState α q u₀ G₀ H₀ P₀ ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, d.energy G₀ H₀ ≤ d.energy (G (φ n)) (H (φ n)) + ε) ∧
          (∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
            Integrable (fun y => entrySq (E y)) →
            Filter.Tendsto (fun n => ∫ y, entryInner (G (φ n) y) (E y)) Filter.atTop
              (nhds (∫ y, entryInner (G₀ y) (E y)))) ∧
          ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
            Filter.Tendsto (fun n => ∫ y, inner ℝ
              (d.heldResidual α (p (φ n)) (u (φ n)) (G (φ n)) (H (φ n)) (P (φ n)) 0 y) (ζ y))
              Filter.atTop (nhds (∫ y, inner ℝ (d.heldResidual α q u₀ G₀ H₀ P₀ 0 y) (ζ y)))


end SteadyCert

end Breakdown
