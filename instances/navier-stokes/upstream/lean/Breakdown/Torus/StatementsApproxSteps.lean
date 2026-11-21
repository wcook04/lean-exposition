import Breakdown.Torus.StatementsInverse
import Breakdown.Torus.StatementsApprox

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def approxPeriodic (W : ℝ → Space → Space) (T t : ℝ) (x : Space) : Space := approxField W T t (wrap x)

def approxPiece (W : ℝ → Space → Space) (T lam : ℝ) (n : ℕ) : Piece V (1 - lam) :=
  toPiece (1 - lam) fun s =>
    (stepScale T lam n) ^ (1 / 4 : ℝ) • toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * s))

def ApproxLinks : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C T lam : ℝ), IsSimilarityProfile W q C →
    0 < T → T ≤ 1 → 0 < lam → lam < 1 → ∀ n : ℕ,
      (∀ s : Icc (0 : ℝ) (1 - lam), approxPiece W T lam n s = (stepScale T lam n) ^ (1 / 4 : ℝ) •
        toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * s))) ∧
      extendPiece (approxPiece W T lam (n + 1)) 0 = lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (approxPiece W T lam n)

def ApproxResidualSmall : Prop :=
  ∀ (hK : KernelSharpBound) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C lam θ : ℝ)
    (hl : 0 < lam) (hl1 : lam < 1), IsSimilarityProfile W q C → lam ^ (1 / 4 : ℝ) < θ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ),
      ‖approxPiece W T lam n -
        (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
          (stepScale_le_one hT1 hl hl1.le n)).pieceFree (1 - lam)
            (extendPiece (approxPiece W T lam n) 0) -
        (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
          (stepScale_le_one hT1 hl hl1.le n)).pieceBil (1 - lam)
            (approxPiece W T lam n) (approxPiece W T lam n)‖ ≤ θ ^ n * (K * T ^ (1 / 4 : ℝ))

def ApproxClose : Prop :=
  ∀ (F : MildFramework Freq.X), F.D = Freq.dilX → ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (C P : ℝ) (k : ℕ) (b ε δ : ℝ) (A : Approximant (MildFramework.stepLength P k) b),
    IsSimilarityProfile W q C → 0 < P → 0 < k → 0 < b → 0 < δ →
    (∀ n, ‖A.r3Piece n - F.profilePiece (fun s => Freq.embedX (W s)) P k n‖ ≤ ε) →
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T < T₀ → ∀ n,
      ‖approxPiece W T (Real.exp (-(P / k))) n - A.torusPiece (stepScale T (Real.exp (-(P / k))) n) n‖ ≤ ε + δ

def ApproxSizes : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C lam c : ℝ), IsSimilarityProfile W q C →
    0 < lam → lam < 1 → 0 < c → (∀ s, c ≤ ‖Freq.embedX (W s)‖) →
    ∃ (T₀ M : ℝ), 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T < T₀ → ∀ n,
      ‖approxPiece W T lam n‖ ≤ M ∧ ∀ s : Icc (0 : ℝ) (1 - lam), c / 2 ≤ ‖approxPiece W T lam n s‖

def DatumClose : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C lam b δ : ℝ) (ψ₀ : Space → Space),
    IsSimilarityProfile W q C → 0 < lam → lam < 1 → IsTestField ψ₀ → tsupport ψ₀ ⊆ Metric.closedBall 0 b →
    0 < b → 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T < T₀ →
      ‖(T ^ (1 / 4 : ℝ)) • toV (transplantField T ψ₀) - extendPiece (approxPiece W T lam 0) 0‖ ≤
        ‖Freq.embedX ψ₀ - Freq.embedX (W 0)‖ + δ

def ToVAdd : Prop :=
  ∀ f g : Space → Space, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → IsPeriodic f → IsPeriodic g →
    (∀ x, divergenceAt f x = 0) → (∀ x, divergenceAt g x = 0) → toV (f + g) = toV f + toV g

def ApproximantExists : Prop :=
  ∀ (F : MildFramework Freq.X) (R : Space ≃ₗᵢ[ℝ] Space) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (C P : ℝ), F.Commutes (Freq.rotX R) → F.IsOrbit (Freq.rotX R) (fun s => Freq.embedX (W s)) P →
    IsSimilarityProfile W q C → ∀ k : ℕ, 0 < k → ∀ ε : ℝ, 0 < ε →
      ∃ b : ℝ, 0 < b ∧ ∃ A : Approximant (MildFramework.stepLength P k) b,
        ∀ n, ‖A.r3Piece n - F.profilePiece (fun s => Freq.embedX (W s)) P k n‖ ≤ ε

end Breakdown.Periodic
