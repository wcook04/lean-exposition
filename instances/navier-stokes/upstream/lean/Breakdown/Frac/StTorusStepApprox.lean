import Breakdown.Frac.StTorusInverse
import Breakdown.Frac.StTorusApprox
import Breakdown.Torus.StatementsApproxSteps

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def fracApproxPiece (α a : ℝ) (U : Space → Space) (T lam : ℝ) (n : ℕ) : Piece V (1 - lam) :=
  toPiece (1 - lam) fun s =>
    (stepScale T lam n) ^ dilExponent α •
      toV (latticePeriodize (fracApproxField α a U T (stepStart T lam n + stepScale T lam n * s)))

def FracApproxLinks (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ) (T lam : ℝ), IsRotatingProfile α a 1 U P →
    0 < T → T ≤ 1 → 0 < lam → lam < 1 → ∀ n : ℕ,
      (∀ s : Icc (0 : ℝ) (1 - lam), fracApproxPiece α a U T lam n s = (stepScale T lam n) ^ dilExponent α •
        toV (latticePeriodize (fracApproxField α a U T (stepStart T lam n + stepScale T lam n * s)))) ∧
      extendPiece (fracApproxPiece α a U T lam (n + 1)) 0 =
        lam ^ dilExponent α • pieceEnd (1 - lam) (fracApproxPiece α a U T lam n)

def FracApproxResidualSmall (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ) (lam θ : ℝ) (hl : 0 < lam) (hl1 : lam < 1),
    IsRotatingProfile α a 1 U P → lam ^ (1 / (4 * α)) < θ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ),
      ‖fracApproxPiece α a U T lam n -
        (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
          (stepScale_le_one hT1 hl hl1.le n)).pieceFree (1 - lam)
            (extendPiece (fracApproxPiece α a U T lam n) 0) -
        (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
          (stepScale_le_one hT1 hl hl1.le n)).pieceBil (1 - lam)
            (fracApproxPiece α a U T lam n) (fracApproxPiece α a U T lam n)‖ ≤
        θ ^ n * (K * T ^ (1 / (4 * α)))

def FracApproxClose (α : ℝ) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.D = Freq.fracDilX α →
    ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ) (P' : ℝ) (k : ℕ) (b ε δ : ℝ)
    (A : Approximant (MildFramework.stepLength P' k) b),
    IsRotatingProfile α a 1 U P → 0 < P' → 0 < k → 0 < b → 0 < δ →
    (∀ n, ‖A.r3Piece n - F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k n‖ ≤ ε) →
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T < T₀ → ∀ n,
      ‖fracApproxPiece α a U T (Real.exp (-(P' / k))) n -
        A.torusPiece (simScale α (stepScale T (Real.exp (-(P' / k))) n)) n‖ ≤ ε + δ

def FracApproxSizes (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ) (lam c : ℝ), IsRotatingProfile α a 1 U P →
    0 < lam → lam < 1 → 0 < c → (∀ s, c ≤ ‖Freq.embedX (rotatingSlice a U s)‖) →
    ∃ (T₀ M : ℝ), 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T < T₀ → ∀ n,
      ‖fracApproxPiece α a U T lam n‖ ≤ M ∧ ∀ s : Icc (0 : ℝ) (1 - lam), c / 2 ≤ ‖fracApproxPiece α a U T lam n s‖

def FracDatumClose (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ) (lam b δ : ℝ) (ψ₀ : Space → Space),
    IsRotatingProfile α a 1 U P → 0 < lam → lam < 1 → IsTestField ψ₀ → tsupport ψ₀ ⊆ Metric.closedBall 0 b →
    0 < b → 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, 0 < T → T < T₀ →
      ‖(simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) ψ₀) -
          extendPiece (fracApproxPiece α a U T lam 0) 0‖ ≤
        ‖Freq.embedX ψ₀ - Freq.embedX (rotatingSlice a U 0)‖ + δ

def FracApproximantExists (α : ℝ) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)) (R : Space ≃ₗᵢ[ℝ] Space) (a : ℝ) (U : Space → Space)
    (P : Space → ℝ) (P' : ℝ), F.Commutes (Freq.rotX R) →
    F.IsOrbit (Freq.rotX R) (fun s => Freq.embedX (rotatingSlice a U s)) P' →
    IsRotatingProfile α a 1 U P → ∀ k : ℕ, 0 < k → ∀ ε : ℝ, 0 < ε →
      ∃ b : ℝ, 0 < b ∧ ∃ A : Approximant (MildFramework.stepLength P' k) b,
        ∀ n, ‖A.r3Piece n - F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P' k n‖ ≤ ε

end Breakdown.Periodic
