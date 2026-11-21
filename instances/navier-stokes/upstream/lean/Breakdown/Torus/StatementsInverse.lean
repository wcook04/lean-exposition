import Breakdown.Torus.InverseDefs

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def BaseInverse : Prop :=
  ∀ (F : MildFramework Freq.X) (ρ : Freq.X ≃ₗᵢ[ℝ] Freq.X), F.Commutes ρ →
    ∀ (w : ℝ → Freq.X) (P : ℝ), F.IsOrbit ρ w P →
    ∀ C' : Submodule ℝ Freq.X, Dense (C' : Set Freq.X) → ∀ t₀ : ℝ, 0 < t₀ →
    ∃ (k : ℕ) (θ : ℝ) (Vs : Submodule ℝ Freq.X) (J : Freq.X →L[ℝ] Freq.X)
      (R : R3Seq (MildFramework.stepLength P k) →L[ℝ] Vs × R3Seq (MildFramework.stepLength P k)),
      0 < k ∧ MildFramework.stepLength P k ≤ t₀ ∧ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ ∧ θ < 1 ∧
      FiniteDimensional ℝ Vs ∧ (∀ x, J x ∈ C') ∧
      (r3Op F P k θ (J.comp Vs.subtypeL) (F.profilePiece w P k)).comp R = ContinuousLinearMap.id ℝ _

def R3ChainEq : Prop :=
  ∀ (F : MildFramework Freq.X), F.K = Freq.bilinX → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (J : E →L[ℝ] Freq.X)
    (A : Approximant (MildFramework.stepLength P k) b),
    0 < MildFramework.stepLength P k → MildFramework.stepLength P k ≤ 1 →
      chainOp (r3Shift F P k θ) (r3Seed F P k J) (r3Lambda A) (r3Restrict _ b) = r3Op F P k θ J A.r3Piece

def TorusChainEq : Prop :=
  ∀ (hK : KernelSharpBound) (T lam θ b : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Jt : E →L[ℝ] V) (A : Approximant (1 - lam) b),
    lam < 1 → 0 < b → Real.sqrt T * b ≤ 1 / 8 →
      chainOp (torusShift hK T lam θ hT hT1 hl hl1) (torusSeed hK T lam hT hT1 hl hl1 Jt)
        (torusLambda A T lam) (torusRestrict _ b T lam) =
      torusOp hK T lam θ hT hT1 hl hl1 Jt (fun n => A.torusPiece (stepScale T lam n) n)

def OpDiffBounds : Prop :=
  (∀ (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) (θ M : ℝ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : E →L[ℝ] Freq.X) (f g : ℕ → Piece Freq.X (MildFramework.stepLength P k)),
    0 < MildFramework.stepLength P k → MildFramework.stepLength P k ≤ 1 → (∀ n, ‖f n - g n‖ ≤ M) →
      ‖r3Op F P k θ J f - r3Op F P k θ J g‖ ≤
        8 * F.CK * (MildFramework.stepLength P k) ^ (1 / 4 : ℝ) * M) ∧
  (∀ (hK : KernelSharpBound) (T lam θ M : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Jt : E →L[ℝ] V) (f g : ℕ → Piece V (1 - lam)),
    lam < 1 → (∀ n, ‖f n - g n‖ ≤ M) →
      ‖torusOp hK T lam θ hT hT1 hl hl1 Jt f - torusOp hK T lam θ hT hT1 hl hl1 Jt g‖ ≤
        8 * hK.choose * (1 - lam) ^ (1 / 4 : ℝ) * M)

def OperatorNormBounds : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ (L b M : ℝ) (A : Approximant L b), 0 < L → L ≤ 1 → (∀ n, ‖A.r3Piece n‖ ≤ M) →
      ‖r3Lambda A‖ ≤ C * M) ∧
    (∀ (b T lam M : ℝ) (A : Approximant (1 - lam) b), 0 < T → T ≤ 1 → 0 < lam → lam < 1 → 0 < b →
      Real.sqrt T * b ≤ 1 / 8 → (∀ n, ‖A.r3Piece n‖ ≤ M) → ‖torusLambda A T lam‖ ≤ C * M) ∧
    (∀ L b : ℝ, 0 < L → ‖r3Restrict L b‖ ≤ C) ∧
    (∀ b T lam : ℝ, 0 < T → T ≤ 1 → 0 < lam → lam < 1 → 0 < b → Real.sqrt T * b ≤ 1 / 8 →
      ‖torusRestrict (1 - lam) b T lam‖ ≤ C) ∧
    (∀ (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) (θ : ℝ), 0 < P → 0 < k → 0 < θ →
      ‖r3Shift F P k θ‖ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ) ∧
    (∀ (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1),
      0 < θ → ‖torusShift hK T lam θ hT hT1 hl hl1‖ ≤ lam ^ (1 / 4 : ℝ) / θ)

structure TestLift (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (J : E →L[ℝ] Freq.X) (b : ℝ) where
  field : E →ₗ[ℝ] (Space → Space)
  isTest : ∀ e, IsTestField (field e)
  support : ∀ e, tsupport (field e) ⊆ Metric.closedBall 0 b
  embed : ∀ e, Freq.embedX (field e) = J e

def TestLiftExists : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E →L[ℝ] Freq.X),
    (∀ e, J e ∈ Freq.testSpan) → ∃ b : ℝ, 0 < b ∧ Nonempty (TestLift E J b)

def TorusLiftExists : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E →L[ℝ] Freq.X)
    (b : ℝ) (ψ : TestLift E J b) (T : ℝ), 0 < b → 0 < T → T ≤ 1 → Real.sqrt T * b ≤ 1 / 8 →
    ∃ Jt : E →L[ℝ] V, ∀ e, Jt e = (T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e))

def ComparisonSmall : Prop :=
  ∀ (hK : KernelSharpBound) (F : MildFramework Freq.X), F.K = Freq.bilinX → F.G = Freq.heatX →
    F.D = Freq.dilX → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] Freq.X) (ψ : TestLift E J b)
    (A : Approximant (MildFramework.stepLength P k) b) (hl : 0 < Real.exp (-(P / k)))
    (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ (1 / 4 : ℝ) < θ →
    θ < 1 → 0 < b → ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ∀ Jt : E →L[ℝ] V, (∀ e, Jt e = (T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e))) →
      ‖(torusRestrict _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - torusShift hK T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (torusLambda A T (Real.exp (-(P / k))))) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - r3Shift F P k θ)).comp (r3Lambda A))‖ ≤ δ ∧
      ‖(torusRestrict _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - torusShift hK T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (torusSeed hK T (Real.exp (-(P / k))) hT hT1 hl hl1 Jt)) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - r3Shift F P k θ)).comp (r3Seed F P k J))‖ ≤ δ

end Breakdown.Periodic
