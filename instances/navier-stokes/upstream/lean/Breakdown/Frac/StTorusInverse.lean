import Breakdown.Frac.StTorusShell
import Breakdown.Torus.InverseDefs
import Breakdown.Torus.StatementsInverse
import Breakdown.Frac.ScaledDefs

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def fracR3Lambda (α : ℝ) {L b : ℝ} (A : Approximant L b) : ShellSeq L →L[ℝ] R3Seq L :=
  seqOp fun n => ∑ l, pieceConv L (fun τ => fracLambdaR3 α (A.field n l) (A.isTest n l) b τ) (A.weight n l)

def fracTorusLambda (α : ℝ) {L b : ℝ} (A : Approximant L b) (T lam : ℝ) : ShellSeq L →L[ℝ] TorusSeq L :=
  seqOp fun n => ∑ l,
    pieceConv L (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ) (A.weight n l)

def fracTorusRestrict (α L b T lam : ℝ) : TorusSeq L →L[ℝ] ShellSeq L :=
  seqOp fun n => pieceComp L (restrictTorus (simScale α (stepScale T lam n)) b)

def fracR3Shift {κ : ℝ} (F : ScaledMildFramework Freq.X κ) (P : ℝ) (k : ℕ) (θ : ℝ) :
    R3Seq (MildFramework.stepLength P k) →L[ℝ] R3Seq (MildFramework.stepLength P k) :=
  seqShift fun _ => θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)

def fracTorusShift (α : ℝ) (hα : 1 < α) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) : TorusSeq (1 - lam) →L[ℝ] TorusSeq (1 - lam) :=
  seqShift fun n => (lam ^ dilExponent α / θ) •
    ((fracStepFrame α hα (stepScale T lam (n + 1)) (stepScale_pos hT hl (n + 1))
      (stepScale_le_one hT1 hl hl1 (n + 1))).pieceFree (1 - lam)).comp (pieceEnd (1 - lam))

def fracR3Seed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : ℝ} (F : ScaledMildFramework Freq.X κ)
    (P : ℝ) (k : ℕ) (J : E →L[ℝ] Freq.X) : E →L[ℝ] R3Seq (MildFramework.stepLength P k) :=
  seqSeed ((F.stepFree P k).comp J)

def fracTorusSeed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) (hα : 1 < α)
    (T lam : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (Jt : E →L[ℝ] V) :
    E →L[ℝ] TorusSeq (1 - lam) :=
  seqSeed (((fracStepFrame α hα (stepScale T lam 0) (stepScale_pos hT hl 0)
      (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam)).comp Jt)

def fracR3Op {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : ℝ} (F : ScaledMildFramework Freq.X κ)
    (P : ℝ) (k : ℕ) (θ : ℝ) (J : E →L[ℝ] Freq.X) (f : ℕ → Piece Freq.X (MildFramework.stepLength P k)) :
    E × R3Seq (MildFramework.stepLength P k) →L[ℝ] R3Seq (MildFramework.stepLength P k) :=
  ContinuousLinearMap.snd ℝ _ _ - (fracR3Shift F P k θ).comp (ContinuousLinearMap.snd ℝ _ _) -
    (fracR3Seed F P k J).comp (ContinuousLinearMap.fst ℝ _ _) -
    (seqOp fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (f n)).comp
      (ContinuousLinearMap.snd ℝ _ _)

def fracTorusOp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) (hα : 1 < α)
    (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (Jt : E →L[ℝ] V)
    (f : ℕ → Piece V (1 - lam)) : E × TorusSeq (1 - lam) →L[ℝ] TorusSeq (1 - lam) :=
  ContinuousLinearMap.snd ℝ _ _ - (fracTorusShift α hα T lam θ hT hT1 hl hl1).comp (ContinuousLinearMap.snd ℝ _ _) -
    (fracTorusSeed α hα T lam hT hT1 hl hl1 Jt).comp (ContinuousLinearMap.fst ℝ _ _) -
    (seqOp fun n => (2 : ℝ) • (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
      (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam) (f n)).comp (ContinuousLinearMap.snd ℝ _ _)

def FracBaseInverse (α : ℝ) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)) (ρ : Freq.X ≃ₗᵢ[ℝ] Freq.X), F.Commutes ρ →
    ∀ (w : ℝ → Freq.X) (P : ℝ), F.IsOrbit ρ w P →
    ∀ C' : Submodule ℝ Freq.X, Dense (C' : Set Freq.X) → ∀ t₀ : ℝ, 0 < t₀ →
    ∃ (k : ℕ) (θ : ℝ) (Vs : Submodule ℝ Freq.X) (J : Freq.X →L[ℝ] Freq.X)
      (R : R3Seq (MildFramework.stepLength P k) →L[ℝ] Vs × R3Seq (MildFramework.stepLength P k)),
      0 < k ∧ MildFramework.stepLength P k ≤ t₀ ∧ Real.exp (-(P / k)) ^ dilExponent α < θ ∧
      Real.exp (-(P / k)) ^ (1 / (4 * α)) < θ ∧ θ < 1 ∧
      FiniteDimensional ℝ Vs ∧ (∀ x, J x ∈ C') ∧
      (fracR3Op F P k θ (J.comp Vs.subtypeL) (F.profilePiece w P k)).comp R = ContinuousLinearMap.id ℝ _

def FracR3ChainEq (α : ℝ) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.K = Freq.fracBilinX α → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (J : E →L[ℝ] Freq.X)
    (A : Approximant (MildFramework.stepLength P k) b),
    0 < MildFramework.stepLength P k → MildFramework.stepLength P k ≤ 1 →
      chainOp (fracR3Shift F P k θ) (fracR3Seed F P k J) (fracR3Lambda α A) (r3Restrict _ b) =
        fracR3Op F P k θ J A.r3Piece

def FracTorusChainEq (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (T lam θ b : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Jt : E →L[ℝ] V) (A : Approximant (1 - lam) b),
    lam < 1 → 0 < b → Real.sqrt (simScale α T) * b ≤ 1 / 8 →
      chainOp (fracTorusShift α hα T lam θ hT hT1 hl hl1) (fracTorusSeed α hα T lam hT hT1 hl hl1 Jt)
        (fracTorusLambda α A T lam) (fracTorusRestrict α _ b T lam) =
      fracTorusOp α hα T lam θ hT hT1 hl hl1 Jt (fun n => A.torusPiece (simScale α (stepScale T lam n)) n)

def FracOpDiffBounds (α : ℝ) (hα : 1 < α) : Prop :=
  (∀ (F : ScaledMildFramework Freq.X (dilExponent α)) (P : ℝ) (k : ℕ) (θ M : ℝ) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (J : E →L[ℝ] Freq.X)
    (f g : ℕ → Piece Freq.X (MildFramework.stepLength P k)),
    0 < MildFramework.stepLength P k → MildFramework.stepLength P k ≤ 1 → (∀ n, ‖f n - g n‖ ≤ M) →
      ‖fracR3Op F P k θ J f - fracR3Op F P k θ J g‖ ≤
        8 * F.CK * (MildFramework.stepLength P k) ^ (1 / 4 : ℝ) * M) ∧
  (∀ (T lam θ M : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Jt : E →L[ℝ] V) (f g : ℕ → Piece V (1 - lam)),
    lam < 1 → (∀ n, ‖f n - g n‖ ≤ M) →
      ‖fracTorusOp α hα T lam θ hT hT1 hl hl1 Jt f - fracTorusOp α hα T lam θ hT hT1 hl hl1 Jt g‖ ≤
        8 * fracStepCK α hα * (1 - lam) ^ (1 / 4 : ℝ) * M)

def FracOperatorNormBounds (α : ℝ) (hα : 1 < α) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ (L b M : ℝ) (A : Approximant L b), 0 < L → L ≤ 1 → (∀ n, ‖A.r3Piece n‖ ≤ M) →
      ‖fracR3Lambda α A‖ ≤ C * M) ∧
    (∀ (b T lam M : ℝ) (A : Approximant (1 - lam) b), 0 < T → T ≤ 1 → 0 < lam → lam < 1 → 0 < b →
      Real.sqrt (simScale α T) * b ≤ 1 / 8 → (∀ n, ‖A.r3Piece n‖ ≤ M) → ‖fracTorusLambda α A T lam‖ ≤ C * M) ∧
    (∀ L b : ℝ, 0 < L → ‖r3Restrict L b‖ ≤ C) ∧
    (∀ b T lam : ℝ, 0 < T → T ≤ 1 → 0 < lam → lam < 1 → 0 < b → Real.sqrt (simScale α T) * b ≤ 1 / 8 →
      ‖fracTorusRestrict α (1 - lam) b T lam‖ ≤ C) ∧
    (∀ (F : ScaledMildFramework Freq.X (dilExponent α)) (P : ℝ) (k : ℕ) (θ : ℝ), 0 < P → 0 < k → 0 < θ →
      ‖fracR3Shift F P k θ‖ ≤ Real.exp (-(P / k)) ^ dilExponent α / θ) ∧
    (∀ (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1),
      0 < θ → ‖fracTorusShift α hα T lam θ hT hT1 hl hl1‖ ≤ lam ^ dilExponent α / θ)

def FracComparisonSmall (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (F : ScaledMildFramework Freq.X (dilExponent α)), F.K = Freq.fracBilinX α → F.G = Freq.fracHeatX α →
    F.D = Freq.fracDilX α → ∀ (P : ℝ) (k : ℕ) (θ b : ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] Freq.X) (ψ : TestLift E J b)
    (A : Approximant (MildFramework.stepLength P k) b) (hl : 0 < Real.exp (-(P / k)))
    (hl1 : Real.exp (-(P / k)) ≤ 1),
    0 < P → 0 < k → MildFramework.stepLength P k ≤ 1 / 2 → Real.exp (-(P / k)) ^ dilExponent α < θ →
    θ < 1 → 0 < b → ∀ δ : ℝ, 0 < δ → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), T < T₀ →
      ∀ Jt : E →L[ℝ] V,
        (∀ e, Jt e = (simScale α T ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α T) (ψ.field e))) →
      ‖(fracTorusRestrict α _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - fracTorusShift α hα T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (fracTorusLambda α A T (Real.exp (-(P / k))))) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - fracR3Shift F P k θ)).comp (fracR3Lambda α A))‖ ≤ δ ∧
      ‖(fracTorusRestrict α _ b T (Real.exp (-(P / k)))).comp
          ((Ring.inverse (1 - fracTorusShift α hα T (Real.exp (-(P / k))) θ hT hT1 hl hl1)).comp
            (fracTorusSeed α hα T (Real.exp (-(P / k))) hT hT1 hl hl1 Jt)) -
        (r3Restrict _ b).comp ((Ring.inverse (1 - fracR3Shift F P k θ)).comp (fracR3Seed F P k J))‖ ≤ δ

end Breakdown.Periodic
