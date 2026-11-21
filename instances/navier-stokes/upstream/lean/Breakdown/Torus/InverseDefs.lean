import Breakdown.Torus.StatementsShell
import Breakdown.Torus.SeqDefs
import Breakdown.Torus.StatementsSeqOps
import Breakdown.Transfer.StatementsFrame

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

abbrev R3Seq (L : ℝ) := lp (fun _ : ℕ => Piece Freq.X L) ∞

abbrev TorusSeq (L : ℝ) := lp (fun _ : ℕ => Piece V L) ∞

abbrev ShellSeq (L : ℝ) := lp (fun _ : ℕ => Piece ShellData L) ∞

structure Approximant (L b : ℝ) where
  terms : ℕ
  field : ℕ → Fin terms → Space → Space
  isTest : ∀ n l, IsTestField (field n l)
  support : ∀ n l, tsupport (field n l) ⊆ Metric.closedBall 0 b
  weight : ℕ → Fin terms → C(Icc (0 : ℝ) L, ℝ)
  bound : ∃ C : ℝ, ∀ n l, ‖Freq.embedX (field n l)‖ ≤ C ∧ ‖weight n l‖ ≤ C

def Approximant.r3Piece {L b : ℝ} (A : Approximant L b) (n : ℕ) : Piece Freq.X L :=
  ⟨fun s => ∑ l, A.weight n l s • Freq.embedX (A.field n l), by fun_prop⟩

def Approximant.torusPiece {L b : ℝ} (A : Approximant L b) (μ : ℝ) (n : ℕ) : Piece V L :=
  ⟨fun s => ∑ l, A.weight n l s • ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ (A.field n l))), by fun_prop⟩

def r3Lambda {L b : ℝ} (A : Approximant L b) : ShellSeq L →L[ℝ] R3Seq L :=
  seqOp fun n => ∑ l, pieceConv L (fun τ => lambdaR3 (A.field n l) (A.isTest n l) b τ) (A.weight n l)

def torusLambda {L b : ℝ} (A : Approximant L b) (T lam : ℝ) : ShellSeq L →L[ℝ] TorusSeq L :=
  seqOp fun n => ∑ l,
    pieceConv L (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ) (A.weight n l)

def r3Restrict (L b : ℝ) : R3Seq L →L[ℝ] ShellSeq L := seqOp fun _ => pieceComp L (restrictR3 b)

def torusRestrict (L b T lam : ℝ) : TorusSeq L →L[ℝ] ShellSeq L :=
  seqOp fun n => pieceComp L (restrictTorus (stepScale T lam n) b)

def r3Shift (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) (θ : ℝ) :
    R3Seq (MildFramework.stepLength P k) →L[ℝ] R3Seq (MildFramework.stepLength P k) :=
  seqShift fun _ => θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)

def torusShift (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) : TorusSeq (1 - lam) →L[ℝ] TorusSeq (1 - lam) :=
  seqShift fun n => (lam ^ (1 / 4 : ℝ) / θ) •
    ((stepFrame hK (stepScale T lam (n + 1)) (stepScale_pos hT hl (n + 1))
      (stepScale_le_one hT1 hl hl1 (n + 1))).pieceFree (1 - lam)).comp (pieceEnd (1 - lam))

def r3Seed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : MildFramework Freq.X) (P : ℝ)
    (k : ℕ) (J : E →L[ℝ] Freq.X) : E →L[ℝ] R3Seq (MildFramework.stepLength P k) :=
  seqSeed ((F.stepFree P k).comp J)

def torusSeed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (hK : KernelSharpBound)
    (T lam : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (Jt : E →L[ℝ] V) :
    E →L[ℝ] TorusSeq (1 - lam) :=
  seqSeed (((stepFrame hK (stepScale T lam 0) (stepScale_pos hT hl 0)
      (stepScale_le_one hT1 hl hl1 0)).pieceFree (1 - lam)).comp Jt)

def r3Op {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : MildFramework Freq.X) (P : ℝ)
    (k : ℕ) (θ : ℝ) (J : E →L[ℝ] Freq.X) (f : ℕ → Piece Freq.X (MildFramework.stepLength P k)) :
    E × R3Seq (MildFramework.stepLength P k) →L[ℝ] R3Seq (MildFramework.stepLength P k) :=
  ContinuousLinearMap.snd ℝ _ _ - (r3Shift F P k θ).comp (ContinuousLinearMap.snd ℝ _ _) -
    (r3Seed F P k J).comp (ContinuousLinearMap.fst ℝ _ _) -
    (seqOp fun n => (2 : ℝ) • F.toHeatBilinear.pieceBil (MildFramework.stepLength P k) (f n)).comp
      (ContinuousLinearMap.snd ℝ _ _)

def torusOp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (hK : KernelSharpBound)
    (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (Jt : E →L[ℝ] V)
    (f : ℕ → Piece V (1 - lam)) : E × TorusSeq (1 - lam) →L[ℝ] TorusSeq (1 - lam) :=
  ContinuousLinearMap.snd ℝ _ _ - (torusShift hK T lam θ hT hT1 hl hl1).comp (ContinuousLinearMap.snd ℝ _ _) -
    (torusSeed hK T lam hT hT1 hl hl1 Jt).comp (ContinuousLinearMap.fst ℝ _ _) -
    (seqOp fun n => (2 : ℝ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
      (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam) (f n)).comp (ContinuousLinearMap.snd ℝ _ _)

end Breakdown.Periodic
