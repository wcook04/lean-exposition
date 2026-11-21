import Breakdown.Transfer.StatementsDefs

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

variable {E Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

open Classical in
def seqOp (A : ℕ → E →L[ℝ] X) : lp (fun _ : ℕ => E) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞ :=
  if h : ∃ T : lp (fun _ : ℕ => E) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞, ∀ g n, T g n = A n (g n)
  then h.choose else 0

open Classical in
def seqShift (A : ℕ → X →L[ℝ] X) : lp (fun _ : ℕ => X) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞ :=
  if h : ∃ T : lp (fun _ : ℕ => X) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞,
      ∀ g n, T g n = if n = 0 then 0 else A (n - 1) (g (n - 1))
  then h.choose else 0

open Classical in
def seqSeed (A : E →L[ℝ] X) : E →L[ℝ] lp (fun _ : ℕ => X) ∞ :=
  if h : ∃ T : E →L[ℝ] lp (fun _ : ℕ => X) ∞, ∀ e n, T e n = if n = 0 then A e else 0
  then h.choose else 0

open Classical in
def pieceComp (L : ℝ) (A : E →L[ℝ] X) : Piece E L →L[ℝ] Piece X L :=
  if h : ∃ T : Piece E L →L[ℝ] Piece X L, ∀ f s, T f s = A (f s) then h.choose else 0

open Classical in
def pieceConv (L : ℝ) (Λ : ℝ → Z →L[ℝ] X) (w : C(Icc (0 : ℝ) L, ℝ)) : Piece Z L →L[ℝ] Piece X L :=
  if h : ∃ T : Piece Z L →L[ℝ] Piece X L, ∀ ζ (s : Icc (0 : ℝ) L),
      T ζ s = ∫ σ in (0 : ℝ)..s, (extendPiece w σ) • Λ (s - σ) (extendPiece ζ σ)
  then h.choose else 0

def SeqOpSpec : Prop :=
  ∀ (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (A : ℕ → E →L[ℝ] X) (C : ℝ),
    (∀ n, ‖A n‖ ≤ C) → 0 ≤ C →
      (∀ g n, seqOp A g n = A n (g n)) ∧ ‖seqOp A‖ ≤ C ∧
      (∀ (B : ℕ → X →L[ℝ] X), (∀ n, ‖B n‖ ≤ C) →
        (∀ g n, seqShift B g n = if n = 0 then 0 else B (n - 1) (g (n - 1))) ∧ ‖seqShift B‖ ≤ C) ∧
      (∀ A₀ : E →L[ℝ] X, (∀ e n, seqSeed A₀ e n = if n = 0 then A₀ e else 0) ∧ ‖seqSeed A₀‖ ≤ ‖A₀‖)

def PieceCompSpec : Prop :=
  ∀ (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (L : ℝ) (A : E →L[ℝ] X),
      0 ≤ L → (∀ f s, pieceComp L A f s = A (f s)) ∧ ‖pieceComp L A‖ ≤ ‖A‖

def PieceConvSpec : Prop :=
  ∀ (Z X : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (L : ℝ) (Λ : ℝ → Z →L[ℝ] X) (w : C(Icc (0 : ℝ) L, ℝ)) (C : ℝ), 0 < L → L ≤ 1 → 0 ≤ C →
    (∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ))) →
    (∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) →
      (∀ ζ (s : Icc (0 : ℝ) L),
        pieceConv L Λ w ζ s = ∫ σ in (0 : ℝ)..s, (extendPiece w σ) • Λ (s - σ) (extendPiece ζ σ)) ∧
      ‖pieceConv L Λ w‖ ≤ 4 * C * L ^ (1 / 4 : ℝ) * ‖w‖

end Breakdown.Periodic
