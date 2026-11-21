import Breakdown.Transfer.StatementsDefs

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def VarConstIntegralStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (u v : ℝ → X) (a b M N : ℝ), a ≤ b → ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) →
    (∀ s ∈ Icc a b, ‖u s‖ ≤ M) → (∀ s ∈ Icc a b, ‖v s‖ ≤ N) →
    (∀ t ∈ Icc a b, IntervalIntegrable (fun s => H.K (t - s) (u s) (v s)) volume a t) ∧
    (∀ t ∈ Icc a b, t - a ≤ 1 →
      ‖∫ s in a..t, H.K (t - s) (u s) (v s)‖ ≤ 4 * H.CK * (t - a) ^ (1 / 4 : ℝ) * M * N) ∧
    ContinuousOn (fun t => ∫ s in a..t, H.K (t - s) (u s) (v s)) (Icc a b)

def PieceOperatorStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (T : ℝ), 0 < T →
    (∀ (f g : Piece X T) (t : Icc (0 : ℝ) T),
      H.pieceBil T f g t = ∫ s in (0 : ℝ)..t, H.K (t - s) (extendPiece f s) (extendPiece g s)) ∧
    (T ≤ 1 → ‖H.pieceBil T‖ ≤ 4 * H.CK * T ^ (1 / 4 : ℝ)) ∧
    (∀ (x : X) (t : Icc (0 : ℝ) T), H.pieceFree T x t = H.G t x) ∧
    ‖H.pieceFree T‖ ≤ 1

def RestrictStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (u : ℝ → X) (a m t : ℝ), a ≤ m → m ≤ t → ContinuousOn u (Icc a t) →
    H.VarConst u a m → H.VarConst u a t → H.VarConst u m t

def ConcatStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (u : ℝ → X) (a m t : ℝ), a ≤ m → m ≤ t → ContinuousOn u (Icc a t) →
    H.VarConst u a m → H.VarConst u m t → H.VarConst u a t

def ShiftStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (u : ℝ → X) (a t c : ℝ), H.VarConst u a t ↔ H.VarConst (fun s => u (s + c)) (a - c) (t - c)

def UniqueStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (u v : ℝ → X) (a b : ℝ),
    (H.IsMildOn u a b → H.IsMildOn v a b → u a = v a → ∀ t ∈ Ico a b, u t = v t) ∧
    (H.IsMildOnIcc u a b → H.IsMildOnIcc v a b → u a = v a → ∀ t ∈ Icc a b, u t = v t)

def SmallDataStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X),
    ∃ c > 0, ∀ x : X, ‖x‖ ≤ c → ∃ u : ℝ → X, u 0 = x ∧ H.IsMildOnIcc u 0 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ ≤ 2 * ‖x‖

def CompactSimpleStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (T : ℝ) (y : X) (φ : C(Icc (0 : ℝ) T, ℝ)) (f : Piece X T), 0 < T → T ≤ 1 →
    (∀ τ, 0 < τ → IsCompactOperator (H.K τ y)) → (∀ t, f t = φ t • y) →
    IsCompactOperator ((pieceEnd T).comp (H.pieceBil T f))

def CompactPieceStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (T : ℝ), 0 < T → T ≤ 1 → H.HasCompactKernel →
    ∀ f : Piece X T, IsCompactOperator ((pieceEnd T).comp (H.pieceBil T f))

def PiecePerturbationStatement : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)
    (T : ℝ) (ub v : Piece X T) (x : X), 0 < T → T ≤ 1 →
    H.IsMildOnIcc (extendPiece ub) 0 T →
    v = H.pieceFree T x + (2 : ℝ) • H.pieceBil T ub v + H.pieceBil T v v →
    extendPiece v 0 = x ∧ H.IsMildOnIcc (extendPiece (ub + v)) 0 T

end Breakdown
