import Breakdown.Torus.CompareStatements
import Breakdown.Torus.ChainR3
import Breakdown.Torus.ChainTorus

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CompareLambda.Internal

theorem sum_pieceConv_apply {Z X : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} {ι : Type} (u : Finset ι)
    (T : ι → Piece Z L →L[ℝ] Piece X L) (ζ : Piece Z L) (s : Icc (0 : ℝ) L) :
    (∑ l ∈ u, T l) ζ s = ∑ l ∈ u, T l ζ s := by
  rw [_root_.sum_apply]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply]

end CompareLambda.Internal

open CompareLambda.Internal

set_option maxHeartbeats 400000 in
theorem r3LambdaFormula (hS : SeqOpSpec) (hV : PieceConvSpec) (hB : R3LambdaBound)
    (hC : HeatDivFreeContinuous) : R3LambdaFormula := by
  intro L b A hL0 hL1 ζ m s
  obtain ⟨C, hC0, hCb⟩ := hB
  obtain ⟨D0, hD0⟩ := A.bound
  have hD : 0 ≤ max D0 0 := le_max_right _ _
  have hq : 0 ≤ L ^ (1 / 4 : ℝ) := rpow_nonneg hL0.le _
  have hPC := fun n l => hV ShellData Freq.X L (fun τ => lambdaR3 (A.field n l) (A.isTest n l) b τ)
    (A.weight n l) (C * ‖Freq.embedX (A.field n l)‖) hL0 hL1 (mul_nonneg hC0 (norm_nonneg _))
    (ChainR3.Internal.lambda_bound hC0 hCb (A.field n l) (A.isTest n l) b)
    (ChainR3.Internal.lambda_cont hC (A.field n l) (A.isTest n l) b)
  have hBn : ∀ n, ‖∑ l, pieceConv L (fun τ => lambdaR3 (A.field n l) (A.isTest n l) b τ)
      (A.weight n l)‖ ≤ ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (hPC n l).2.trans ?_)
    have h1 : ‖Freq.embedX (A.field n l)‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).1
    have h2 : ‖A.weight n l‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).2
    gcongr
  have hM0 : 0 ≤ ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hTL := (hS (Piece ShellData L) (Piece Freq.X L) _ _ hBn hM0).1
  unfold r3Lambda
  rw [hTL, sum_pieceConv_apply]
  exact Finset.sum_congr rfl fun l _ => (hPC m l).1 (ζ m) s

set_option maxHeartbeats 400000 in
theorem torusLambdaFormula (hS : SeqOpSpec) (hV : PieceConvSpec) (hB : TorusLambdaBound) :
    TorusLambdaFormula := by
  intro L b T lam A hL0 hL1 hT hT1 hl hl1 hb hTb ζ m s
  obtain ⟨C, hC0, hCb⟩ := hB
  obtain ⟨D0, hD0⟩ := A.bound
  have hD : 0 ≤ max D0 0 := le_max_right _ _
  have hq : 0 ≤ L ^ (1 / 4 : ℝ) := rpow_nonneg hL0.le _
  have hsh := ChainTorus.Internal.isShellScale_step hT hT1 hl hl1 hb hTb
  have hΛ : ∀ n l τ, 0 < τ → τ ≤ 1 →
      ‖lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ‖ ≤
        C * ‖Freq.embedX (A.field n l)‖ * τ ^ (-(3 / 4 : ℝ)) := by
    intro n l τ hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hC0 (norm_nonneg _)) (rpow_nonneg hτ.le _)) fun z => ?_
    calc _ ≤ _ := hCb _ (A.isTest n l) b _ τ (hsh n) hτ
          (mul_le_one₀ (stepScale_le_one hT1 hl hl1 n) hτ.le hτ1) z
      _ = _ := by ring
  have hPC := fun n l => hV ShellData V L
    (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
    (A.weight n l) (C * ‖Freq.embedX (A.field n l)‖) hL0 hL1 (mul_nonneg hC0 (norm_nonneg _))
    (hΛ n l) (fun z => ChainTorus.Internal.lambdaTorus_continuousOn _ _ _ (stepScale_pos hT hl n) z)
  have hBn : ∀ n, ‖∑ l, pieceConv L
      (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ) (A.weight n l)‖ ≤
        ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (hPC n l).2.trans ?_)
    have h1 : ‖Freq.embedX (A.field n l)‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).1
    have h2 : ‖A.weight n l‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).2
    gcongr
  have hM0 : 0 ≤ ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hTL := (hS (Piece ShellData L) (Piece V L) _ _ hBn hM0).1
  unfold torusLambda
  rw [hTL, sum_pieceConv_apply]
  exact Finset.sum_congr rfl fun l _ => (hPC m l).1 (ζ m) s

end Breakdown.Periodic
