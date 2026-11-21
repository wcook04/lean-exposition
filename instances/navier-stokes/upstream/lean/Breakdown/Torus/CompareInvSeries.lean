import Breakdown.Torus.CompareStatements

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace CompareInvSeries.Internal

theorem inverse_fixed {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : F →L[ℝ] F) (hT : ‖T‖ < 1) (y : F) :
    Ring.inverse (1 - T) y - T (Ring.inverse (1 - T) y) = y := by
  have h := congrArg (fun f : F →L[ℝ] F => f y)
    (Ring.mul_inverse_cancel (1 - T) (isUnit_one_sub_of_norm_lt_one hT))
  simpa using h

theorem shiftChain_self {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ℕ → X →L[ℝ] X) (n : ℕ) : shiftChain B n n = ContinuousLinearMap.id ℝ X := by
  cases n with
  | zero => simp [shiftChain]
  | succ n => simp [shiftChain]

theorem shiftChain_succ_of_ne {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ℕ → X →L[ℝ] X) (m n : ℕ) (h : m ≠ n + 1) :
    shiftChain B m (n + 1) = (B n).comp (shiftChain B m n) := by
  simp [shiftChain, h]

end CompareInvSeries.Internal

open CompareInvSeries.Internal

theorem invSeriesEntry : InvSeriesEntry := by
  intro X _ _ _ B hB hS g n
  set x := Ring.inverse (1 - seqShift B) g with hx
  have hfix : x - seqShift B x = g := inverse_fixed (seqShift B) hB g
  have hpt : ∀ k, x k = g k + seqShift B x k := by
    intro k
    have h := congrArg (fun v : lp (fun _ : ℕ => X) ∞ => (v : ℕ → X) k) hfix
    simp only [lp.coeFn_sub, Pi.sub_apply] at h
    rw [← h]
    abel
  induction n with
  | zero =>
    rw [hpt 0, hS x 0]
    simp [shiftChain_self]
  | succ n ih =>
    rw [hpt (n + 1), hS x (n + 1), Finset.sum_range_succ, shiftChain_self]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, ih, map_sum,
      ContinuousLinearMap.id_apply]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [shiftChain_succ_of_ne B m n (by
      have := Finset.mem_range.mp hm
      omega)]
    rfl

theorem shiftChainNorm : ShiftChainNorm := by
  intro X _ _ B C hC hB m n hmn
  induction n, hmn using Nat.le_induction with
  | base =>
    rw [shiftChain_self, Nat.sub_self, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n hmn ih =>
    rw [shiftChain_succ_of_ne B m n (by omega), Nat.succ_sub hmn, pow_succ']
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hB n) ih (norm_nonneg _) hC)

end Breakdown.Periodic
