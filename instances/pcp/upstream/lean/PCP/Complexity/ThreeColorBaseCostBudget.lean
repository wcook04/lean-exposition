import PCP.Complexity.ThreeColorBaseBranchCost

/-! # Polynomial absorption for the actual base-verifier program -/

namespace PCP.Lang.ThreeColorBaseBranches

open PCP.Algebraic ThreeColorFullFieldSampling ThreeColorBasePreflight ThreeColorBaseSetup

theorem history_budget (x bs : List Bool) (qs : List ℕ) (Cq dq n : ℕ)
    (hn : x.length + bs.length + 1 ≤ n) (hq : listSize qs ≤ Cq * n ^ dq) :
    x.length + listSize qs + bs.length + 1 ≤ (Cq + 1) * n ^ (dq + 1) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : n ≤ n ^ (dq + 1) := Nat.le_pow (by omega)
  have hq' : listSize qs ≤ Cq * n ^ (dq + 1) :=
    hq.trans (Nat.mul_le_mul_left Cq (Nat.pow_le_pow_right hn1 (by omega)))
  nlinarith

theorem branch_history_cost (Cb db Cq dq n e : ℕ) (hb : BranchCost Cb db)
    (hde : (dq + 1) * db ≤ e) (x bits bs : List Bool) (qs : List ℕ)
    (hv : Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits))
    (hn : x.length + bs.length + 1 ≤ n) (hq : listSize qs ≤ Cq * n ^ dq)
    (i : Fin 7) (st : State 400 128) (hc : Context x bits bs qs st) :
    ((branch i).run st).2 ≤ Cb * (Cq + 1) ^ db * n ^ e := by
  have h := hb x bits bs qs hv i st hc
  have harg := history_budget x bs qs Cq dq n hn hq
  calc
    _ ≤ Cb * ((Cq + 1) * n ^ (dq + 1)) ^ db := h.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg db))
    _ = Cb * (Cq + 1) ^ db * n ^ ((dq + 1) * db) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
    _ ≤ Cb * (Cq + 1) ^ db * n ^ e := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) hde)


end PCP.Lang.ThreeColorBaseBranches
