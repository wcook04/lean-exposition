import PCP.Complexity.AmplifiedSequenceLang
import PCP.Complexity.AmplifiedRoundCost

/-! Bounds and Boolean shape of the actual result registers after repetition. -/

namespace PCP.Lang.AmplifiedStream

open PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

theorem size_getD_le (xs : List ℕ) (i : ℕ) : Nat.size (xs.getD i 0) ≤ listSize xs := by
  induction xs generalizing i with
  | nil => simp [listSize]
  | cons x xs ih =>
      cases i with
      | zero => simp [listSize]; omega
      | succ i =>
          simp only [List.getD_cons_succ]
          have h := ih i
          simp only [listSize, List.map_cons, List.sum_cons] at h ⊢
          omega

structure Output (st : State 420 140) (C : ℕ) : Prop where
  tag : st.regs 402 ≤ 1
  halt : st.regs 402 = 0 → st.regs 403 ≤ 1
  query : st.regs 402 ≠ 0 → Nat.size (st.regs 403) ≤ C

attribute [local irreducible] round consume

theorem copies_output (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (N C : ℕ) (hB : Bounded P qs N C) (k : ℕ)
    (st : State 420 140) (b : ℕ) (x bits answers : List Bool)
    (hs : Ready st b x bits answers) (hb : b ≤ N) (hx : x.length ≤ N) :
    Output ((copies P k).run st).1 C := by
  induction k generalizing st bits answers with
  | zero => constructor <;> simp [copies, Stmt.run, Expr.eval, Function.update]
  | succ k ih =>
      let s := ((round P).run st).1
      have hr := round_run P qs fs hc st b x bits answers hs
      have hready := round_ready P st b x bits answers hs
      change s.lists 103 = _ ∧ s.regs 403 = _ ∧ s.regs 402 = _ at hr
      change Ready s b x (bits.drop b) answers at hready
      rw [copies, run_seq_fst]
      change Output ((Stmt.ite 402 .skip
        (.ite 403 (.seq consume (copies P k)) .skip)).run s).1 C
      by_cases hshort : answers.length < (qs x (paddedBits b bits)).length
      · have ht : ((Stmt.ite 402 .skip
            (.ite 403 (.seq consume (copies P k)) .skip)).run s).1 = s := by
          simp [Stmt.run, hr.2.2, hshort]
        rw [ht]
        constructor
        · simp [hr.2.2, hshort]
        · simp [hr.2.2, hshort]
        · intro _
          rw [hr.2.1, ite_eq_left hshort]
          exact (size_getD_le _ _).trans
            (hB.queries x (paddedBits b bits) hx (by simpa using hb))
      · simp only [hshort, ↓reduceIte] at hr
        cases hv : fs x (paddedBits b bits)
            (PCP.QueryTree.answersOracle (qs x (paddedBits b bits)) answers)
        · have ht : ((Stmt.ite 402 .skip
              (.ite 403 (.seq consume (copies P k)) .skip)).run s).1 = s := by
            simp [Stmt.run, hr.2.2, hr.2.1, hv]
          rw [ht]
          constructor <;> simp [hr.2.2, hr.2.1, hv]
        · have ht := consume_ready s b x (bits.drop b) answers hready
          rw [hr.1] at ht
          have hi := ih (consume.run s).1 (bits.drop b)
            (answers.drop (qs x (paddedBits b bits)).length) ht
          simpa [run_ite_fst, hr.2.2, hr.2.1, hv, run_seq_fst] using hi

end PCP.Lang.AmplifiedStream
