import PCP.Complexity.AmplifiedRound

/-! Concrete sequential repetition, with no evaluation of the fixed repetition count. -/

namespace PCP.Lang.AmplifiedStream

open PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

def copies (P : Stmt 400 128) : ℕ → Stmt 420 140
  | 0 => .seq (.assign 402 (.const 0)) (.assign 403 (.const 1))
  | k+1 => .seq (round P) (.ite 402 .skip
      (.ite 403 (.seq consume (copies P k)) .skip))

def result (st : State 420 140) : Bool ⊕ ℕ :=
  if st.regs 402 = 0 then .inl (decide (st.regs 403 ≠ 0)) else .inr (st.regs 403)

attribute [local irreducible] round consume

theorem copies_run (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (k : ℕ) (st : State 420 140) (b : ℕ) (x bits answers : List Bool)
    (hs : Ready st b x bits answers) :
    result ((copies P k).run st).1 = slicedSequence b (qs x) (fs x) k bits answers := by
  induction k generalizing st bits answers with
  | zero => simp [copies, Stmt.run, Expr.eval, Function.update, result, slicedSequence]
  | succ k ih =>
      let s := ((round P).run st).1
      have hr := round_run P qs fs hc st b x bits answers hs
      have hready := round_ready P st b x bits answers hs
      change s.lists 103 = _ ∧ s.regs 403 = _ ∧ s.regs 402 = _ at hr
      change Ready s b x (bits.drop b) answers at hready
      rw [copies, run_seq_fst]
      change result ((Stmt.ite 402 .skip
        (.ite 403 (.seq consume (copies P k)) .skip)).run s).1 = _
      rw [slicedSequence, PCP.QueryTree.thenStep_slicing]
      by_cases hshort : answers.length < (qs x (paddedBits b bits)).length
      · simp [hr.2.2, hshort, Stmt.run, result, hr.2.1,
          List.getD_eq_getElem?_getD]
      · simp only [hshort, ↓reduceIte] at hr
        rw [dite_eq_right hshort]
        cases hv : fs x (paddedBits b bits)
            (PCP.QueryTree.answersOracle (qs x (paddedBits b bits)) answers)
        · simp [hr.2.2, hr.2.1, hv, Stmt.run, result]
        · have ht := consume_ready s b x (bits.drop b) answers hready
          rw [hr.1] at ht
          have hi := ih (consume.run s).1 (bits.drop b)
            (answers.drop (qs x (paddedBits b bits)).length) ht
          simpa [run_ite_fst, hr.2.2, hr.2.1, hv, run_seq_fst] using hi

end PCP.Lang.AmplifiedStream
