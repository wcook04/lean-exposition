import PCP.Complexity.AmplifiedSequenceLang
import PCP.Complexity.AmplifiedRoundCost

/-! Polynomial charged runtime for every fixed repetition count. -/

namespace PCP.Lang.AmplifiedStream

open PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

attribute [local irreducible] round consume

theorem copies_cost (P : Stmt 400 128) (qs : List Bool → List Bool → List ℕ)
    (fs : List Bool → List Bool → PCP.ProofOracle → Bool) (hc : Correct P qs fs)
    (N C : ℕ) (hB : Bounded P qs N C) (k : ℕ)
    (st : State 420 140) (b : ℕ) (x bits answers : List Bool)
    (hs : Ready st b x bits answers) (hb : b ≤ N) (hx : x.length ≤ N)
    (hbits : bits.length ≤ N) (has : answers.length ≤ N) :
    ((copies P k).run st).2 ≤ (k+1)*5000*(N+C+1)^2 := by
  induction k generalizing st bits answers with
  | zero =>
      have hp : 1 ≤ (N+C+1)^2 := one_le_pow₀ (by omega)
      simp only [copies, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
      norm_num
      omega
  | succ k ih =>
      let s := ((round P).run st).1
      have hr := round_run P qs fs hc st b x bits answers hs
      have hready := round_ready P st b x bits answers hs
      have hcost := round_cost P qs fs hc N C hB st b x bits answers hs hb hx hbits has
      change s.lists 103 = _ ∧ s.regs 403 = _ ∧ s.regs 402 = _ at hr
      change Ready s b x (bits.drop b) answers at hready
      have hp : 1 ≤ (N+C+1)^2 := one_le_pow₀ (by omega)
      rw [copies, run_seq_snd]
      change ((round P).run st).2 + ((Stmt.ite 402 .skip
        (.ite 403 (.seq consume (copies P k)) .skip)).run s).2+1 ≤ _
      by_cases hshort : answers.length < (qs x (paddedBits b bits)).length
      · have ht : ((Stmt.ite 402 .skip
            (.ite 403 (.seq consume (copies P k)) .skip)).run s).2 = 3 := by
          simp [Stmt.run, hr.2.2, hshort]
        rw [ht]
        nlinarith
      · simp only [hshort, ↓reduceIte] at hr
        cases hv : fs x (paddedBits b bits)
            (PCP.QueryTree.answersOracle (qs x (paddedBits b bits)) answers)
        · have ht : ((Stmt.ite 402 .skip
              (.ite 403 (.seq consume (copies P k)) .skip)).run s).2 = 3 := by
            simp [Stmt.run, hr.2.2, hr.2.1, hv]
          rw [ht]
          nlinarith
        · have ht := consume_ready s b x (bits.drop b) answers hready
          rw [hr.1] at ht
          have hi := ih (consume.run s).1 (bits.drop b)
            (answers.drop (qs x (paddedBits b bits)).length) ht
            (by simpa only [List.length_drop] using (Nat.sub_le bits.length b).trans hbits)
            (by simpa only [List.length_drop] using
              (Nat.sub_le answers.length _).trans has)
          have hq : listSize (s.lists 103) ≤ C := by
            rw [hr.1]
            exact hB.queries x (paddedBits b bits) hx (by simpa using hb)
          have ha : listSize (s.lists 132) ≤ 2*N := by
            rw [hready.answers]
            exact (boolList_size answers).trans (Nat.mul_le_mul_left 2 has)
          have hconsume := consume_cost_bound s N C hready.empty ha hq
          have htail : ((Stmt.ite 402 .skip
              (.ite 403 (.seq consume (copies P k)) .skip)).run s).2 =
                (consume.run s).2 + ((copies P k).run (consume.run s).1).2 + 4 := by
            simp [Stmt.run, hr.2.2, hr.2.1, hv]
          rw [htail]
          nlinarith

end PCP.Lang.AmplifiedStream
