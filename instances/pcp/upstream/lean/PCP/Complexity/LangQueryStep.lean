import PCP.Complexity.LangLookup
import PCP.Verifier.QueryListAlgorithm

/-!
# The actual answer-history next-query protocol

The routine consumes a work copy of the query addresses for exactly the stored
answer-history length. It returns the next query if present, or the supplied
verdict if the query list is exhausted. Both source lists are preserved.
-/

namespace PCP.Lang.QueryStep

/-- Register one receives a head and register two records whether it exists. -/
def pop : Stmt 4 3 := .pop 2 1 2

/-- Query addresses are in list zero, answers in list one, verdict in register three. -/
def setup : Stmt 4 3 := .seq (.copy 0 2) (.len 1 0)

def scan : Stmt 4 3 := .seq (.loop 0 pop) pop

/-- Result: query/halt tag in register two and address/verdict in register one. -/
def program : Stmt 4 3 :=
  .seq setup (.seq scan (.ite 2 .skip (.assign 1 (.var 3))))

theorem pop_tail (st : State 4 3) : (pop.run st).1.lists 2 = (st.lists 2).tail := by
  cases h : st.lists 2 <;> simp [pop, Stmt.run, h, Function.update]

theorem pop_head (st : State 4 3) :
    (pop.run st).1.regs 1 = (st.lists 2).headD 0 ∧
    (pop.run st).1.regs 2 = (if st.lists 2 = [] then 0 else 1) := by
  cases h : st.lists 2 <;> simp [pop, Stmt.run, h, Function.update]

theorem pop_iterate (c k : ℕ) (st : State 4 3) :
    (iterate pop.run c k st).1.lists 2 = (st.lists 2).drop k := by
  induction k generalizing st with
  | zero => simp [iterate]
  | succ k ih =>
      rw [iterate_succ_fst, ih, pop_tail, ← List.drop_one, List.drop_drop]
      simp [Nat.add_comm]

theorem scan_run (st : State 4 3) :
    (scan.run st).1.regs 1 = (st.lists 2).getD (st.regs 0) 0 ∧
    (scan.run st).1.regs 2 = (if st.regs 0 < (st.lists 2).length then 1 else 0) := by
  simp only [scan, run_seq_fst, run_loop_fst, (pop_head _).1, (pop_head _).2, pop_iterate]
  simp [List.getD_eq_getElem?_getD, List.drop_eq_nil_iff]
  split_ifs <;> omega

theorem program_run (st : State 4 3) :
    (program.run st).1.regs 1 =
      (if (st.lists 1).length < (st.lists 0).length then
        (st.lists 0).getD (st.lists 1).length 0 else st.regs 3) ∧
    (program.run st).1.regs 2 =
      (if (st.lists 1).length < (st.lists 0).length then 1 else 0) := by
  let s := (setup.run st).1
  have h0 : s.regs 0 = (st.lists 1).length := by
    simp [s, setup, Stmt.run, Function.update]
  have hL : s.lists 2 = st.lists 0 := by simp [s, setup, Stmt.run, Function.update]
  have h3 : (scan.run s).1.regs 3 = st.regs 3 := by
    have hf := run_regs_frame scan 3 (by decide) s
    simpa [s, setup, Stmt.run, Function.update] using hf
  obtain ⟨ha, ht⟩ := scan_run s
  rw [h0, hL] at ha ht
  simp only [program, run_seq_fst]
  change ((Stmt.ite 2 .skip (.assign 1 (.var 3))).run (scan.run s).1).1.regs 1 = _ ∧
    ((Stmt.ite 2 .skip (.assign 1 (.var 3))).run (scan.run s).1).1.regs 2 = _
  by_cases hi : (st.lists 1).length < (st.lists 0).length <;>
    simp [Stmt.run, Expr.eval, Function.update, ha, ht, h3, hi]

theorem program_sources (st : State 4 3) :
    (program.run st).1.lists 0 = st.lists 0 ∧
    (program.run st).1.lists 1 = st.lists 1 :=
  ⟨run_lists_frame program 0 (by decide) st, run_lists_frame program 1 (by decide) st⟩

/-- Interpret the routine's finite result tag without changing the verifier protocol. -/
def result (st : State 4 3) : Bool ⊕ ℕ :=
  if st.regs 2 = 0 then .inl (decide (st.regs 1 ≠ 0)) else .inr (st.regs 1)

/-- This is exactly `listStep`, including short and surplus answer histories. -/
theorem program_listStep (st : State 4 3) (bs : List Bool) (f : PCP.ProofOracle → Bool)
    (hB : st.lists 1 = bs.map Bool.toNat)
    (hV : st.regs 3 = (f (PCP.QueryTree.answersOracle (st.lists 0) bs)).toNat) :
    result (program.run st).1 = PCP.QueryTree.listStep (st.lists 0) f bs := by
  obtain ⟨hv, ht⟩ := program_run st
  simp only [hB, List.length_map] at hv ht
  by_cases hi : bs.length < (st.lists 0).length
  · rw [PCP.QueryTree.listStep_next _ _ _ hi]
    simp [result, hv, ht, hi, List.getD_eq_getElem?_getD]
  · rw [PCP.QueryTree.listStep_halt _ _ _ (by omega)]
    simp only [result, ht, ite_eq_right hi, hv, hV]
    cases f (PCP.QueryTree.answersOracle (st.lists 0) bs) <;> rfl

private theorem pop_space (st : State 4 3) :
    listSize ((pop.run st).1.lists 2) ≤ listSize (st.lists 2) := by
  rw [pop_tail]
  cases st.lists 2 <;> simp [listSize]

private theorem pop_cost (st : State 4 3) :
    (pop.run st).2 ≤ listSize (st.lists 2) + 1 := by
  cases h : st.lists 2 with
  | nil => simp [pop, Stmt.run, h]
  | cons x xs => simp [pop, Stmt.run, listSize, h]; omega

private theorem scan_cost (st : State 4 3) (S : ℕ) (hS : listSize (st.lists 2) ≤ S) :
    (scan.run st).2 ≤ (st.regs 0 + 1) * (Nat.size (st.regs 0) + S + 2) + 1 := by
  have hi := iterate_cost_le pop.run (Nat.size (st.regs 0) + 1) (S + 1)
    (fun s : State 4 3 => listSize (s.lists 2) ≤ S)
    (fun s hs => (pop_space s).trans hs)
    (fun s hs => (pop_cost s).trans (Nat.add_le_add_right hs 1)) (st.regs 0) st hS
  have hf := iterate_frame pop.run (Nat.size (st.regs 0) + 1)
    (fun s : State 4 3 => listSize (s.lists 2) ≤ S)
    (fun s hs => (pop_space s).trans hs) (st.regs 0) st hS
  have hp := (pop_cost (iterate pop.run (Nat.size (st.regs 0) + 1) (st.regs 0) st).1).trans
    (Nat.add_le_add_right hf 1)
  simp only [scan, run_seq_snd, run_loop_snd, run_loop_fst]
  nlinarith

/-- The scan is polynomial in stored history/query size, even for surplus answers. -/
theorem program_cost (st : State 4 3) :
    (program.run st).2 ≤ 20 *
      (listSize (st.lists 0) + listSize (st.lists 1) + Nat.size (st.regs 3) + 2) ^ 2 := by
  let W := listSize (st.lists 0) + listSize (st.lists 1) + Nat.size (st.regs 3) + 1
  let s := (setup.run st).1
  have h0 : s.regs 0 = (st.lists 1).length := by
    simp [s, setup, Stmt.run, Function.update]
  have hL : s.lists 2 = st.lists 0 := by simp [s, setup, Stmt.run, Function.update]
  have h3 : (scan.run s).1.regs 3 = st.regs 3 := by
    have hf := run_regs_frame scan 3 (by decide) s
    simpa [s, setup, Stmt.run, Function.update] using hf
  have hs := scan_cost s (listSize (st.lists 0)) (by rw [hL])
  rw [h0] at hs
  have hlen : (st.lists 1).length ≤ W := by
    have := length_le_listSize (st.lists 1); dsimp [W]; omega
  have hsize : Nat.size (st.lists 1).length ≤ W := (size_le_self _).trans hlen
  have hqs : listSize (st.lists 0) ≤ W := by dsimp [W]; omega
  have hbs : listSize (st.lists 1) ≤ W := by dsimp [W]; omega
  have hv : Nat.size (st.regs 3) ≤ W := by dsimp [W]; omega
  have hscan := Nat.mul_le_mul (Nat.add_le_add_right hlen 1)
    (show Nat.size (st.lists 1).length + listSize (st.lists 0) + 2 ≤ 2 * (W + 1) by omega)
  have htag : Nat.size ((scan.run s).1.regs 2) ≤ 1 := by
    rw [(scan_run s).2]
    split <;> simp
  have ht : ((Stmt.ite 2 .skip (.assign 1 (.var 3))).run (scan.run s).1).2 ≤ 2 * W + 3 := by
    simp only [Stmt.run]
    split
    · omega
    · simp only [Expr.cost, Expr.readSize, Expr.eval]
      rw [h3]
      omega
  have hsetup : (setup.run st).2 ≤ 3 * W + 3 := by
    simp [setup, Stmt.run, Function.update]
    omega
  change (setup.run st).2 + ((scan.run s).2 +
    ((Stmt.ite 2 .skip (.assign 1 (.var 3))).run (scan.run s).1).2 + 1) + 1 ≤
      20 * (W + 1) ^ 2
  nlinarith

end PCP.Lang.QueryStep
