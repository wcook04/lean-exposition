import PCP.Complexity.LangCost
import PCP.Complexity.LangSpace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Executable decoding of stored mixed-radix seeds

Each supplied radix contributes one digit, including leading zero digits. The
program uses only materialized modulo, division, and list instructions. Radix
zero has the same total convention as natural division and remainder.
-/

namespace PCP.Lang.MixedRadixDecode

/-- Little-endian successive remainders and the unconsumed quotient. -/
def split (code : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], code)
  | radix :: radices =>
      let tail := split (code / radix) radices
      (code % radix :: tail.1, tail.2)

@[simp] theorem split_length (code : ℕ) (radices : List ℕ) :
    (split code radices).1.length = radices.length := by
  induction radices generalizing code with
  | nil => rfl
  | cons r rs ih => simp [split, ih]

/-- All emitted digits are no larger than the original code, even with zero radices. -/
theorem split_digit_le (code : ℕ) (radices : List ℕ) (d : ℕ)
    (hd : d ∈ (split code radices).1) : d ≤ code := by
  induction radices generalizing code with
  | nil => simp [split] at hd
  | cons r rs ih =>
      simp only [split, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Nat.mod_le _ _
      · exact (ih (code / r) hd).trans (Nat.div_le_self _ _)

/-- Every fixed-width digit list has a polynomial encoded size. -/
theorem split_listSize (code : ℕ) (radices : List ℕ) :
    listSize (split code radices).1 ≤ radices.length * (Nat.size code + 1) := by
  unfold listSize
  have h := List.sum_le_sum (l := (split code radices).1)
    (f := fun d => Nat.size d + 1) (g := fun _ => Nat.size code + 1)
    (fun d hd => Nat.add_le_add_right (Nat.size_le_size (split_digit_le code radices d hd)) 1)
  simpa using h

/-- Register zero is the current quotient; register two receives the next radix. -/
def body : Stmt 5 2 :=
  .seq (.pop 0 2 4) (.seq (.assign 3 (.mod 0 2))
    (.seq (.assign 0 (.div 0 2)) (.push 1 3)))

/-- Capture the number of stored radices, consume precisely those many, then restore digit order. -/
def program : Stmt 5 2 := .seq (.len 0 1) (.seq (.loop 1 body) (.rev 1))

theorem body_step (st : State 5 2) (r : ℕ) (rs : List ℕ)
    (h : st.lists 0 = r :: rs) :
    (body.run st).1.regs 0 = st.regs 0 / r ∧
    (body.run st).1.lists 0 = rs ∧
    (body.run st).1.lists 1 = st.regs 0 % r :: st.lists 1 := by
  simp [body, Stmt.run, Expr.eval, Function.update, h]

/-- The loop realizes successive division, with a reversed output accumulator. -/
theorem iterate_result (c : ℕ) (rs : List ℕ) (st : State 5 2)
    (h : st.lists 0 = rs) :
    (iterate body.run c rs.length st).1.regs 0 = (split (st.regs 0) rs).2 ∧
    (iterate body.run c rs.length st).1.lists 0 = [] ∧
    (iterate body.run c rs.length st).1.lists 1 =
      (split (st.regs 0) rs).1.reverse ++ st.lists 1 := by
  induction rs generalizing st with
  | nil => simp [iterate, split, h]
  | cons r rs ih =>
      obtain ⟨h0, hL, hA⟩ := body_step st r rs h
      obtain ⟨hq, hE, hD⟩ := ih (body.run st).1 hL
      rw [List.length_cons, iterate_succ_fst]
      refine ⟨?_, hE, ?_⟩
      · simpa only [split, h0] using hq
      · simp only [hD, h0, hA, split, List.reverse_cons, List.append_assoc,
          List.singleton_append]

/-- Exact output, final quotient, and exhausted input. Existing output is reversed and kept. -/
theorem program_run (st : State 5 2) :
    (program.run st).1.regs 0 = (split (st.regs 0) (st.lists 0)).2 ∧
    (program.run st).1.lists 0 = [] ∧
    (program.run st).1.lists 1 = (st.lists 1).reverse ++
      (split (st.regs 0) (st.lists 0)).1 := by
  let s := setReg st 1 (st.lists 0).length
  have h := iterate_result (Nat.size (st.lists 0).length + 1) (st.lists 0) s rfl
  simp only [program, run_seq_fst, run_len_fst, run_loop_fst, run_rev_fst,
    setReg_regs, Function.update_self, setList_regs, setList_lists]
  simp only [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2]
  simp [s, Function.update, List.reverse_append]

/-- A body pass never increases its current quotient or remaining radix input size. -/
theorem body_space (st : State 5 2) :
    (body.run st).1.regs 0 ≤ st.regs 0 ∧
    listSize ((body.run st).1.lists 0) ≤ listSize (st.lists 0) := by
  cases h : st.lists 0 with
  | nil => simp [body, Stmt.run, Expr.eval, Function.update, h]
  | cons r rs =>
      obtain ⟨h0, hL, _⟩ := body_step st r rs h
      rw [h0, hL]
      exact ⟨Nat.div_le_self _ _, by simp [listSize]⟩

def passConstant : ℕ := body.C * (body.width + body.csize + 1)

/-- Scratch values are overwritten before they are read. -/
theorem body_cost (st : State 5 2) (W : ℕ)
    (h0 : Nat.size (st.regs 0) ≤ W) (hL : listSize (st.lists 0) ≤ W) :
    (body.run st).2 ≤ passConstant * (W + 1) := by
  apply loopFree_cost_le body (by decide) st W
  · intro r hr
    fin_cases r <;> simp [body, Stmt.uses, Stmt.mustW, Expr.uses] at hr
    exact h0
  · intro L hL'
    fin_cases L <;> simp [body, Stmt.lUses] at hL'
    exact hL

/-- The full decoder has polynomial charged cost in the stored input size. -/
theorem program_cost (st : State 5 2) :
    (program.run st).2 ≤ (passConstant + 12) *
      (listSize (st.lists 0) + listSize (st.lists 1) + Nat.size (st.regs 0) + 2) ^ 2 := by
  let rs := st.lists 0
  let code := st.regs 0
  let W := listSize rs + listSize (st.lists 1) + Nat.size code + 1
  let s := setReg st 1 rs.length
  have hlen : rs.length ≤ W := by
    have := length_le_listSize rs
    dsimp [W]; omega
  have hsize : Nat.size rs.length ≤ W := (size_le_self _).trans hlen
  have hcode : Nat.size code ≤ W := by dsimp [W]; omega
  have hL : listSize rs ≤ W := by dsimp [W]; omega
  have hA : listSize (st.lists 1) ≤ W := by dsimp [W]; omega
  have hi := iterate_cost_le body.run (Nat.size rs.length + 1) (passConstant * (W + 1))
    (fun v : State 5 2 => Nat.size (v.regs 0) ≤ W ∧ listSize (v.lists 0) ≤ W)
    (fun v hv => ⟨(Nat.size_le_size (body_space v).1).trans hv.1,
      (body_space v).2.trans hv.2⟩)
    (fun v hv => body_cost v W hv.1 hv.2) rs.length s ⟨hcode, hL⟩
  have hr := (iterate_result (Nat.size rs.length + 1) rs s rfl).2.2
  have hout : listSize ((iterate body.run (Nat.size rs.length + 1) rs.length s).1.lists 1) ≤
      rs.length * (Nat.size code + 1) + listSize (st.lists 1) := by
    rw [hr, listSize_append, listSize_reverse]
    exact Nat.add_le_add_right (split_listSize code rs) _
  have hiter := Nat.mul_le_mul hlen
    (show Nat.size rs.length + 1 + passConstant * (W + 1) ≤
      (passConstant + 1) * (W + 1) by nlinarith)
  have hdigits := Nat.mul_le_mul hlen (Nat.add_le_add_right hcode 1)
  simp only [program, run_seq_snd, run_len_snd, run_len_fst, run_loop_snd,
    run_loop_fst, run_rev_snd, setReg_regs, Function.update_self]
  change listSize rs + Nat.size rs.length + 1 +
    ((iterate body.run (Nat.size rs.length + 1) rs.length s).2 + Nat.size rs.length + 1 +
      (listSize ((iterate body.run (Nat.size rs.length + 1) rs.length s).1.lists 1) + 1) + 1) + 1 ≤
      (passConstant + 12) * (W + 1) ^ 2
  nlinarith

/-- Successive division removes the product of the supplied radices. -/
theorem split_quotient (code : ℕ) (rs : List ℕ) :
    (split code rs).2 = code / rs.prod := by
  induction rs generalizing code with
  | nil => simp [split]
  | cons r rs ih => simp [split, ih, Nat.div_div_eq_div_mul]

/-- Coordinate extraction agrees with the explicit prefix-product formula. -/
theorem split_getD (code : ℕ) (rs : List ℕ) (i : ℕ) (hi : i < rs.length) :
    (split code rs).1.getD i 0 = (code / (rs.take i).prod) % rs.getD i 0 := by
  induction rs generalizing code i with
  | nil => simp at hi
  | cons r rs ih =>
      cases i with
      | zero => simp [split]
      | succ i =>
          simpa [split, Nat.div_div_eq_div_mul] using ih (code / r) i (by simpa using hi)

end PCP.Lang.MixedRadixDecode
