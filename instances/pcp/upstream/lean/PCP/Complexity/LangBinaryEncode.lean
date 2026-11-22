import PCP.Complexity.LangCost
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Canonical binary output from a bounded materialized loop

The supplied iteration budget bounds the input's bit length. Halving and
remainder instructions emit only while the current value is nonzero, so the
output has no high zero digits and is exactly `Nat.bits`, including at zero.
-/

namespace PCP.Lang.BinaryEncode

/-- Numeric digits in the public little-endian binary convention. -/
def digits (n : ℕ) : List ℕ := n.bits.map Bool.toNat

@[simp] theorem digits_zero : digits 0 = [] := rfl

/-- Exact first-digit recursion, excluding the canonical empty zero word. -/
theorem digits_cons (n : ℕ) (hn : n ≠ 0) : digits n = n % 2 :: digits (n / 2) := by
  have hb : n.div2 = 0 → n.bodd = true := by
    intro hq
    cases ho : n.bodd
    · have he := Nat.bit_bodd_div2 n
      rw [ho, hq] at he
      exact (hn he.symm).elim
    · rfl
  have h := Nat.bits_append_bit n.div2 n.bodd hb
  rw [Nat.bit_bodd_div2] at h
  simp [digits, h, Nat.mod_two_of_bodd, Nat.div2_val]

/-- Each bit contributes at most two symbols to the natural-list encoding. -/
theorem digits_listSize (n : ℕ) : listSize (digits n) ≤ 2 * Nat.size n := by
  unfold listSize digits
  rw [List.map_map]
  have h := List.sum_le_sum (l := n.bits)
    (f := fun b => Nat.size b.toNat + 1) (g := fun _ => 2)
    (fun b _ => by cases b <;> decide)
  simpa [Function.comp_def, Nat.size_eq_bits_len, Nat.mul_comm] using h

/-- Register zero holds the decreasing value and register two holds the radix two. -/
def body : Stmt 4 1 := .ite 0
  (.seq (.assign 3 (.mod 0 2)) (.seq (.assign 0 (.div 0 2)) (.push 0 3))) .skip

/-- Register one is an explicit upper bound on the input bit length. -/
def program : Stmt 4 1 :=
  .seq (.assign 2 (.const 2)) (.seq (.loop 1 body) (.rev 0))

theorem body_step (st : State 4 1) (h2 : st.regs 2 = 2) :
    (body.run st).1.regs 0 = st.regs 0 / 2 ∧
    (body.run st).1.regs 2 = 2 ∧
    (body.run st).1.lists 0 =
      (if st.regs 0 = 0 then st.lists 0 else st.regs 0 % 2 :: st.lists 0) := by
  by_cases h0 : st.regs 0 = 0 <;>
    simp [body, Stmt.run, Expr.eval, Function.update, h2, h0]

/-- Sufficiently many iterations emit exactly the canonical word and exhaust the value. -/
theorem iterate_result (c k : ℕ) (st : State 4 1) (h2 : st.regs 2 = 2)
    (hk : Nat.size (st.regs 0) ≤ k) :
    (iterate body.run c k st).1.regs 0 = 0 ∧
    (iterate body.run c k st).1.lists 0 = (digits (st.regs 0)).reverse ++ st.lists 0 := by
  induction k generalizing st with
  | zero =>
      have hz : st.regs 0 = 0 := Nat.size_eq_zero.mp (by omega)
      simp [iterate, hz]
  | succ k ih =>
      obtain ⟨h0, h2', hL⟩ := body_step st h2
      have hsmall : Nat.size ((body.run st).1.regs 0) ≤ k := by
        rw [h0, Nat.size_le]
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
        simpa only [pow_succ] using Nat.size_le.mp hk
      obtain ⟨hz, hD⟩ := ih (body.run st).1 h2' hsmall
      rw [iterate_succ_fst]
      refine ⟨hz, ?_⟩
      rw [hD, h0, hL]
      by_cases hzero : st.regs 0 = 0
      · simp [hzero]
      · rw [ite_eq_right hzero, digits_cons _ hzero]
        simp [List.reverse_cons, List.append_assoc]

/-- The output accumulator is restored to forward order, followed by the canonical binary digits. -/
theorem program_run (st : State 4 1) (h : Nat.size (st.regs 0) ≤ st.regs 1) :
    (program.run st).1.regs 0 = 0 ∧
    (program.run st).1.lists 0 = (st.lists 0).reverse ++ digits (st.regs 0) := by
  let s := setReg st 2 2
  have hi := iterate_result (Nat.size (st.regs 1) + 1) (st.regs 1) s rfl h
  simp only [program, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    run_rev_fst, setReg_regs, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
    setList_regs, setList_lists, Function.update_self]
  refine ⟨hi.1, ?_⟩
  rw [hi.2]
  simp [s, Function.update, List.reverse_append]

def passConstant : ℕ := body.C * (body.width + body.csize + 1)

/-- A loop pass has linear charged cost and retains a bounded decreasing value. -/
theorem body_cost (st : State 4 1) (W : ℕ) (h0 : Nat.size (st.regs 0) ≤ W)
    (h2 : Nat.size (st.regs 2) ≤ W) : (body.run st).2 ≤ passConstant * (W + 1) := by
  apply loopFree_cost_le body (by decide) st W
  · intro r hr
    fin_cases r <;> simp [body, Stmt.uses, Stmt.mustW, Expr.uses] at hr <;> assumption
  · intro L hL
    simp [body, Stmt.lUses] at hL

/-- Runtime is polynomial in the explicit bit budget and the encoded input sizes. -/
theorem program_cost (st : State 4 1) (h : Nat.size (st.regs 0) ≤ st.regs 1) :
    (program.run st).2 ≤ (passConstant + 10) *
      (st.regs 1 + Nat.size (st.regs 0) + listSize (st.lists 0) + 3) ^ 2 := by
  let k := st.regs 1
  let code := st.regs 0
  let W := k + Nat.size code + listSize (st.lists 0) + 2
  let s := setReg st 2 2
  have hk : k ≤ W := by dsimp [W]; omega
  have hcode : Nat.size code ≤ W := by dsimp [W]; omega
  have hA : listSize (st.lists 0) ≤ W := by dsimp [W]; omega
  have htwo : Nat.size 2 ≤ W := by change 2 ≤ W; dsimp [W]; omega
  have hsk : Nat.size k ≤ W := (size_le_self k).trans hk
  have hi := iterate_cost_le body.run (Nat.size k + 1) (passConstant * (W + 1))
    (fun v : State 4 1 => Nat.size (v.regs 0) ≤ W ∧ v.regs 2 = 2)
    (fun v hv => by
      obtain ⟨h0, h2, _⟩ := body_step v hv.2
      exact ⟨by rw [h0]; exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hv.1, h2⟩)
    (fun v hv => body_cost v W hv.1 (by rw [hv.2]; exact htwo)) k s ⟨hcode, rfl⟩
  have hr := (iterate_result (Nat.size k + 1) k s rfl h).2
  have hout : listSize ((iterate body.run (Nat.size k + 1) k s).1.lists 0) ≤
      2 * Nat.size code + listSize (st.lists 0) := by
    rw [hr, listSize_append, listSize_reverse]
    exact Nat.add_le_add_right (digits_listSize code) _
  have hiter := Nat.mul_le_mul hk
    (show Nat.size k + 1 + passConstant * (W + 1) ≤
      (passConstant + 1) * (W + 1) by nlinarith)
  have hsizeTwo : Nat.size 2 = 2 := Nat.size_pow (n := 1)
  have hsetup : ((Stmt.assign 2 (.const 2) : Stmt 4 1).run st).2 = 5 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, hsizeTwo]
  simp only [program, run_seq_snd, hsetup, run_assign_fst, Expr.eval,
    run_loop_snd, run_loop_fst, run_rev_snd,
    setReg_regs, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
  change 5 + ((iterate body.run (Nat.size k + 1) k s).2 + Nat.size k + 1 +
      (listSize ((iterate body.run (Nat.size k + 1) k s).1.lists 0) + 1) + 1) + 1 ≤
      (passConstant + 10) * (W + 1) ^ 2
  nlinarith

end PCP.Lang.BinaryEncode
