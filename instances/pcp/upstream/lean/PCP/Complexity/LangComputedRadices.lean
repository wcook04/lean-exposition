import PCP.Complexity.ArithmeticExpressionCost
import PCP.Complexity.LangPowerTwo

/-!
# Computing a fixed family of binary structural radices
-/

namespace PCP.Lang.ComputedRadices

open ArithmeticExpression

variable (terms : Fin 7 → Term 4)

def compute (i : Fin 7) : Stmt 15 2 :=
  (scalar (terms i)).rename (Fin.castLE (by decide)) id

def power : Stmt 15 2 := PowerTwo.program.rename (Fin.natAdd 7) id

def emit (i : Fin 7) : Stmt 15 2 := .seq (compute terms i)
  (.seq (.assign 9 (.var 4)) (.seq power (.push 0 12)))

def emitAll (terms : Fin 7 → Term 4) : List (Fin 7) → Stmt 15 2
  | [] => .skip
  | i :: is => .seq (emit terms i) (emitAll terms is)

@[irreducible] def program : Stmt 15 2 := .seq (emitAll terms (List.finRange 7)) (.rev 0)

def Context (n m c t : ℕ) (st : State 15 2) : Prop :=
  ∀ i : Fin 4, st.regs (i.castAdd 11) = ![n, m, c, t] i

theorem compute_result (i : Fin 7) (st : State 15 2) :
    ((compute terms i).run st).1.restrict (Fin.castLE (by decide)) id =
      ((scalar (terms i)).run (st.restrict (Fin.castLE (by decide)) id)).1 := by
  unfold compute
  exact congrArg Prod.fst ((scalar (terms i)).run_rename _ _
    (Fin.castLE_injective _) Function.injective_id st)

theorem compute_run (i : Fin 7) (n m c t : ℕ) (st : State 15 2)
    (hc : Context n m c t st) :
    ((compute terms i).run st).1.regs 4 = (terms i).eval ![n, m, c, t] ∧
    Context n m c t ((compute terms i).run st).1 ∧
    ((compute terms i).run st).1.lists 0 = st.lists 0 ∧
    ((compute terms i).run st).1.lists 1 = st.lists 1 := by
  have h := scalar_spec (terms i) (st.restrict (Fin.castLE (by decide)) id)
  rw [← compute_result terms i st] at h
  have hin : (fun j : Fin 4 => (st.restrict (Fin.castLE (by decide)) id).regs
      (j.castAdd 3)) = ![n, m, c, t] := funext hc
  rw [hin] at h
  refine ⟨h.1, ?_, ?_, h.2⟩
  · intro j
    have hj := scalar_preserves_input (terms i) j
      (st.restrict (Fin.castLE (by decide)) id)
    rw [← compute_result terms i st] at hj
    exact hj.trans (hc j)
  · have h0 := scalar_preserves_source (terms i)
      (st.restrict (Fin.castLE (by decide)) id)
    rw [← compute_result terms i st] at h0
    exact h0

theorem power_run (st : State 15 2) : (power.run st).1.regs 12 = 2 ^ st.regs 9 := by
  have h := PowerTwo.program_run (st.restrict (Fin.natAdd 7) id)
  have hr := PowerTwo.program.run_rename (Fin.natAdd 7) id
    (Fin.natAdd_injective _ _) Function.injective_id st
  rw [← hr] at h
  exact h

theorem power_reg (i : Fin 15) (hi : i.val < 7) (st : State 15 2) :
    (power.run st).1.regs i = st.regs i := by
  unfold power
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_natAdd] at this
  omega

theorem power_lists (L : Fin 2) (st : State 15 2) :
    (power.run st).1.lists L = st.lists L := by
  exact run_lists_frame power L
    (by simp [power, PowerTwo.program, BinaryPolynomialCoefficient.powerBody, Stmt.listWrites]) st

theorem emit_run (i : Fin 7) (n m c t : ℕ) (st : State 15 2)
    (hc : Context n m c t st) :
    ((emit terms i).run st).1.lists 0 = 2 ^ (terms i).eval ![n, m, c, t] :: st.lists 0 ∧
    Context n m c t ((emit terms i).run st).1 ∧
    ((emit terms i).run st).1.lists 1 = st.lists 1 := by
  have h := compute_run terms i n m c t st hc
  generalize hu : ((compute terms i).run st).1 = u at *
  let s := setReg u 9 (u.regs 4)
  have hp := power_run s
  have hp0 := power_lists 0 s
  have hp1 := power_lists 1 s
  have hpr (j : Fin 4) : (power.run s).1.regs (j.castAdd 11) = u.regs (j.castAdd 11) := by
    rw [power_reg _ (by simp only [Fin.val_castAdd]; omega)]
    have hj : j.castAdd 11 ≠ (9 : Fin 15) := by
      intro hh; have := congrArg Fin.val hh; simp only [Fin.val_castAdd] at this
      norm_num at this
      omega
    simp [s, hj]
  simp only [emit, run_seq_fst, hu, run_assign_fst, Expr.eval, run_push_fst]
  change (setList (power.run s).1 0 ((power.run s).1.regs 12 ::
    (power.run s).1.lists 0)).lists 0 = _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [setList_lists, Function.update_self, hp, hp0]
    simp only [s, setReg_regs, Function.update_self, setReg_lists, h.1, h.2.2.1]
  · intro j
    exact (hpr j).trans (h.2.1 j)
  · simpa [hp1, s, Function.update] using h.2.2.2

theorem emitAll_run (is : List (Fin 7)) (n m c t : ℕ) (st : State 15 2)
    (hc : Context n m c t st) :
    ((emitAll terms is).run st).1.lists 0 =
      (is.map (fun i => 2 ^ (terms i).eval ![n, m, c, t])).reverse ++ st.lists 0 ∧
    Context n m c t ((emitAll terms is).run st).1 ∧
    ((emitAll terms is).run st).1.lists 1 = st.lists 1 := by
  induction is generalizing st with
  | nil => simpa [emitAll, Stmt.run] using
      (show Context n m c t st ∧ st.lists 1 = st.lists 1 from ⟨hc, rfl⟩)
  | cons i is ih =>
      have h := emit_run terms i n m c t st hc
      have hi := ih ((emit terms i).run st).1 h.2.1
      simp only [emitAll, run_seq_fst]
      refine ⟨?_, hi.2.1, hi.2.2.trans h.2.2⟩
      rw [hi.1, h.1]
      simp [List.reverse_cons, List.append_assoc]

theorem program_run (n m c t : ℕ) (st : State 15 2)
    (hc : Context n m c t st) (he : st.lists 0 = []) :
    ((program terms).run st).1.lists 0 = List.ofFn (fun i => 2 ^ (terms i).eval ![n, m, c, t]) ∧
    Context n m c t ((program terms).run st).1 ∧
    ((program terms).run st).1.lists 1 = st.lists 1 := by
  have h := emitAll_run terms (List.finRange 7) n m c t st hc
  generalize hu : ((emitAll terms (List.finRange 7)).run st).1 = u at *
  simp only [program, run_seq_fst, hu, run_rev_fst]
  refine ⟨?_, h.2.1, ?_⟩
  · simp [h.1, he, ← List.ofFn_eq_map]
  · simpa [Function.update] using h.2.2

end PCP.Lang.ComputedRadices
