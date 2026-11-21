import PCP.Complexity.AmplifiedEncode

/-! Polynomial charged cost for producing the public next-query or halt code. -/

namespace PCP.Lang.AmplifiedStream

theorem budget_cost (cs : List ℕ) (st : State 420 140) :
    ((budget cs).run st).2 ≤ (PolynomialBudget.costConstant cs+6)*(Nat.size (st.regs 414)+1) := by
  let s := (budgetSetup.run st).1
  have hr := (PolynomialBudget.code cs).run_rename_cost budgetR budgetQ
    (by decide) (by decide) s
  have hp := PolynomialBudget.code_cost_le cs (s.restrict budgetR budgetQ)
  rw [← hr] at hp
  have hs : (budgetSetup.run st).2 = 2*Nat.size (st.regs 414)+5 := by
    simp [budgetSetup, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]
    omega
  have hi : Nat.size ((s.restrict budgetR budgetQ).regs 0) +
      Nat.size ((s.restrict budgetR budgetQ).regs 1) +
      Nat.size ((s.restrict budgetR budgetQ).regs 2)+1 = Nat.size (st.regs 414)+1 := by
    simp [s, budgetSetup, Stmt.run, Expr.eval, Function.update, budgetR]
  rw [hi] at hp
  change (budgetSetup.run st).2+((PolynomialBudget.code cs).rename budgetR budgetQ |>.run s).2+1 ≤ _
  rw [hs]
  nlinarith

theorem emit_cost (st : State 420 140) (C : ℕ) (ho : Output st C)
    (hb : C ≤ st.regs 411) (he : st.lists 139 = []) :
    (emit.run st).2 ≤ (BinaryEncode.passConstant+25)*(2*st.regs 411+3)^2 := by
  let s := setList st 1 []
  have hsreg : s.regs = st.regs := rfl
  have htag : Nat.size (st.regs 402) ≤ 1 := size_le_one_of_le_one ho.tag
  have hp : 1 ≤ (2*st.regs 411+3)^2 := one_le_pow₀ (by omega)
  simp only [emit, run_seq_snd, run_copy_snd, run_copy_fst, he]
  change 0+1+((Stmt.ite 402 (AnswerEncode.query.rename emitR emitQ)
    (AnswerEncode.halt.rename emitR emitQ)).run s).2+1 ≤ _
  by_cases ht : st.regs 402 = 0
  · have hbool : st.regs 403 = (decide (st.regs 403 ≠ 0)).toNat := by
      have h := ho.halt ht
      interval_cases hval : st.regs 403 <;> simp
    have h := AnswerEncode.halt_cost (s.restrict emitR emitQ)
      (decide (st.regs 403 ≠ 0)) hbool
    rw [← AnswerEncode.halt.run_rename_cost emitR emitQ (by decide) (by decide) s] at h
    simp only [Stmt.run, hsreg, ht, ne_eq, not_true_eq_false, ↓reduceIte, Nat.size_zero]
    change 0+1+(((AnswerEncode.halt.rename emitR emitQ).run s).2+0+1)+1 ≤ _
    nlinarith
  · have h := AnswerEncode.query_cost (s.restrict emitR emitQ) ((ho.query ht).trans hb)
    rw [← AnswerEncode.query.run_rename_cost emitR emitQ (by decide) (by decide) s] at h
    change ((AnswerEncode.query.rename emitR emitQ).run s).2 ≤
      (BinaryEncode.passConstant+20)*(st.regs 411+Nat.size (st.regs 403)+0+3)^2 at h
    have h' : ((AnswerEncode.query.rename emitR emitQ).run s).2 ≤
        (BinaryEncode.passConstant+20)*(2*st.regs 411+3)^2 := h.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := ho.query ht; omega) 2))
    simp only [Stmt.run, hsreg, ht, ne_eq, not_false_eq_true, ↓reduceIte]
    change 0+1+(((AnswerEncode.query.rename emitR emitQ).run s).2+
      Nat.size (st.regs 402)+1)+1 ≤ _
    nlinarith

theorem encode_cost (cs : List ℕ) (st : State 420 140) (C : ℕ) (ho : Output st C)
    (hb : C ≤ PolynomialBudget.value cs (st.regs 414)) (he : st.lists 139 = []) :
    ((encode cs).run st).2 ≤
      (PolynomialBudget.costConstant cs+6)*(Nat.size (st.regs 414)+1)+
        (BinaryEncode.passConstant+25)*(2*PolynomialBudget.value cs (st.regs 414)+3)^2+1 := by
  have he' : ((budget cs).run st).1.lists 139 = [] := (budget_lists cs st 139).trans he
  have hb' : C ≤ ((budget cs).run st).1.regs 411 := by rwa [budget_run]
  have h := emit_cost ((budget cs).run st).1 C (budget_output cs st C ho) hb' he'
  rw [budget_run] at h
  rw [encode, run_seq_snd]
  exact Nat.add_le_add_right (Nat.add_le_add (budget_cost cs st) h) 1

end PCP.Lang.AmplifiedStream
