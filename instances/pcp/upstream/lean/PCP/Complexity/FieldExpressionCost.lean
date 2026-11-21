import PCP.Complexity.FieldExpressionLang

/-!
# Charged cost of compiled field expressions

For each fixed expression, evaluation has quartic cost in the field's bit width.
The proof counts every concrete arithmetic call, stack operation, and control
step, and allows arbitrary pre-existing contents of the expression stack.
-/

namespace PCP.Lang.FieldExpression

open PCP.Algebraic BinaryField BinaryFieldCode

variable {n t : ℕ} [NeZero t]

omit [NeZero t] in
private theorem field_size (a : BinaryMaterializedField.Element t) :
    Nat.size (fieldEquiv t a).val ≤ t := Nat.size_le.mpr (fieldEquiv t a).isLt

omit [NeZero t] in
private theorem linear_le_quartic : t + 1 ≤ (t + 1) ^ 4 := by
  simpa using Nat.pow_le_pow_right (by omega : 1 ≤ t + 1) (by decide : 1 ≤ 4)

private theorem pop_cons_cost {R Q : ℕ} (st : State R Q) (L : Fin Q) (x flag : Fin R)
    (a : ℕ) (xs : List ℕ) (h : st.lists L = a :: xs) :
    ((Stmt.pop L x flag).run st).2 = Nat.size a + 1 := by simp [Stmt.run, h]

theorem binaryStep_cost (op : Op) (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st)
    (a b : BinaryMaterializedField.Element t) (tail : List ℕ)
    (hs : st.lists 11 = (fieldEquiv t b).val :: (fieldEquiv t a).val :: tail) :
    ((binaryStep op).run st).2 ≤ 20000010 * (t + 1) ^ 4 := by
  let s := setReg (setReg (setList st 11 ((fieldEquiv t a).val :: tail))
    (slot n 25) (fieldEquiv t b).val) (slot n 35) 1
  let u := setReg (setReg (setList s 11 tail) (slot n 24) (fieldEquiv t a).val) (slot n 35) 1
  have hvs : View t env s := ((hv.setStack _).setReg 25 _ (by decide)).setReg 35 _ (by decide)
  have hvu : View t env u := ((hvs.setStack _).setReg 24 _ (by decide)).setReg 35 _ (by decide)
  have hu24 : u.regs (slot n 24) = (fieldEquiv t a).val := by simp [u, slot, Function.update]
  have hu25 : u.regs (slot n 25) = (fieldEquiv t b).val := by simp [u, s, slot, Function.update]
  have hcost := binary_cost op (Nat.pos_of_ne_zero (NeZero.ne t))
    (u.restrict (slot n) Fin.castSucc) (fieldEquiv t a) (fieldEquiv t b)
    hvu.2.1 hu24 hu25 hvu.2.2.1 hvu.2.2.2
  have hrcost := congrArg Prod.snd (embed_result (binary op) u)
  rw [← hrcost] at hcost
  have hout := binary_run_field op (u.restrict (slot n) Fin.castSucc) a b hvu.2.1
    hu24 hu25 hvu.2.2.1 hvu.2.2.2
  have hr := congrArg (fun z : State 36 11 × ℕ => z.1.regs 26) (embed_result (binary op) u)
  have hcode : ((embed (binary op)).run u).1.regs (slot n 26) =
      (fieldEquiv t (op.fieldEval a b)).val := hr.trans hout
  have hfirst : ((Stmt.pop 11 (slot n 25) (slot n 35)).run st).1 = s := by
    simp [Stmt.run, hs, s]
  have hsecond : ((Stmt.pop 11 (slot n 24) (slot n 35)).run s).1 = u := by
    simp [Stmt.run, s, u]
  simp only [binaryStep, run_seq_snd, hfirst, hsecond, run_push_snd, hcode]
  rw [pop_cons_cost st _ _ _ _ _ hs, pop_cons_cost s _ _ _ (fieldEquiv t a).val tail (by simp [s])]
  have ha := field_size a
  have hb := field_size b
  have ho := field_size (op.fieldEval a b)
  have hlin := linear_le_quartic (t := t)
  omega

theorem inverseStep_cost (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st)
    (a : BinaryMaterializedField.Element t) (tail : List ℕ)
    (hs : st.lists 11 = (fieldEquiv t a).val :: tail) :
    (inverseStep.run st).2 ≤ 20000010 * (t + 1) ^ 4 := by
  let u := setReg (setReg (setList st 11 tail) (slot n 24) (fieldEquiv t a).val) (slot n 35) 1
  have hvu : View t env u := ((hv.setStack _).setReg 24 _ (by decide)).setReg 35 _ (by decide)
  have hu24 : u.regs (slot n 24) = (fieldEquiv t a).val := by simp [u, slot, Function.update]
  have hcost := inverse_cost (u.restrict (slot n) Fin.castSucc) (fieldEquiv t a)
    hvu.2.1 hu24 hvu.2.2.1 hvu.2.2.2
  have hrcost := congrArg Prod.snd (embed_result inverse u)
  rw [← hrcost] at hcost
  have hout := inverse_run_field (u.restrict (slot n) Fin.castSucc) a hvu.2.1
    hu24 hvu.2.2.1 hvu.2.2.2
  have hr := congrArg (fun z : State 36 11 × ℕ => z.1.regs 26) (embed_result inverse u)
  have hcode : ((embed inverse).run u).1.regs (slot n 26) =
      (fieldEquiv t a⁻¹).val := hr.trans hout
  have hfirst : ((Stmt.pop 11 (slot n 24) (slot n 35)).run st).1 = u := by
    simp [Stmt.run, hs, u]
  simp only [inverseStep, run_seq_snd, hfirst, run_push_snd, hcode]
  rw [pop_cons_cost st _ _ _ _ _ hs]
  have ha := field_size a
  have ho := field_size a⁻¹
  have hlin := linear_le_quartic (t := t)
  omega

/-- A finite syntactic coefficient accounts for every arithmetic and stack call. -/
def Term.weight : Term n → ℕ
  | .bit _ => 6
  | .input _ => 1
  | .bin _ a b => a.weight + b.weight + 20000012
  | .inv a => a.weight + 20000011

/-- Fixed expression evaluation is polynomial in the encoded field width. -/
theorem compile_cost (a : Term n) (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st) :
    ((compile a).run st).2 ≤ a.weight * (t + 1) ^ 4 := by
  induction a generalizing st with
  | bit b =>
      have hp : 1 ≤ (t + 1) ^ 4 := one_le_pow₀ (by omega)
      cases b <;> simp [compile, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
        Term.weight, Function.update, show Nat.size 1 = 1 from rfl] <;> omega
  | input i =>
      have hs := field_size (env i)
      have hlin := linear_le_quartic (t := t)
      simp only [compile, run_push_snd, Term.weight, one_mul, hv.1 i]
      omega
  | bin op a b iha ihb =>
      obtain ⟨ha, hva⟩ := compile_spec a st env hv
      obtain ⟨hb, hvb⟩ := compile_spec b ((compile a).run st).1 env hva
      have hc1 := iha st hv
      have hc2 := ihb ((compile a).run st).1 hva
      have hc3 := binaryStep_cost op _ env hvb (a.eval env) (b.eval env) (st.lists 11)
        (by rw [hb, ha])
      have hp : 1 ≤ (t + 1) ^ 4 := one_le_pow₀ (by omega)
      simp only [compile, run_seq_snd, Term.weight]
      nlinarith
  | inv a ih =>
      obtain ⟨ha, hva⟩ := compile_spec a st env hv
      have hc1 := ih st hv
      have hc2 := inverseStep_cost _ env hva (a.eval env) (st.lists 11) ha
      have hp : 1 ≤ (t + 1) ^ 4 := one_le_pow₀ (by omega)
      simp only [compile, run_seq_snd, Term.weight]
      nlinarith

/-- The result-pop overhead preserves the same quartic degree. -/
theorem scalar_cost (a : Term n) (st : State (n + 36) 12)
    (env : Fin n → BinaryMaterializedField.Element t) (hv : View t env st) :
    ((scalar a).run st).2 ≤ (a.weight + 2) * (t + 1) ^ 4 := by
  obtain ⟨ha, _⟩ := compile_spec a st env hv
  have hc := compile_cost a st env hv
  have hsize := field_size (a.eval env)
  have hlin := linear_le_quartic (t := t)
  have hp : 1 ≤ (t + 1) ^ 4 := one_le_pow₀ (by omega)
  rw [scalar, run_seq_snd, pop_cons_cost _ _ _ _ _ _ ha]
  nlinarith

end PCP.Lang.FieldExpression
