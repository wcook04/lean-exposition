import PCP.Complexity.BinaryGeneratorPredicate

/-! # Charged polynomial cost of the bounded generator predicate -/

namespace PCP.Lang.BinaryGeneratorPredicate

open PCP.Algebraic BinaryField BinaryFieldCode BooleanLoops

variable {t : ℕ} [NeZero t]

theorem tail_cost (st : State 36 11) (hs : Nat.size (st.regs 26) ≤ t)
    (hg : st.regs 29 < 2) : (tail.run st).2 ≤ 30 * (t+1)^2 := by
  have hg' : st.regs 29 = 0 ∨ st.regs 29 = 1 := by omega
  rcases hg' with hg' | hg' <;>
    by_cases h : st.regs 26 = 1 <;>
    simp [tail, Stmt.run, Expr.eval, Expr.cost, Expr.readSize, Function.update, h, hg'] <;>
    nlinarith [Nat.zero_le t]

theorem body_cost (a : Field t) (n : ℕ) (st : State 36 11) (hc : Context a st)
    (hp : st.regs 25 = (fieldEquiv t (a ^ n)).val)
    (hg : st.regs 29 = truth (GoodPrefix a n)) :
    (body.run st).2 ≤ 21000000 * (t+1)^4 := by
  have hm := binary_run_field .mul st a (a^n) hc.1 hc.2.1 hp hc.2.2.1 hc.2.2.2
  have hmc := binary_cost .mul (NeZero.pos t) st (fieldEquiv t a) (fieldEquiv t (a^n))
    hc.1 hc.2.1 hp hc.2.2.1 hc.2.2.2
  have hf := run_regs_frame (binary .mul) 29 (by decide) st
  have htail := tail_cost (t := t) (binary .mul |>.run st).1
    (by rw [hm]; exact Nat.size_le.mpr (Fin.isLt _))
    (by rw [hf, hg]; exact truth_lt_two _)
  have hpow : (t+1)^2 ≤ (t+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 1 ≤ (t+1)^4 := Nat.one_le_pow _ _ (by omega)
  rw [body, run_seq_snd]
  nlinarith



omit [NeZero t] in
theorem finish_cost (st : State 36 11) (hs : Nat.size (st.regs 24) ≤ t)
    (hg : st.regs 29 < 2) : (finish.run st).2 ≤ 30 * (t+1)^2 := by
  have hg' : st.regs 29 = 0 ∨ st.regs 29 = 1 := by omega
  rcases hg' with hg' | hg' <;>
    by_cases h : st.regs 24 = 0 <;>
    simp [finish, Stmt.run, Expr.eval, Expr.cost, Expr.readSize, Function.update, h, hg'] <;>
    nlinarith [Nat.zero_le t]

omit [NeZero t] in
theorem prepare_cost (st : State 36 11) (q : ℕ)
    (ha : Nat.size (st.regs 33) ≤ q) (hq : st.regs 28 = q) :
    (prepare.run st).2 ≤ 30 * (q+4)^2 := by
  have hsize := size_le_self q
  have hsub := size_le_self (q-2)
  simp [prepare, Stmt.run, Expr.eval, Expr.cost, Expr.readSize, Function.update, hq]
  rw [show Nat.size 2 = 2 from rfl]
  nlinarith [Nat.sub_le q 2]

theorem program_cost (a : Field t) (st : State 36 11)
    (ht : st.regs 20 = t) (ha : st.regs 33 = (fieldEquiv t a).val)
    (hq : st.regs 28 = 2 ^ t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (program.run st).2 ≤ 50000000 * (2 ^ t + 4)^5 := by
  let q := 2 ^ t
  have htq : t ≤ q := (Nat.lt_two_pow_self).le
  have has : Nat.size (st.regs 33) ≤ t := by rw [ha]; exact Nat.size_le.mpr (Fin.isLt _)
  have hprep := prepare_cost st q (has.trans htq) hq
  let s := (prepare.run st).1
  have hs : Context a s ∧ s.regs 25 = (fieldEquiv t (a^0)).val ∧
      s.regs 29 = truth (GoodPrefix a 0) := by
    rw [pow_zero, fieldCode_one]
    simp [s, prepare, Stmt.run, Expr.eval, Function.update, Context, ht, ha, hm, he, truth]
  have hs30 : s.regs 30 = q - 2 := by
    simp [s, prepare, Stmt.run, Expr.eval, Function.update, hq, q]
  let Inv := fun n u => Context a u ∧ u.regs 25 = (fieldEquiv t (a^n)).val ∧
      u.regs 29 = truth (GoodPrefix a n)
  have hstep (n : ℕ) (u : State 36 11) (hu : Inv n u) :
      Inv (n+1) (body.run u).1 :=
    ⟨body_context a u hu.1, body_step a n u hu.1 hu.2.1 hu.2.2⟩
  have hit := iterate_cost_idx body.run (Nat.size (q-2)+1) (21000000*(t+1)^4) (q-2)
    Inv (fun n u _ hu => ⟨hstep n u hu, body_cost a n u hu.1 hu.2.1 hu.2.2⟩) s hs
  have hout := iterate_inv body.run (Nat.size (q-2)+1) (q-2) Inv
    (fun n u _ hu => hstep n u hu) s hs
  have hfinish := finish_cost (t := t)
    (iterate body.run (Nat.size (q-2)+1) (q-2) s).1
    (by rw [hout.1.2.1]; exact Nat.size_le.mpr (Fin.isLt _))
    (by rw [hout.2.2]; exact truth_lt_two _)
  have hsize : Nat.size (q-2) ≤ q := (size_le_self _).trans (Nat.sub_le _ _)
  have hsmall : (t+1)^4 ≤ (q+4)^4 := Nat.pow_le_pow_left (by omega) _
  have hiter : (iterate body.run (Nat.size (q-2)+1) (q-2) s).2 ≤
      (q+4) * ((q+4) + 21000000*(q+4)^4) := hit.trans
    (Nat.mul_le_mul (by omega) (by nlinarith only [hsize, hsmall]))
  have hfinish' := hfinish.trans (Nat.mul_le_mul_left 30
    (Nat.pow_le_pow_left (by omega : t+1 ≤ q+4) 2))
  have hpow : (q+4)^2 ≤ (q+4)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hlow : q+4 ≤ (q+4)^5 := Nat.le_pow (by decide)
  simp only [program, run_seq_snd, run_seq_fst, run_loop_snd, run_loop_fst]
  change (prepare.run st).2 +
    ((iterate body.run (Nat.size (s.regs 30)+1) (s.regs 30) s).2 +
      Nat.size (s.regs 30)+1 +
      (finish.run (iterate body.run (Nat.size (s.regs 30)+1) (s.regs 30) s).1).2 + 1) + 1 ≤ _
  rw [hs30]
  change _ ≤ 50000000*(q+4)^5
  nlinarith only [hprep, hiter, hfinish', hpow, hlow, hsize]

end PCP.Lang.BinaryGeneratorPredicate
