import PCP.Complexity.LangDifferenceQueries

/-!
# Charged polynomial cost of actual difference-query construction
-/

namespace PCP.Lang.DifferenceQueries

open PCP.Algebraic BinaryPolynomialSpace

variable {t : ℕ}

def finish : Stmt 80 32 := .seq emit (.rev 24)

def finishConstant : ℕ := finish.C * (finish.width + finish.csize + 1)

theorem homogeneous_cost (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hd : st.regs 56 = 3) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (homogeneous.run st).2 ≤ (BooleanLabelTransform.queryConstant + 200) * (2 ^ t + 7) ^ 8 := by
  have hc := BooleanLabelConstructors.homogeneous_cost w
    (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ht hd he hw
  rw [← homogeneous_result st] at hc
  simpa only [show Nat.size 3 = 2 from rfl, Nat.add_assoc] using hc

theorem pack_cost {r : ℕ} (p : Coefficients t r) (st : State 80 32)
    (hp : st.lists 5 = BooleanCoefficientList.encode p) :
    (pack.run st).2 ≤ (WordCodec.passConstant * 3 + 30) * (2 ^ t + 1) ^ 2 := by
  let s := setList st 0 (st.lists 5)
  have hc := HadamardLabel.decode_cost p s (by simpa [s] using hp)
  have ho := HadamardLabel.decode_run p s (by simpa [s] using hp)
  dsimp only [s] at hc ho
  simp only [pack, run_seq_snd, run_copy_snd, run_copy_fst]
  generalize hu : (HadamardLabel.decode.run (setList st 0 (st.lists 5))).1 = u at *
  change listSize (st.lists 5) + 1 +
    ((HadamardLabel.decode.run (setList st 0 (st.lists 5))).2 +
      (Expr.var 1).cost u.regs + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, ho]
  rw [hp] at hc ⊢
  have he := HadamardLabel.encode_size p
  have hs := HadamardLabel.code_size p
  nlinarith [Nat.zero_le ((2 ^ t) ^ 2)]

theorem finish_uses (i : Fin 80) (hi : i ∈ finish.uses) : 57 ≤ i.val ∧ i.val ≤ 63 := by
  have h : ∀ j : Fin 80, j ∈ finish.uses → 57 ≤ j.val ∧ j.val ≤ 63 := by decide
  exact h i hi

theorem finish_lUses (L : Fin 32) (hL : L ∈ finish.lUses) : L = 24 := by
  have h : ∀ K : Fin 32, K ∈ finish.lUses → K = 24 := by decide
  exact h L hL

theorem finish_cost (st : State 80 32) (W : ℕ)
    (hr : ∀ i : Fin 80, 57 ≤ i.val → i.val ≤ 63 → Nat.size (st.regs i) ≤ W)
    (he : st.lists 24 = []) : (finish.run st).2 ≤ finishConstant * (W + 1) := by
  apply loopFree_cost_le finish (by decide) st W
  · intro i hi
    exact hr i (finish_uses i hi).1 (finish_uses i hi).2
  · intro L hL
    rw [finish_lUses L hL, he]
    simp [listSize]

/-- Input point/cardinality bit lengths and field cardinality bound the complete query program. -/
theorem program_cost (w : Fin t → ZMod 2) (st : State 80 32) (W : ℕ)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val))
    (hr : ∀ i : Fin 80, 57 ≤ i.val → i.val ≤ 62 → Nat.size (st.regs i) ≤ W) :
    (program.run st).2 ≤
      (BooleanLabelTransform.queryConstant + WordCodec.passConstant * 3 + finishConstant + 250) *
        (2 ^ t + W + 8) ^ 8 := by
  have hq0 := Nat.zero_le (2 ^ t)
  have hW0 := Nat.zero_le W
  let s := setReg (setList st 24 []) 56 3
  have hs20 : s.regs 20 = t := by simpa [s, Function.update] using ht
  have hs56 : s.regs 56 = 3 := by simp [s]
  have hs7 : s.lists 7 = [] := by simpa [s, Function.update] using he
  have hs17 : s.lists 17 = List.ofFn (fun i => (w i).val) := by
    simpa [s, Function.update] using hw
  have hh := homogeneous_run w s hs20 hs56 hs7 hs17
  have hc := homogeneous_cost w s hs20 hs56 hs7 hs17
  have hreg (i : Fin 80) (hi : 57 ≤ i.val) :
      (homogeneous.run s).1.regs i = st.regs i := by
    have hne : i ≠ 56 := by intro h; subst i; norm_num at hi
    simpa [s, hne] using homogeneous_reg i hi s
  have hlist : (homogeneous.run s).1.lists 24 = [] := by
    simpa [s] using homogeneous_list 24 (by decide) s
  generalize hu : (homogeneous.run s).1 = u at *
  let p := BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 3) w
  have hp := pack_run p u hh
  have hpc := pack_cost p u hh
  have hpl := (pack_list u).trans hlist
  have hpr (i : Fin 80) (hi : 57 ≤ i.val) (hi' : i.val ≤ 62) :
      (pack.run u).1.regs i = st.regs i := (pack_reg i hi hi' u).trans (hreg i hi)
  generalize hv : (pack.run u).1 = v at *
  have hfc := finish_cost v (W + 2 ^ t) (by
    intro i hi hi'
    by_cases hx : i = 63
    · subst i
      rw [hp]
      exact (HadamardLabel.code_size p).trans (by omega)
    · have hi62 : i.val ≤ 62 := by
        have : i.val ≠ 63 := by simpa [Fin.ext_iff] using hx
        omega
      rw [hpr i hi hi62]
      exact (hr i hi hi62).trans (by omega)) hpl
  have hq1 : (2 ^ t + 7) ^ 8 ≤ (2 ^ t + W + 8) ^ 8 :=
    Nat.pow_le_pow_left (by omega) _
  have hq2 : (2 ^ t + 1) ^ 2 ≤ (2 ^ t + W + 8) ^ 8 := by
    calc _ ≤ (2 ^ t + W + 8) ^ 2 := Nat.pow_le_pow_left (by omega) _
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hq3 : W + 2 ^ t + 1 ≤ (2 ^ t + W + 8) ^ 8 :=
    (by omega : W + 2 ^ t + 1 ≤ 2 ^ t + W + 8).trans (Nat.le_pow (by decide))
  have hc' := hc.trans (Nat.mul_le_mul_left _ hq1)
  have hpc' := hpc.trans (Nat.mul_le_mul_left _ hq2)
  have hfc' := hfc.trans (Nat.mul_le_mul_left _ hq3)
  have hpos : 1 ≤ (2 ^ t + W + 8) ^ 8 := Nat.one_le_pow _ _ (by omega)
  change ((Stmt.seq (.copy 7 24) (.seq (.assign 56 (.const 3))
    (.seq homogeneous (.seq pack finish)))).run st).2 ≤ _
  simp only [run_seq_snd, run_copy_snd, run_copy_fst, run_assign_fst, Expr.eval, he,
    listSize, List.map_nil, List.sum_nil, Nat.zero_add]
  dsimp only [s] at hc hu
  rw [hu, hv]
  have hconst : ((Stmt.assign 56 (.const 3) : Stmt 80 32).run
      (setList st 24 [])).2 = 5 := by
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, show Nat.size 3 = 2 from rfl]
  rw [hconst]
  nlinarith only [hc', hpc', hfc', hpos]

end PCP.Lang.DifferenceQueries
