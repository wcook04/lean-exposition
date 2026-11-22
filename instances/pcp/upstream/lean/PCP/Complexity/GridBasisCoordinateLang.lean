import PCP.Complexity.GridFactorLang

/-!
# A uniform one-coordinate Lagrange basis program

A counted loop multiplies the factors at all numeric grid nodes except the selected
node. The grid size and selected node are data supplied to one fixed program.
-/

namespace PCP.Lang.GridBasisCoordinate

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

/-- Partial tensor-factor product in the production field-code ordering. -/
def value (z : BinaryMaterializedField.Element t) (k n : ℕ) :
    BinaryMaterializedField.Element t :=
  ∏ j ∈ Finset.range n,
    if j = k then 1 else (z + GridFactor.node t j) /
      (GridFactor.node t k + GridFactor.node t j)

@[simp] theorem value_zero (z : BinaryMaterializedField.Element t) (k : ℕ) :
    value z k 0 = 1 := by simp [value]

@[simp] theorem value_succ (z : BinaryMaterializedField.Element t) (k j : ℕ) :
    value z k (j + 1) = value z k j *
      (if j = k then 1 else (z + GridFactor.node t j) /
        (GridFactor.node t k + GridFactor.node t j)) := by
  simp only [value, Finset.prod_range_succ]

def factorTerm : Term 4 := .bin .mul (.input 2)
  (.bin .mul (.bin .add (.input 0) (.input 1))
    (.inv (.bin .add (.input 3) (.input 1))))

def env (z : BinaryMaterializedField.Element t) (k j : ℕ) :
    Fin 4 → BinaryMaterializedField.Element t :=
  ![z, GridFactor.node t j, value z k j, GridFactor.node t k]

theorem factorTerm_eval (z : BinaryMaterializedField.Element t) (k j : ℕ) (hjk : j ≠ k) :
    factorTerm.eval (env z k j) = value z k (j + 1) := by
  simp [factorTerm, Term.eval, env, Op.fieldEval, hjk, div_eq_mul_inv]

def update : Stmt 40 12 := .seq (scalar factorTerm) (.assign 2 (.var 30))

def advance : Stmt 40 12 := .seq (.assign 4 (.eq 1 3)) (.ite 4 .skip update)

def body : Stmt 40 12 :=
  .seq advance (.seq (.assign 31 (.const 1)) (.assign 1 (.add 1 31)))

/-- Point code 0, chosen-node code 3, width 24, node count 32; output code 2. -/
def program : Stmt 40 12 :=
  .seq (.assign 1 (.const 0)) (.seq (.assign 2 (.const 1)) (.loop 32 body))

def Inv (z : BinaryMaterializedField.Element t) (k n j : ℕ) (st : State 40 12) : Prop :=
  st.regs 0 = (fieldEquiv t z).val ∧ st.regs 1 = j ∧
  st.regs 2 = (fieldEquiv t (value z k j)).val ∧ st.regs 3 = k ∧
  st.regs 24 = t ∧ st.regs 32 = n ∧
  st.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = []

theorem inv_view (z : BinaryMaterializedField.Element t) (k n j : ℕ) (st : State 40 12)
    (h : Inv z k n j st) (hj : j < 2 ^ t) (hk : k < 2 ^ t) :
    View t (env z k j) st := by
  refine ⟨?_, h.2.2.2.2.1, h.2.2.2.2.2.2⟩
  intro i
  fin_cases i
  · exact h.1
  · simpa [env, GridFactor.code_node j hj] using h.2.1
  · exact h.2.2.1
  · simpa [env, GridFactor.code_node k hk] using h.2.2.2.1

/-- The conditional field update returns the next product, retaining the old index. -/
theorem advance_spec (z : BinaryMaterializedField.Element t) (k n j : ℕ)
    (st : State 40 12) (h : Inv z k n j st) (hj : j < 2 ^ t) (hk : k < 2 ^ t) :
    let u := (advance.run st).1
    u.regs 0 = (fieldEquiv t z).val ∧ u.regs 1 = j ∧
    u.regs 2 = (fieldEquiv t (value z k (j + 1))).val ∧ u.regs 3 = k ∧
    u.regs 24 = t ∧ u.regs 32 = n ∧
    u.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧ u.lists 7 = [] := by
  by_cases heq : j = k
  · have hval : value z k (j + 1) = value z k j := by simp [heq]
    simpa [Inv, advance, run_seq_fst, run_assign_fst, run_ite_fst, Expr.eval,
      Function.update, h.2.1, h.2.2.2.1, heq, hval, Stmt.run] using h
  · let s := setReg st 4 0
    have hs : Inv z k n j s := by
      simpa [Inv, s, Function.update] using h
    obtain ⟨ho, _, hv⟩ := scalar_spec factorTerm s (env z k j) (inv_view z k n j s hs hj hk)
    rw [factorTerm_eval z k j heq] at ho
    have hf := run_regs_frame (scalar factorTerm) 32 (by decide) s
    have hr : (advance.run st).1 = setReg ((scalar factorTerm).run s).1 2
        (((scalar factorTerm).run s).1.regs 30) := by
      simp [advance, update, run_seq_fst, run_assign_fst, run_ite_fst, Expr.eval,
        Function.update, h.2.1, h.2.2.2.1, heq, s]
    dsimp only
    rw [hr]
    generalize hu : ((scalar factorTerm).run s).1 = u at *
    have h0 : u.regs 0 = (fieldEquiv t z).val := hv.1 0
    have h1 : u.regs 1 = j := by simpa [env, GridFactor.code_node j hj] using hv.1 1
    have h3 : u.regs 3 = k := by simpa [env, GridFactor.code_node k hk] using hv.1 3
    have h24 : u.regs 24 = t := hv.2.1
    have h32 : u.regs 32 = n := hf.trans hs.2.2.2.2.2.1
    change u.regs 30 = _ at ho
    simp [Function.update, h0, h1, h3, h24, h32, ho, hv.2.2.1, hv.2.2.2]

theorem body_inv (z : BinaryMaterializedField.Element t) (k n j : ℕ) (st : State 40 12)
    (h : Inv z k n j st) (hj : j < 2 ^ t) (hk : k < 2 ^ t) :
    Inv z k n (j + 1) (body.run st).1 := by
  have ha := advance_spec z k n j st h hj hk
  simp only [body, run_seq_fst]
  generalize hu : (advance.run st).1 = u at *
  obtain ⟨h0, h1, h2, h3, h24, h32, hm, he⟩ := ha
  simp [Inv, run_assign_fst, Expr.eval, Function.update, h0, h1, h2, h3, h24, h32, hm, he]

theorem program_run (z : BinaryMaterializedField.Element t) (k n : ℕ)
    (hn : n ≤ 2 ^ t) (hk : k < 2 ^ t) (st : State 40 12)
    (h0 : st.regs 0 = (fieldEquiv t z).val) (h3 : st.regs 3 = k)
    (ht : st.regs 24 = t) (hc : st.regs 32 = n)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    Inv z k n n (program.run st).1 := by
  let s := setReg (setReg st 1 0) 2 1
  have hi : Inv z k n 0 s := by
    refine ⟨by simpa [s, Function.update] using h0, by simp [s, Function.update], ?_,
      by simpa [s, Function.update] using h3, by simpa [s, Function.update] using ht,
      by simpa [s, Function.update] using hc, hm, he⟩
    change 1 = (fieldEquiv t (value z k 0)).val
    rw [value_zero, code_one]
  have hout := iterate_inv body.run (Nat.size n + 1) n (Inv z k n)
    (fun j u hj hu => body_inv z k n j u hu (lt_of_lt_of_le hj hn) hk) s hi
  simpa only [program, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update_of_ne (by decide : (32 : Fin 40) ≠ 2),
    Function.update_of_ne (by decide : (32 : Fin 40) ≠ 1), hc] using hout

end PCP.Lang.GridBasisCoordinate
