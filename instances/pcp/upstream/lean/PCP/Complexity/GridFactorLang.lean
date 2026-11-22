import PCP.Complexity.FieldExpressionCost
import PCP.Algebraic.FiniteAlphabetIndex

/-!
# Uniform evaluation of grid-vanishing factors

A fixed counted-loop program visits the initial field-code alphabet and multiplies
its linear factors. The alphabet size is stored data, not part of the program.
-/

namespace PCP.Lang.GridFactor

open PCP.Algebraic BinaryField BinaryFieldCode FieldExpression

variable {t : ℕ} [NeZero t]

/-- Total numeric decoding, agreeing with the field indexing below the cardinality. -/
def node (t j : ℕ) : BinaryMaterializedField.Element t :=
  (fieldEquiv t).symm ⟨j % 2 ^ t, Nat.mod_lt _ (by positivity)⟩

omit [NeZero t] in
@[simp] theorem code_node (j : ℕ) (hj : j < 2 ^ t) :
    (fieldEquiv t (node t j)).val = j := by
  simp [node, Nat.mod_eq_of_lt hj]

/-- Partial products at the consecutive numeric nodes. -/
def value (z : BinaryMaterializedField.Element t) (n : ℕ) :
    BinaryMaterializedField.Element t := ∏ j ∈ Finset.range n, (z + node t j)

@[simp] theorem value_zero (z : BinaryMaterializedField.Element t) : value z 0 = 1 := by
  simp [value]

@[simp] theorem value_succ (z : BinaryMaterializedField.Element t) (n : ℕ) :
    value z (n + 1) = value z n * (z + node t n) := by
  simp [value, Finset.prod_range_succ]

/-- Source registers contain the point, node and accumulated product. -/
def factorTerm : Term 3 := .bin .mul (.input 2) (.bin .add (.input 0) (.input 1))

def env (z : BinaryMaterializedField.Element t) (j : ℕ) :
    Fin 3 → BinaryMaterializedField.Element t := ![z, node t j, value z j]

@[simp] theorem factorTerm_eval (z : BinaryMaterializedField.Element t) (j : ℕ) :
    factorTerm.eval (env z j) = value z (j + 1) := by
  simp [factorTerm, Term.eval, env, Op.fieldEval]

def body : Stmt 39 12 :=
  .seq (scalar factorTerm) (.seq (.assign 2 (.var 29))
    (.seq (.assign 30 (.const 1)) (.assign 1 (.add 1 30))))

/-- Register 31 stores the number of nodes. Register 2 receives the product. -/
def program : Stmt 39 12 :=
  .seq (.assign 1 (.const 0)) (.seq (.assign 2 (.const 1)) (.loop 31 body))

def Inv (z : BinaryMaterializedField.Element t) (n j : ℕ) (st : State 39 12) : Prop :=
  st.regs 0 = (fieldEquiv t z).val ∧ st.regs 1 = j ∧
  st.regs 2 = (fieldEquiv t (value z j)).val ∧ st.regs 23 = t ∧
  st.regs 31 = n ∧ st.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧
  st.lists 7 = []

theorem inv_view (z : BinaryMaterializedField.Element t) (n j : ℕ) (st : State 39 12)
    (h : Inv z n j st) (hj : j < 2 ^ t) : View t (env z j) st := by
  refine ⟨?_, h.2.2.2.1, h.2.2.2.2.2⟩
  intro i
  fin_cases i
  · exact h.1
  · simpa [env, code_node j hj] using h.2.1
  · exact h.2.2.1

theorem body_inv (z : BinaryMaterializedField.Element t) (n j : ℕ) (st : State 39 12)
    (h : Inv z n j st) (hj : j < 2 ^ t) : Inv z n (j + 1) (body.run st).1 := by
  have hv := inv_view z n j st h hj
  obtain ⟨ho, hs, he⟩ := scalar_spec factorTerm st (env z j) hv
  rw [factorTerm_eval] at ho
  have hf := run_regs_frame (scalar factorTerm) 31 (by decide) st
  simp only [body, run_seq_fst]
  generalize hu : ((scalar factorTerm).run st).1 = u at *
  have h0 : u.regs 0 = (fieldEquiv t z).val := he.1 0
  have h1 : u.regs 1 = j := by simpa [env, code_node j hj] using he.1 1
  change u.regs 29 = _ at ho
  have hu23 : u.regs 23 = t := he.2.1
  simp only [run_assign_fst, Expr.eval]
  simp [Inv, Function.update, h0, h1, ho, hu23, hf.trans h.2.2.2.2.1,
    he.2.2.1, he.2.2.2]

/-- Exact product computation with width, point, count and modulus retained. -/
theorem program_run (z : BinaryMaterializedField.Element t) (n : ℕ) (hn : n ≤ 2 ^ t)
    (st : State 39 12) (h0 : st.regs 0 = (fieldEquiv t z).val)
    (ht : st.regs 23 = t) (hc : st.regs 31 = n)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    Inv z n n (program.run st).1 := by
  let s := setReg (setReg st 1 0) 2 1
  have hi : Inv z n 0 s := by
    refine ⟨by simpa [s, Function.update] using h0, by simp [s, Function.update],
      ?_, by simpa [s, Function.update] using ht,
      by simpa [s, Function.update] using hc, hm, he⟩
    change 1 = (fieldEquiv t (value z 0)).val
    rw [value_zero, code_one]
  have hout := iterate_inv body.run (Nat.size n + 1) n (Inv z n)
    (fun j u hj hu => body_inv z n j u hu (lt_of_lt_of_le hj hn)) s hi
  simpa only [program, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update_of_ne (by decide : (31 : Fin 39) ≠ 2),
    Function.update_of_ne (by decide : (31 : Fin 39) ≠ 1), hc] using hout

/-- The numeric loop evaluates precisely the production prefix-alphabet product. -/
theorem value_eq_alphabet (z : BinaryMaterializedField.Element t) (n : ℕ)
    (hn : n ≤ 2 ^ t) :
    value z n = ∏ a ∈ FiniteAlphabetIndex.alphabet (fieldEquiv t) hn, (z - a) := by
  rw [value, Finset.prod_range, FiniteAlphabetIndex.alphabet, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _
  have hi : i.val < 2 ^ t := lt_of_lt_of_le i.isLt hn
  have hnode : node t i.val = FiniteAlphabetIndex.prefixEmbedding (fieldEquiv t) hn i := by
    apply (fieldEquiv t).injective
    apply Fin.ext
    rw [code_node i.val hi, FiniteAlphabetIndex.code_prefixEmbedding]
    rfl
  rw [hnode, sub_eq_add_neg]
  rfl

end PCP.Lang.GridFactor
