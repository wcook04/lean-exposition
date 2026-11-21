import PCP.Complexity.ArithmeticConditionals
import PCP.Complexity.ArithmeticLookupCost
import PCP.Algebraic.GridEdgeArithmetic
import PCP.Algebraic.ThreeColorEncoding

/-!
# Arithmetic lookup of public graph adjacency

The reader checks both orientations of the stored adjacency matrix, rejects loops
and padded vertices, and treats missing entries as false. It is exact on every
public bitstring, including malformed graph encodings.
-/

namespace PCP.Lang.GraphAdjacency

open ArithmeticExpression ArithmeticLookup PCP.Algebraic

/-- The total numeric equivalent of the public graph decoder. -/
def bit (input : List ℕ) (N u v : ℕ) : ℕ :=
  if u < N then if v < N then if u = v then 0 else
    if input.getD (N + 1 + (u * N + v)) 0 = 1 then 1 else
      if input.getD (N + 1 + (v * N + u)) 0 = 1 then 1 else 0
  else 0 else 0

theorem bit_lt (input : List ℕ) (N u v : ℕ) : bit input N u v < 2 := by
  unfold bit
  split_ifs <;> decide

theorem source_bit (x : List Bool) (u v : Fin (ThreeColorEncoding.vertexCount x)) :
    (x.map Bool.toNat).getD (ThreeColorEncoding.vertexCount x + 1 +
      (u.val * ThreeColorEncoding.vertexCount x + v.val)) 0 =
    (ThreeColorEncoding.edgeBit x u v).toNat := by
  change (x.map Bool.toNat).getD _ false.toNat = _
  rw [List.getD_map]
  unfold ThreeColorEncoding.edgeBit ThreeColorEncoding.payload
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem bit_correct (x : List Bool) (u v : ℕ) :
    bit (x.map Bool.toNat) (ThreeColorEncoding.vertexCount x) u v =
      if GridEdgeArithmetic.Adj (ThreeColorEncoding.graph x) u v then 1 else 0 := by
  by_cases hu : u < ThreeColorEncoding.vertexCount x
  · by_cases hv : v < ThreeColorEncoding.vertexCount x
    · simp only [bit, ite_eq_left hu, ite_eq_left hv, GridEdgeArithmetic.Adj, dite_eq_left hu, dite_eq_left hv]
      rw [source_bit x ⟨u, hu⟩ ⟨v, hv⟩, source_bit x ⟨v, hv⟩ ⟨u, hu⟩]
      cases h₁ : ThreeColorEncoding.edgeBit x ⟨u, hu⟩ ⟨v, hv⟩ <;>
        cases h₂ : ThreeColorEncoding.edgeBit x ⟨v, hv⟩ ⟨u, hu⟩ <;>
          simp [ThreeColorEncoding.graph, h₁, h₂, Fin.ext_iff]
    · simp [bit, GridEdgeArithmetic.Adj, hu, hv]
  · simp [bit, GridEdgeArithmetic.Adj, hu]

def answerTerm : Term 7 :=
  .iteLt (.input 5) (.input 1)
    (.iteLt (.input 6) (.input 1)
      (.iteEq (.input 5) (.input 6) (.const 0)
        (.iteEq (.input 3) (.const 1) (.const 1)
          (.iteEq (.input 4) (.const 1) (.const 1) (.const 0)))) (.const 0)) (.const 0)

@[irreducible] def code : Code 7 :=
  .seq (.assign 5 (.bin .mod (.input 0) (.input 2)))
    (.seq (.assign 6 (.bin .div (.input 0) (.input 2)))
      (.seq (.lookup 3 (.bin .add (.bin .add (.input 1) (.const 1))
        (.bin .add (.bin .mul (.input 5) (.input 1)) (.input 6))))
        (.seq (.lookup 4 (.bin .add (.bin .add (.input 1) (.const 1))
          (.bin .add (.bin .mul (.input 6) (.input 1)) (.input 5))))
          (.assign 4 answerTerm))))

theorem code_eval (input : List ℕ) (r : Fin 7 → ℕ) :
    (code.eval input r) 0 = r 0 ∧ (code.eval input r) 1 = r 1 ∧
      (code.eval input r) 2 = r 2 ∧
      (code.eval input r) 4 = bit input (r 1) (r 0 % r 2) (r 0 / r 2) := by
  simp only [code, Code.eval, answerTerm, Term.eval_iteLt, Term.eval_iteEq,
    Term.eval, Op.eval]
  simp [Function.update, bit]

def reset : Stmt 11 3 := .seq (.assign 3 (.const 0))
  (.seq (.assign 4 (.const 0)) (.seq (.assign 5 (.const 0)) (.assign 6 (.const 0))))

def program : Stmt 11 3 := .seq reset code.compile

theorem reset_inputs (st : State 11 3) (i : Fin 7) :
    inputs (reset.run st).1 i = if i.val < 3 then inputs st i else 0 := by
  fin_cases i <;> simp [reset, inputs, Stmt.run, Expr.eval, Function.update]

theorem reset_lists (st : State 11 3) : (reset.run st).1.lists = st.lists := by
  simp [reset, Stmt.run]

theorem reset_cost (st : State 11 3) : (reset.run st).2 = 7 := by
  simp [reset, Stmt.run, Expr.cost, Expr.readSize, Expr.eval]

/-- Exact public adjacency answer and the preserved source data. -/
theorem program_run (st : State 11 3) :
    (program.run st).1.regs 4 = bit (st.lists 0) (st.regs 1)
      (st.regs 0 % st.regs 2) (st.regs 0 / st.regs 2) ∧
    (program.run st).1.regs 0 = st.regs 0 ∧
    (program.run st).1.regs 1 = st.regs 1 ∧
    (program.run st).1.regs 2 = st.regs 2 ∧
    (program.run st).1.lists 0 = st.lists 0 ∧
    (program.run st).1.lists 1 = st.lists 1 := by
  have hs := code.spec (reset.run st).1
  have he := code_eval ((reset.run st).1.lists 0) (inputs (reset.run st).1)
  simp only [program, run_seq_fst]
  have h0 : inputs (reset.run st).1 0 = st.regs 0 := by
    rw [reset_inputs]
    rfl
  have h1 : inputs (reset.run st).1 1 = st.regs 1 := by
    rw [reset_inputs]
    rfl
  have h2 : inputs (reset.run st).1 2 = st.regs 2 := by
    rw [reset_inputs]
    rfl
  refine ⟨?_, (congrFun hs.1 0).trans (he.1.trans h0),
    (congrFun hs.1 1).trans (he.2.1.trans h1),
    (congrFun hs.1 2).trans (he.2.2.1.trans h2),
    hs.2.1.trans (congrFun (reset_lists st) 0), hs.2.2.trans (congrFun (reset_lists st) 1)⟩
  exact (congrFun hs.1 4).trans (by rw [he.2.2.2, reset_lists, h0, h1, h2])

/-- The reader's charged cost is independent of unused incoming scratch registers. -/
theorem program_cost : ∃ C : ℕ, ∀ (st : State 11 3) (W : ℕ),
    (∀ i : Fin 3, Nat.size (st.regs (i.castAdd 8)) ≤ W) → listSize (st.lists 0) ≤ W →
    (program.run st).2 ≤ C * (W + 1) ^ 2 := by
  obtain ⟨C, _, hC⟩ := code.cost_bound
  refine ⟨C + 8, fun st W hr hl => ?_⟩
  have hi : ∀ i : Fin 7, Nat.size (inputs (reset.run st).1 i) ≤ W := by
    intro i
    rw [reset_inputs]
    split_ifs with hi
    · exact hr ⟨i.val, hi⟩
    · simp
  have hc := (hC (reset.run st).1 W hi (by simpa only [reset_lists] using hl)).1
  rw [program, run_seq_snd, reset_cost]
  have hp : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

end PCP.Lang.GraphAdjacency
