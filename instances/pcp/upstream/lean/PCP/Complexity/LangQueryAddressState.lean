import PCP.Complexity.LangQueryAddress
import PCP.Complexity.ArithmeticExpressionCost

/-!
# Proof-address computation inside a live verifier state

Address evaluation retains its source payload and expression stack, and an emit
operation prepends the actual production address to the stored query list.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.QueryAddress

open ArithmeticExpression PCP.Algebraic ThreeColorVerifier

variable {F : Type*} {q n m c t C1 C3 : ℕ}

def View (eF : F ≃ Fin q) (e1 : BinaryPolynomialSpace.Coefficients t 1 ≃ Fin C1)
    (e3 : BinaryPolynomialSpace.Coefficients t 3 ≃ Fin C3) (z : Query F n m c t)
    (st : State 14 2) : Prop :=
  ∀ i : Fin 11, st.regs (i.castAdd 3) = inputs eF e1 e3 z i

theorem program_run_state (eF : F ≃ Fin q)
    (e1 : BinaryPolynomialSpace.Coefficients t 1 ≃ Fin C1)
    (e3 : BinaryPolynomialSpace.Coefficients t 3 ≃ Fin C3)
    (z : Query F n m c t) (st : State 14 2) (hv : View eF e1 e3 z st) :
    (program.run st).1.regs 11 = (ThreeColorQueryIndex.equiv eF e1 e3 z).val := by
  have hr := (scalar_spec term st).1
  have he : (fun i : Fin 11 => st.regs (i.castAdd 3)) = inputs eF e1 e3 z := funext hv
  rw [he, term_eq] at hr
  exact hr

theorem program_frame (st : State 14 2) :
    (∀ i : Fin 11, (program.run st).1.regs (i.castAdd 3) = st.regs (i.castAdd 3)) ∧
    (program.run st).1.lists 0 = st.lists 0 ∧ (program.run st).1.lists 1 = st.lists 1 := by
  exact ⟨fun i => scalar_preserves_input term i st,
    scalar_preserves_source term st, (scalar_spec term st).2⟩

theorem program_cost_state (st : State 14 2) (W : ℕ)
    (hr : ∀ i : Fin 11, Nat.size (st.regs (i.castAdd 3)) ≤ W)
    (hs : listSize (st.lists 1) ≤ W) :
    (program.run st).2 ≤ program.C * (program.width + program.csize + 1) * (W + 1) :=
  scalar_cost_state term st W hr hs

/-- Append construction uses a reversed query accumulator, later reversed once. -/
def emit : Stmt 14 2 := .seq program (.push 0 11)

theorem emit_run (eF : F ≃ Fin q)
    (e1 : BinaryPolynomialSpace.Coefficients t 1 ≃ Fin C1)
    (e3 : BinaryPolynomialSpace.Coefficients t 3 ≃ Fin C3)
    (z : Query F n m c t) (st : State 14 2) (hv : View eF e1 e3 z st) :
    (emit.run st).1.lists 0 = (ThreeColorQueryIndex.equiv eF e1 e3 z).val :: st.lists 0 ∧
    View eF e1 e3 z (emit.run st).1 ∧ (emit.run st).1.lists 1 = st.lists 1 := by
  have hr := program_run_state eF e1 e3 z st hv
  have hf := program_frame st
  simp only [emit, run_seq_fst, run_push_fst]
  refine ⟨?_, ?_, ?_⟩
  · simp [hr, hf.2.1]
  · intro i
    exact (hf.1 i).trans (hv i)
  · exact hf.2.2

/-- Only the evaluated address's own bit length is added to scalar evaluation cost. -/
theorem emit_cost (eF : F ≃ Fin q)
    (e1 : BinaryPolynomialSpace.Coefficients t 1 ≃ Fin C1)
    (e3 : BinaryPolynomialSpace.Coefficients t 3 ≃ Fin C3)
    (z : Query F n m c t) (st : State 14 2) (hv : View eF e1 e3 z st) (W : ℕ)
    (hr : ∀ i : Fin 11, Nat.size (st.regs (i.castAdd 3)) ≤ W)
    (hs : listSize (st.lists 1) ≤ W)
    (ha : Nat.size (ThreeColorQueryIndex.equiv eF e1 e3 z).val ≤ W) :
    (emit.run st).2 ≤ (program.C * (program.width + program.csize + 1) + 2) * (W + 1) := by
  have hc := program_cost_state st W hr hs
  have ho := program_run_state eF e1 e3 z st hv
  simp only [emit, run_seq_snd, run_push_snd, ho]
  nlinarith

end PCP.Lang.QueryAddress
