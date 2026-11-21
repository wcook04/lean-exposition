import PCP.Complexity.LangBinaryEncode
import PCP.Complexity.LangSymbolBridge

/-!
# Packing the verifier's actual halt and query answers

A halt is a single Boolean code. A query is separator code two followed by the
canonical binary address. The loop budget is a supplied bound on address bit
length, so a large binary address does not trigger a loop of its numeric value.
-/

namespace PCP.Lang.AnswerEncode

open PCP.Machine LangSymbolBridge

theorem code_bits (bs : List Bool) : code (ofBits bs) = bs.map Bool.toNat := by
  simp only [code, ofBits, List.map_map]
  congr 1
  funext b
  cases b <;> rfl

/-- Register zero holds the address, register one its bit-length budget; list zero is output. -/
def query : Stmt 4 1 := .seq BinaryEncode.program
  (.seq (.assign 2 (.const 2)) (.push 0 2))

/-- The emitted list is exactly the public machine encoding's natural-symbol representation. -/
theorem query_run (st : State 4 1) (h : Nat.size (st.regs 0) ≤ st.regs 1)
    (hL : st.lists 0 = []) :
    (query.run st).1.lists 0 = code (encodeAnswer (.inr (st.regs 0))) := by
  have hb := (BinaryEncode.program_run st h).2
  simp only [query, run_seq_fst, run_assign_fst, run_push_fst, Expr.eval,
    setList_lists, setReg_lists, setReg_regs, Function.update_self]
  rw [hb, hL]
  simp only [List.reverse_nil, List.nil_append, encodeAnswer, code, List.map_cons, symbolCode]
  exact congrArg (2 :: ·) (code_bits _).symm

/-- Full query packing retains a polynomial charged runtime. -/
theorem query_cost (st : State 4 1) (h : Nat.size (st.regs 0) ≤ st.regs 1) :
    (query.run st).2 ≤ (BinaryEncode.passConstant + 20) *
      (st.regs 1 + Nat.size (st.regs 0) + listSize (st.lists 0) + 3) ^ 2 := by
  have hb := BinaryEncode.program_cost st h
  have htwo : Nat.size 2 = 2 := Nat.size_pow (n := 1)
  have htail : ∀ s : State 4 1,
      ((Stmt.seq (.assign 2 (.const 2)) (.push 0 2)).run s).2 = 9 := by
    intro s
    simp [Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update, htwo]
  simp only [query, run_seq_snd, htail]
  have hp : 1 ≤ (st.regs 1 + Nat.size (st.regs 0) + listSize (st.lists 0) + 3) ^ 2 := by
    exact one_le_pow₀ (by omega)
  nlinarith

/-- The halt encoder reads the already computed Boolean verdict from register zero. -/
def halt : Stmt 4 1 := .push 0 0

theorem halt_run (st : State 4 1) (b : Bool) (h : st.regs 0 = b.toNat)
    (hL : st.lists 0 = []) :
    (halt.run st).1.lists 0 = code (encodeAnswer (.inl b)) := by
  cases b <;> simp [halt, Stmt.run, Function.update, h, hL, code, encodeAnswer, symbolCode]

theorem halt_cost (st : State 4 1) (b : Bool) (h : st.regs 0 = b.toNat) :
    (halt.run st).2 ≤ 2 := by
  cases b <;> simp [halt, Stmt.run, h]

end PCP.Lang.AnswerEncode
