import PCP.Complexity.DerivedSeedWords
import PCP.Complexity.GridEdgeLang

/-! # Computing the public edge weight for the proper derived-grid branch -/

-- Fixed port arithmetic uses 300 registers.
set_option maxRecDepth 1024

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode
open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

def weight (k : Certificate) (h : ℕ) (hh : h ≤ 2 ^ t) (x : List Bool)
    (s : DerivedGrid.Sample k t n m) : OuterBranch.Field t := by
  cases k with
  | valid => exact 0
  | proper =>
      exact FieldQueryArithmetic.edgeValue
        (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
        (ThreeColorGridIndex.pad (FiniteAlphabetIndex.code (fieldEquiv t) hh) n
          (ThreeColorEncoding.graph x)) s.1

def edgePrepare : Stmt 300 112 := .seq (.assign 44 (.var 240))
  (.seq (.assign 45 (.var 279)) (.seq (.assign 54 (.var 280))
    (.seq (.copy 101 3) (.seq (.copy 100 7) (.seq (.copy 109 12) (.copy 111 16))))))

def edgeCall : Stmt 300 112 := DerivedCall.call (by decide) (by decide) GridEdge.program

def edge : Certificate → Stmt 300 112
  | .valid => .assign 245 (.const 0)
  | .proper => .seq edgePrepare (.seq edgeCall (.assign 245 (.var 50)))

attribute [local irreducible] GridEdge.program edgeCall

theorem edge_run (k : Certificate) (h : ℕ) (hh : h ≤ 2 ^ t) (x : List Bool)
    (s : DerivedGrid.Sample k t n m) (st : State 300 112)
    (ht : st.regs 240 = t) (hh' : st.regs 279 = h) (hn : st.regs 280 = n)
    (hmod : st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 100 = [])
    (hz : st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val))
    (hx : st.lists 111 = x.map Bool.toNat) :
    ((edge k).run st).1.regs 245 = (fieldEquiv t (weight k h hh x s)).val := by
  cases k with
  | valid => simpa only [edge, run_assign_fst, Expr.eval, setReg_regs, Function.update_self,
      weight] using (FieldExpression.code_zero (t := t)).symm
  | proper =>
    have hi : GridEdge.Input t h n x s.1
        (DerivedCall.view (by decide) (by decide) (edgePrepare.run st).1) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using ht
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hh'
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hn
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hmod
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using he
      · calc _ = st.lists 109 := by
                simp [edgePrepare, Stmt.run, Expr.eval, Function.update,
                  DerivedCall.view, State.restrict]
             _ = _ := hz
      · simpa [edgePrepare, Stmt.run, Expr.eval, Function.update,
          DerivedCall.view, State.restrict] using hx
    have hr := GridEdge.program_run hh x s.1
      (DerivedCall.view (by decide) (by decide) (edgePrepare.run st).1) hi
    rw [← DerivedCall.call_result (by decide) (by decide) GridEdge.program
      (edgePrepare.run st).1] at hr
    change ((DerivedCall.call (by decide) (by decide) GridEdge.program).run
      (edgePrepare.run st).1).1.regs 50 = _ at hr
    simpa only [edge, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
      Function.update_self, edgeCall, weight] using hr

theorem edge_reg (k : Certificate) (st : State 300 112) (i : Fin 300)
    (hi : 220 ≤ i.val) (hne : i ≠ 245) : ((edge k).run st).1.regs i = st.regs i := by
  cases k with
  | valid => simp [edge, Stmt.run, Function.update, hne]
  | proper =>
    have hp : (edgePrepare.run st).1.regs i = st.regs i := by
      apply run_regs_frame
      have hb : ∀ j ∈ edgePrepare.regWrites, j.val < 220 := by decide
      intro hm
      have := hb i hm
      omega
    have hd := DerivedCall.call_reg (by decide) (by decide) GridEdge.program
      (edgePrepare.run st).1 i hi
    simpa only [edge, run_seq_fst, run_assign_fst, setReg_regs,
      Function.update_of_ne hne, edgeCall] using hd.trans hp

theorem edge_list (k : Certificate) (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val) :
    ((edge k).run st).1.lists L = st.lists L := by
  cases k with
  | valid => rfl
  | proper =>
    have hp : (edgePrepare.run st).1.lists L = st.lists L := by
      apply run_lists_frame
      have hb : ∀ j ∈ edgePrepare.listWrites, j.val < 96 := by decide
      intro hm
      have := hb L hm
      omega
    have hd := DerivedCall.call_list (by decide) (by decide) GridEdge.program
      (edgePrepare.run st).1 L hL
    simpa only [edge, run_seq_fst, run_assign_fst, setReg_lists, edgeCall] using hd.trans hp

end PCP.Lang.DerivedSeed
