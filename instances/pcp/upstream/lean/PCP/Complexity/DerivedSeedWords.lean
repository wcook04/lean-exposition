import PCP.Complexity.DerivedSeedDecode
import PCP.Complexity.HadamardSeedMaterialize

/-! # Actual coordinate, bit-word and coefficient-mask materialization for derived seeds -/

-- Fixed port arithmetic uses 300 registers.
set_option maxRecDepth 1024

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode
open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

def vectorPrepare (src len : Fin 300) (base : Expr 300) : Stmt 300 112 :=
  .seq (.copy 100 2) (.seq (.assign 0 (.var src))
    (.seq (.assign 5 (.var len)) (.assign 6 base)))

def vectorDecode : Stmt 300 112 := DerivedCall.call (by decide) (by decide) UniformDecode.program

def vector (src len : Fin 300) (base : Expr 300) (dst : Fin 112) : Stmt 300 112 :=
  .seq (vectorPrepare src len base) (.seq vectorDecode (.copy 1 dst))

theorem vector_field {σ : Type*} (σc : Codec σ)
    (p : σ → BinaryMaterializedField.Element t) (src len : Fin 300) (dst : Fin 112)
    (hlen : 220 ≤ len.val) (st : State 300 112)
    (hc : st.regs src =
      ((σc.function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv p).val)
    (hn : st.regs len = σc.size) (hb : st.regs 243 = 2 ^ t) (he : st.lists 100 = []) :
    ((vector src len (.var 243) dst).run st).1.lists dst =
      List.ofFn (fun i => (fieldEquiv t (p (σc.equiv.symm i))).val) := by
  have hl0 : len ≠ 0 := by intro h; subst len; norm_num at hlen
  have h := UniformDecode.program_fieldPoint σc p
    (DerivedCall.view (by decide) (by decide) (vectorPrepare src len (.var 243) |>.run st).1)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict] using hc)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict, hl0] using hn)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict] using hb)
    (by simpa [vectorPrepare, Stmt.run, Function.update,
      DerivedCall.view, State.restrict] using he)
  rw [← DerivedCall.call_result (by decide) (by decide) UniformDecode.program
    (vectorPrepare src len (.var 243) |>.run st).1] at h
  simpa only [vector, run_seq_fst, run_copy_fst, setList_lists, Function.update_self,
    vectorDecode, DerivedCall.view, State.restrict_lists,
    show Fin.castLE (by decide : 3 ≤ 112) (1 : Fin 3) = (1 : Fin 112) from rfl] using h

omit [NeZero t] in
theorem vector_bits (w : Fin t → ZMod 2) (src : Fin 300) (dst : Fin 112)
    (st : State 300 112) (hc : st.regs src = ((bitsCodec t).equiv w).val)
    (ht : st.regs 240 = t) (he : st.lists 100 = []) :
    ((vector src 240 (.const 2) dst).run st).1.lists dst =
      List.ofFn (fun i => (w i).val) := by
  have h := UniformDecode.program_bits w
    (DerivedCall.view (by decide) (by decide) (vectorPrepare src 240 (.const 2) |>.run st).1)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict] using hc)
    (by simpa [vectorPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict] using ht)
    (by simp [vectorPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict])
    (by simpa [vectorPrepare, Stmt.run, Function.update,
      DerivedCall.view, State.restrict] using he)
  rw [← DerivedCall.call_result (by decide) (by decide) UniformDecode.program
    (vectorPrepare src 240 (.const 2) |>.run st).1] at h
  simpa only [vector, run_seq_fst, run_copy_fst, setList_lists, Function.update_self,
    vectorDecode, DerivedCall.view, State.restrict_lists,
    show Fin.castLE (by decide : 3 ≤ 112) (1 : Fin 3) = (1 : Fin 112) from rfl] using h

theorem vector_reg (src len i : Fin 300) (base : Expr 300) (dst : Fin 112)
    (hi : 220 ≤ i.val) (st : State 300 112) :
    ((vector src len base dst).run st).1.regs i = st.regs i := by
  have hp : ((vectorPrepare src len base).run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hb : ∀ j ∈ (vectorPrepare src len base).regWrites, j.val < 220 := by
      simp [vectorPrepare, Stmt.regWrites]
    intro hm
    have := hb i hm
    omega
  have hd := DerivedCall.call_reg (by decide) (by decide) UniformDecode.program
    (vectorPrepare src len base |>.run st).1 i hi
  simpa only [vector, run_seq_fst, run_copy_fst, setList_regs, vectorDecode] using hd.trans hp

theorem vector_list (src len : Fin 300) (base : Expr 300) (dst L : Fin 112)
    (hL : 96 ≤ L.val) (hne : L ≠ dst) (st : State 300 112) :
    ((vector src len base dst).run st).1.lists L = st.lists L := by
  have hp : ((vectorPrepare src len base).run st).1.lists L = st.lists L := by
    apply run_lists_frame
    have hb : ∀ j ∈ (vectorPrepare src len base).listWrites, j.val < 96 := by
      simp [vectorPrepare, Stmt.listWrites]
    intro hm
    have := hb L hm
    omega
  have hd := DerivedCall.call_list (by decide) (by decide) UniformDecode.program
    (vectorPrepare src len base |>.run st).1 L hL
  simpa only [vector, run_seq_fst, run_copy_fst, setList_lists,
    Function.update_of_ne hne, vectorDecode] using hd.trans hp

def maskPrepare : Stmt 300 112 := .seq (.copy 100 7) (.seq (.copy 100 25)
  (.seq (.push 25 277) (.assign 20 (.var 240))))

def maskLoad : Stmt 300 112 :=
  DerivedCall.call (by decide) (by decide) (HadamardSeed.loadTo 3 18)

def mask : Stmt 300 112 := .seq maskPrepare (.seq maskLoad (.copy 18 106))

attribute [local irreducible] HadamardSeed.loadTo maskLoad

omit [NeZero t] in
theorem mask_run (p : BinaryPolynomialSpace.Coefficients t 3) (st : State 300 112)
    (ht : st.regs 240 = t) (he : st.lists 100 = [])
    (hp : st.regs 277 = ((coefficientCodec t 3).equiv p).val) :
    (mask.run st).1.lists 106 = BooleanCoefficientList.encode p := by
  have hp' : st.regs 277 = HadamardLabel.code p := hp
  have h := (HadamardSeed.loadTo_run p [] 18 (by decide) (by decide)
    (DerivedCall.view (by decide) (by decide) (maskPrepare.run st).1)
    (by simpa [maskPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict] using ht)
    (by simpa [maskPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict] using he)
    (by simpa [maskPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict, he] using hp')).1
  rw [← DerivedCall.call_result (by decide) (by decide) (HadamardSeed.loadTo 3 18)
    (maskPrepare.run st).1] at h
  change ((DerivedCall.call (by decide) (by decide) (HadamardSeed.loadTo 3 18)).run
    (maskPrepare.run st).1).1.lists 18 = _ at h
  simpa only [mask, run_seq_fst, run_copy_fst, setList_lists,
    Function.update_self, maskLoad] using h

theorem mask_reg (st : State 300 112) (i : Fin 300) (hi : 220 ≤ i.val) :
    (mask.run st).1.regs i = st.regs i := by
  have hp : (maskPrepare.run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hb : ∀ j ∈ maskPrepare.regWrites, j.val < 220 := by decide
    intro hm
    have := hb i hm
    omega
  have hd := DerivedCall.call_reg (by decide) (by decide) (HadamardSeed.loadTo 3 18)
    (maskPrepare.run st).1 i hi
  simpa only [mask, run_seq_fst, run_copy_fst, setList_regs, maskLoad] using hd.trans hp

theorem mask_list (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val) (hne : L ≠ 106) :
    (mask.run st).1.lists L = st.lists L := by
  have hp : (maskPrepare.run st).1.lists L = st.lists L := by
    apply run_lists_frame
    have hb : ∀ j ∈ maskPrepare.listWrites, j.val < 96 := by decide
    intro hm
    have := hb L hm
    omega
  have hd := DerivedCall.call_list (by decide) (by decide) (HadamardSeed.loadTo 3 18)
    (maskPrepare.run st).1 L hL
  simpa only [mask, run_seq_fst, run_copy_fst, setList_lists,
    Function.update_of_ne hne, maskLoad] using hd.trans hp

end PCP.Lang.DerivedSeed
