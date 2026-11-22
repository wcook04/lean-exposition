import PCP.Complexity.DerivedSeedWords
import PCP.Complexity.GridRecoveryPoints
import PCP.Complexity.LangRadixCodec

/-! # Computing and encoding both actual derived-grid certificate points -/

-- Fixed port arithmetic uses 300 registers.
set_option maxRecDepth 1024

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode
open LocalCorrection DerivedGrid

variable {t n m : ℕ} [NeZero t]

def pointsPrepare : Stmt 300 112 := .seq (.assign 23 (.var 240))
  (.seq (.assign 31 (.var 279)) (.seq (.copy 101 3)
    (.seq (.copy 100 7) (.copy 109 12))))

def pointsCall : Stmt 300 112 := DerivedCall.call (by decide) (by decide) GridRecovery.points

def points : Stmt 300 112 := .seq pointsPrepare
  (.seq pointsCall (.seq (.copy 15 103) (.copy 16 104)))

attribute [local irreducible] GridRecovery.points pointsCall

theorem points_run (k : Certificate) (h : ℕ) (hh : h ≤ 2 ^ t)
    (s : DerivedGrid.Sample k t n m) (st : State 300 112)
    (ht : st.regs 240 = t) (hcount : st.regs 279 = h)
    (hmod : st.lists 101 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 100 = [])
    (hx : st.lists 109 = List.ofFn (fun i => (fieldEquiv t (s.1 i)).val)) :
    (points.run st).1.lists 103 =
      List.ofFn (fun i => (fieldEquiv t (k.outer.vector (firstPoint k s) i)).val) ∧
    (points.run st).1.lists 104 =
      List.ofFn (fun i => (fieldEquiv t (k.outer.vector
        (secondPoint k (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) s) i)).val) := by
  have hc : GridRecovery.Context t h
      (DerivedCall.view (by decide) (by decide) (pointsPrepare.run st).1) := by
    constructor
    · simpa [pointsPrepare, Stmt.run, Expr.eval, Function.update,
        DerivedCall.view, State.restrict] using ht
    constructor
    · simpa [pointsPrepare, Stmt.run, Expr.eval, Function.update,
        DerivedCall.view, State.restrict] using hcount
    constructor
    · simpa [pointsPrepare, Stmt.run, Expr.eval, Function.update,
        DerivedCall.view, State.restrict] using hmod
    · simpa [pointsPrepare, Stmt.run, Expr.eval, Function.update,
        DerivedCall.view, State.restrict] using he
  have hr := GridRecovery.points_zero_recovery h hh s.1
    (DerivedCall.view (by decide) (by decide) (pointsPrepare.run st).1) hc
    (by simpa [pointsPrepare, Stmt.run, Expr.eval, Function.update,
      DerivedCall.view, State.restrict] using hx)
  rw [← DerivedCall.call_result (by decide) (by decide) GridRecovery.points
    (pointsPrepare.run st).1] at hr
  change ((DerivedCall.call (by decide) (by decide) GridRecovery.points).run
    (pointsPrepare.run st).1).1.lists 15 = _ ∧
    ((DerivedCall.call (by decide) (by decide) GridRecovery.points).run
    (pointsPrepare.run st).1).1.lists 16 = _ at hr
  rw [show DerivedCall.call (by decide) (by decide) GridRecovery.points = pointsCall by
    unfold pointsCall; rfl] at hr
  generalize hu : (pointsCall.run (pointsPrepare.run st).1).1 = u at *
  simp only [points, run_seq_fst, hu, run_copy_fst]
  constructor
  · calc _ = u.lists 15 := by simp [Function.update]
         _ = _ := by cases k <;> exact hr.1
  · calc _ = u.lists 16 := by simp [Function.update]
         _ = _ := by cases k <;> exact hr.2

theorem points_reg (st : State 300 112) (i : Fin 300) (hi : 220 ≤ i.val) :
    (points.run st).1.regs i = st.regs i := by
  have hp : (pointsPrepare.run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hb : ∀ j ∈ pointsPrepare.regWrites, j.val < 220 := by decide
    intro hm
    have := hb i hm
    omega
  have hd := DerivedCall.call_reg (by decide) (by decide) GridRecovery.points
    (pointsPrepare.run st).1 i hi
  simpa only [points, run_seq_fst, run_copy_fst, setList_regs, pointsCall] using hd.trans hp

theorem points_list (st : State 300 112) (L : Fin 112) (hL : 96 ≤ L.val)
    (h3 : L ≠ 103) (h4 : L ≠ 104) : (points.run st).1.lists L = st.lists L := by
  have hp : (pointsPrepare.run st).1.lists L = st.lists L := by
    apply run_lists_frame
    have hb : ∀ j ∈ pointsPrepare.listWrites, j.val < 96 := by decide
    intro hm
    have := hb L hm
    omega
  have hd := DerivedCall.call_list (by decide) (by decide) GridRecovery.points
    (pointsPrepare.run st).1 L hL
  simpa only [points, run_seq_fst, run_copy_fst, setList_lists,
    Function.update_of_ne h3, Function.update_of_ne h4, pointsCall] using hd.trans hp

def encodePrepare (src : Fin 112) : Stmt 300 112 :=
  .seq (.copy src 0) (.assign 0 (.var 243))

def encodeCall : Stmt 300 112 := DerivedCall.call (by decide) (by decide) RadixCodec.encode

def encode (src : Fin 112) (dst : Fin 300) : Stmt 300 112 :=
  .seq (encodePrepare src) (.seq encodeCall (.assign dst (.var 2)))

omit [NeZero t] in
theorem encode_run (k : Certificate) (p : k.Point t n) (src : Fin 112) (dst : Fin 300)
    (st : State 300 112) (hb : st.regs 243 = 2 ^ t)
    (hx : st.lists src = List.ofFn (fun i => (fieldEquiv t (k.outer.vector p i)).val)) :
    ((encode src dst).run st).1.regs dst = k.outer.pointCode (fieldEquiv t) p := by
  have h := (RadixCodec.encode_run
    (DerivedCall.view (by decide) (by decide) (encodePrepare src |>.run st).1)).2.1
  rw [← DerivedCall.call_result (by decide) (by decide) RadixCodec.encode
    (encodePrepare src |>.run st).1] at h
  change ((DerivedCall.call (by decide) (by decide) RadixCodec.encode).run
    (encodePrepare src |>.run st).1).1.regs 2 = _ at h
  change ((DerivedCall.call (by decide) (by decide) RadixCodec.encode).run
    (encodePrepare src |>.run st).1).1.regs 2 =
      RadixCodec.value ((encodePrepare src |>.run st).1.regs 0)
        ((encodePrepare src |>.run st).1.lists 0) at h
  have hr : (encodePrepare src |>.run st).1.regs 0 = 2 ^ t := by
    simpa [encodePrepare, Stmt.run, Expr.eval, Function.update] using hb
  have hl : (encodePrepare src |>.run st).1.lists 0 =
      List.ofFn (fun i => (fieldEquiv t (k.outer.vector p i)).val) := by
    simpa [encodePrepare, Stmt.run, Function.update] using hx
  rw [hr, hl, RadixCodec.value_finFunction] at h
  calc _ = ((DerivedCall.call (by decide) (by decide) RadixCodec.encode).run
      (encodePrepare src |>.run st).1).1.regs 2 := by
        simp only [encode, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
          Function.update_self, encodeCall]
       _ = (finFunctionFinEquiv (fun i => fieldEquiv t (k.outer.vector p i))).val := h
       _ = _ := rfl

theorem encode_reg (src : Fin 112) (dst i : Fin 300) (hi : 220 ≤ i.val)
    (hne : i ≠ dst) (st : State 300 112) :
    ((encode src dst).run st).1.regs i = st.regs i := by
  have hp : ((encodePrepare src).run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hb : ∀ j ∈ (encodePrepare src).regWrites, j.val < 220 := by
      simp [encodePrepare, Stmt.regWrites]
    intro hm
    have := hb i hm
    omega
  have hd := DerivedCall.call_reg (by decide) (by decide) RadixCodec.encode
    (encodePrepare src |>.run st).1 i hi
  simpa only [encode, run_seq_fst, run_assign_fst, setReg_regs,
    Function.update_of_ne hne, encodeCall] using hd.trans hp

theorem encode_list (src L : Fin 112) (dst : Fin 300) (hL : 96 ≤ L.val)
    (st : State 300 112) : ((encode src dst).run st).1.lists L = st.lists L := by
  have hp : ((encodePrepare src).run st).1.lists L = st.lists L := by
    apply run_lists_frame
    have hb : ∀ j ∈ (encodePrepare src).listWrites, j.val < 96 := by
      simp [encodePrepare, Stmt.listWrites]
    intro hm
    have := hb L hm
    omega
  have hd := DerivedCall.call_list (by decide) (by decide) RadixCodec.encode
    (encodePrepare src |>.run st).1 L hL
  simpa only [encode, run_seq_fst, run_assign_fst, setReg_lists, encodeCall] using hd.trans hp

end PCP.Lang.DerivedSeed
