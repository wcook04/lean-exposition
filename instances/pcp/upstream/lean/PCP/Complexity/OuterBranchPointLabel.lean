import PCP.Complexity.OuterBranchPrimary
import PCP.Complexity.HadamardHomogeneousCode

/-!
# The actual outer affine point and homogeneous label

These stages retain the stored sample and histories and work for either primary
row degree. The scalar is read from an arbitrary protected register.
-/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

def loadOuterPoint (src : Fin 180) : Stmt 180 80 :=
  .seq (.copy 40 3) (.seq (.copy 41 7) (.seq (.copy 42 12) (.seq (.copy 43 13)
    (.seq (.assign 26 (.var src)) (.seq (.assign 43 (.var 120)) (.assign 45 (.var 123)))))))

def callOuterPoint : Stmt 180 80 := call (by decide) (by decide) StandardCorrection.scalarPoint

def outerPoint (src : Fin 180) : Stmt 180 80 :=
  .seq (loadOuterPoint src) (.seq callOuterPoint (.assign 145 (.var 59)))

def loadOuterLabel : Stmt 180 80 := .seq (.copy 45 17) (.seq (.copy 41 7)
  (.seq (.assign 20 (.var 120)) (.assign 56 (.var 121))))

def callOuterLabel : Stmt 180 80 := call (by decide) (by decide) HadamardHomogeneousCode.program

def outerLabel : Stmt 180 80 :=
  .seq loadOuterLabel (.seq callOuterLabel (.assign 146 (.var 1)))

attribute [local irreducible] StandardCorrection.scalarPoint HadamardHomogeneousCode.program
  callOuterPoint callOuterLabel

theorem loadOuterPoint_frame (src : Fin 180) (st : State 180 80) :
    Frame st ((loadOuterPoint src).run st).1 :=
  frame_of_writes _ (by simp [loadOuterPoint, Stmt.regWrites])
    (by simp [loadOuterPoint, Stmt.listWrites]) _

theorem loadOuterPoint_input (src : Fin 180) (k : Kind) (a : Fin 5 → Field t)
    (ζ : Field t) (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    StandardCorrection.AffineContext (k.vector s.1.1) (k.vector s.1.2)
      (((loadOuterPoint src).run st).1.restrict (Fin.castLE (by decide))
        (Fin.castLE (by decide))) := by
  simp [loadOuterPoint, StandardCorrection.AffineContext, Stmt.run, Expr.eval,
    State.restrict, Function.update, hc.width, hc.card, hc.modulus, hc.empty, hc.left, hc.right]

theorem outerPoint_run (src : Fin 180) (hsrc : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : st.regs src = (fieldEquiv t α).val) :
    ((outerPoint src).run st).1.regs 145 =
      k.pointCode (fieldEquiv t) (PolynomialLine.point s.1.1 s.1.2 α) ∧
      Frame st ((outerPoint src).run st).1 := by
  have hi := loadOuterPoint_input src k a ζ s qs bs st hc
  have h43 : src ≠ 43 := by intro he; subst src; contradiction
  have h45 : src ≠ 45 := by intro he; subst src; contradiction
  have hx : ((loadOuterPoint src).run st).1.regs 26 = (fieldEquiv t α).val := by
    simpa [loadOuterPoint, Stmt.run, Expr.eval, Function.update, h43, h45] using ha
  have hp := StandardCorrection.scalarPoint_run α (k.vector s.1.1) (k.vector s.1.2) _ hi hx
  have hr := call_result (by decide) (by decide) StandardCorrection.scalarPoint
    ((loadOuterPoint src).run st).1
  rw [← hr] at hp
  have hf := call_frame (by decide) (by decide) StandardCorrection.scalarPoint
    ((loadOuterPoint src).run st).1
  have ht := frame_of_writes (.assign 145 (.var 59)) (by decide) (by decide)
    (callOuterPoint.run ((loadOuterPoint src).run st).1).1
  simp only [outerPoint, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self]
  constructor
  · simpa only [callOuterPoint, State.restrict_regs, Kind.pointCode, Kind.vector_point,
      Function.comp_def,
      show Fin.castLE (by decide : 80 ≤ 180) (59 : Fin 80) = (59 : Fin 180) from rfl] using hp
  · simpa only [callOuterPoint, run_assign_fst, Expr.eval] using
      (loadOuterPoint_frame src st).trans (hf.trans (by
        simpa only [callOuterPoint, run_assign_fst, Expr.eval] using ht))

theorem outerPoint_reg (src i : Fin 180) (hi : 120 ≤ i.val) (hj : i ≠ 145)
    (st : State 180 80) : ((outerPoint src).run st).1.regs i = st.regs i := by
  have hl : i ∉ (loadOuterPoint src).regWrites := by
    intro hm
    have hb : ∀ j ∈ (loadOuterPoint src).regWrites, j.val < 120 := by
      simp [loadOuterPoint, Stmt.regWrites]
    have := hb i hm
    omega
  have hc := call_reg (by decide) (by decide) StandardCorrection.scalarPoint
    ((loadOuterPoint src).run st).1 i hi
  simp only [outerPoint, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_of_ne hj]
  simpa only [callOuterPoint] using hc.trans (run_regs_frame _ _ hl st)

theorem outerPoint_queries (src : Fin 180) (st : State 180 80) :
    ((outerPoint src).run st).1.lists 49 = st.lists 49 := by
  have hc := call_list (by decide) (by decide) StandardCorrection.scalarPoint
    ((loadOuterPoint src).run st).1 49 (by decide)
  have hl := run_lists_frame (loadOuterPoint src) 49 (by simp [loadOuterPoint, Stmt.listWrites]) st
  simp only [outerPoint, run_seq_fst, run_assign_fst, Expr.eval, setReg_lists]
  simpa only [callOuterPoint] using hc.trans hl

theorem loadOuterLabel_frame (st : State 180 80) : Frame st (loadOuterLabel.run st).1 :=
  frame_of_writes _ (by decide) (by decide) _

theorem outerLabel_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) :
    (outerLabel.run st).1.regs 146 =
      HadamardLabel.code (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2) ∧
      Frame st (outerLabel.run st).1 := by
  have ht : (loadOuterLabel.run st).1.regs 20 = t := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.width
  have hd : (loadOuterLabel.run st).1.regs 56 = k.degree := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.degree
  have he : (loadOuterLabel.run st).1.lists 7 = [] := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.empty
  have hw : (loadOuterLabel.run st).1.lists 17 = List.ofFn (fun i => (s.2.2.1.2 i).val) := by
    simpa [loadOuterLabel, Stmt.run, Expr.eval, Function.update] using hc.label
  have hp := HadamardHomogeneousCode.program_run k.degree_pos s.2.2.1.2
    ((loadOuterLabel.run st).1.restrict (Fin.castLE (by decide : 80 ≤ 180))
      (Fin.castLE (by decide : 32 ≤ 80)))
    (by simpa only [State.restrict_regs,
      show Fin.castLE (by decide : 80 ≤ 180) (20 : Fin 80) = (20 : Fin 180) from rfl] using ht)
    (by simpa only [State.restrict_regs,
      show Fin.castLE (by decide : 80 ≤ 180) (56 : Fin 80) = (56 : Fin 180) from rfl] using hd)
    (by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 32 ≤ 80) (7 : Fin 32) = (7 : Fin 80) from rfl] using he)
    (by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 32 ≤ 80) (17 : Fin 32) = (17 : Fin 80) from rfl] using hw)
  have hr := call_result (by decide) (by decide) HadamardHomogeneousCode.program
    (loadOuterLabel.run st).1
  rw [← hr] at hp
  have hf := call_frame (by decide) (by decide) HadamardHomogeneousCode.program
    (loadOuterLabel.run st).1
  have hf' := frame_of_writes (.assign 146 (.var 1)) (by decide) (by decide)
    (callOuterLabel.run (loadOuterLabel.run st).1).1
  simp only [outerLabel, run_seq_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_self]
  constructor
  · simpa only [callOuterLabel, State.restrict_regs,
      show Fin.castLE (by decide : 80 ≤ 180) (1 : Fin 80) = (1 : Fin 180) from rfl] using hp.1
  · simpa only [callOuterLabel, run_assign_fst, Expr.eval] using
      (loadOuterLabel_frame st).trans (hf.trans (by
        simpa only [callOuterLabel, run_assign_fst, Expr.eval] using hf'))

theorem outerLabel_reg (i : Fin 180) (hi : 120 ≤ i.val) (hj : i ≠ 146)
    (st : State 180 80) : (outerLabel.run st).1.regs i = st.regs i := by
  have hl : i ∉ loadOuterLabel.regWrites := by
    intro hm
    have hb : ∀ j ∈ loadOuterLabel.regWrites, j.val < 120 := by decide
    have := hb i hm
    omega
  have hc := call_reg (by decide) (by decide) HadamardHomogeneousCode.program
    (loadOuterLabel.run st).1 i hi
  simp only [outerLabel, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_of_ne hj]
  simpa only [callOuterLabel] using hc.trans (run_regs_frame _ _ hl st)

theorem outerLabel_queries (st : State 180 80) : (outerLabel.run st).1.lists 49 = st.lists 49 := by
  have hc := call_list (by decide) (by decide) HadamardHomogeneousCode.program
    (loadOuterLabel.run st).1 49 (by decide)
  have hl := run_lists_frame loadOuterLabel 49 (by decide) st
  simp only [outerLabel, run_seq_fst, run_assign_fst, Expr.eval, setReg_lists]
  simpa only [callOuterLabel] using hc.trans hl

end PCP.Lang.OuterBranch
