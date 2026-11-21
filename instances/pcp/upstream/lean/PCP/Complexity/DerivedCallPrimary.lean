import PCP.Complexity.DerivedCallState

/-! # The actual masked primary read inside a complete derived-grid check -/

namespace PCP.Lang.DerivedCall

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

set_option maxRecDepth 2048

attribute [local irreducible] DerivedPrimary.program

def preparePrimary : Stmt 300 112 := .seq (.assign 98 (.var 240)) (
  .seq (.assign 99 (.var 245)) (
  .seq (.assign 80 (.var 260)) (
  .seq (.assign 81 (.var 261)) (
  .seq (.assign 82 (.var 262)) (
  .seq (.assign 83 (.var 263)) (
  .seq (.assign 84 (.var 264)) (
  .seq (.assign 85 (.var 265)) (
  .seq (.assign 86 (.var 266)) (
  .seq (.assign 87 (.var 267)) (
  .seq (.assign 88 (.var 268)) (
  .seq (.assign 89 (.var 269)) (
  .seq (.copy 105 20) (
  .seq (.copy 106 21) (
  .seq (.copy 101 22) (
  .seq (.copy 100 23) (
  .seq (.copy 107 30) (
  .seq (.copy 108 31) (
  (.copy 100 27)))))))))))))))))))

def primaryCall (weighted : Bool) : Stmt 300 112 :=
  call (by decide) (by decide) (DerivedPrimary.program weighted)

def savePrimary : Stmt 300 112 := .seq (.assign 270 (.var 8))
  (.seq (.copy 100 110) (.revApp 26 110))

def primary (weighted : Bool) : Stmt 300 112 :=
  .seq preparePrimary (.seq (primaryCall weighted) savePrimary)

def primaryLabel (weighted : Bool) (weight : OuterBranch.Field t) (w : Fin t → ZMod 2) :=
  BinaryCubicQueryLang.translated weighted weight
    (BooleanCoefficientArithmetic.homogeneousIndex (le_refl 1) w)

def primaryQueries (weighted : Bool) (weight : OuterBranch.Field t) (w : Fin t → ZMod 2)
    (mask : Coefficients t 3) (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3) : List ℕ :=
  [queryCode (loc.query (primaryLabel weighted weight w + mask)), queryCode (loc.query mask)]

def primaryBit (weighted : Bool) (weight : OuterBranch.Field t) (w : Fin t → ZMod 2)
    (mask : Coefficients t 3) (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (qs : List ℕ) (bs : List Bool) : ZMod 2 :=
  Hadamard.selfCorrect (fun p => BinarySeedPadding.boolEquiv
    (QueryTree.answersOracle qs bs (queryCode (loc.query p))))
    (primaryLabel weighted weight w) mask

theorem preparePrimary_frame (st : State 300 112) : Frame st (preparePrimary.run st).1 :=
  frame_of_writes preparePrimary (by decide) (by decide) st

theorem primary_frame (weighted : Bool) (st : State 300 112) :
    Frame st ((primary weighted).run st).1 := by
  exact (preparePrimary_frame st).trans
    ((call_frame (by decide) (by decide) (DerivedPrimary.program weighted) _).trans
      (frame_of_writes savePrimary (by decide) (by decide) _))

theorem preparePrimary_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a b : k.Point t n) (w : Fin t → ZMod 2)
    (mask : Coefficients t 3) (weight : OuterBranch.Field t)
    (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st) :
    DerivedPrimary.Context weight w mask (view (by decide) (by decide) (preparePrimary.run st).1) ∧
    HadamardRow.Payload (loc.payload (t := t) (fieldEquiv t))
      (view (by decide) (by decide) (preparePrimary.run st).1) ∧
    (preparePrimary.run st).1.lists 30 = qs ∧
    (preparePrimary.run st).1.lists 31 = bs.map Bool.toNat := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [view, State.restrict, preparePrimary, Stmt.run, Expr.eval, Function.update]
      using hc.width
  · simpa [view, State.restrict, preparePrimary, Stmt.run, Expr.eval, Function.update]
      using hc.weight
  · simpa [view, State.restrict, preparePrimary, Stmt.run, Function.update] using hc.label
  · simpa [view, State.restrict, preparePrimary, Stmt.run, Function.update] using hc.mask
  · simpa [view, State.restrict, preparePrimary, Stmt.run, Function.update] using hc.modulus
  · simpa [view, State.restrict, preparePrimary, Stmt.run, Function.update] using hc.empty
  · intro i
    have h := hc.payload i
    fin_cases i <;>
      simpa [HadamardRow.payloadReg, payloadPort, view, State.restrict, preparePrimary,
        Stmt.run, Expr.eval, Function.update] using h
  · simpa [preparePrimary, Stmt.run, Function.update] using hc.history
  · simpa [preparePrimary, Stmt.run, Function.update] using hc.answers

attribute [local irreducible] primaryCall

theorem primary_run (weighted : Bool) (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a b : k.Point t n) (w : Fin t → ZMod 2)
    (mask : Coefficients t 3) (weight : OuterBranch.Field t)
    (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st) :
    ((primary weighted).run st).1.regs 270 = (primaryBit weighted weight w mask loc qs bs).val ∧
    ((primary weighted).run st).1.lists 110 = (primaryQueries weighted weight w mask loc).reverse ∧
    Frame st ((primary weighted).run st).1 := by
  have hp := preparePrimary_run k nodes ζ a b w mask weight loc first second qs bs st hc
  have h := DerivedPrimary.program_location weighted weight w mask loc qs bs
    (view (by decide) (by decide) (preparePrimary.run st).1) hp.1 hp.2.1
    (by simpa [view, State.restrict] using hp.2.2.1)
    (by simpa [view, State.restrict] using hp.2.2.2)
  rw [← call_result (by decide) (by decide) (DerivedPrimary.program weighted)] at h
  have he := (call_list (by decide) (by decide) (DerivedPrimary.program weighted)
    (preparePrimary.run st).1 100 (by decide)).trans
      ((preparePrimary_frame st).lists 100 (by decide) (by decide) |>.trans hc.empty)
  rw [show call (by decide) (by decide) (DerivedPrimary.program weighted) = primaryCall weighted by
    unfold primaryCall; rfl] at h he
  generalize hu : ((primaryCall weighted).run (preparePrimary.run st).1).1 = u at *
  have hq : u.lists 26 = primaryQueries weighted weight w mask loc := h.1
  have hv : u.regs 8 = (primaryBit weighted weight w mask loc qs bs).val := h.2
  refine ⟨?_, ?_, primary_frame weighted st⟩
  · simpa [primary, run_seq_fst, hu, savePrimary, Stmt.run, Expr.eval, Function.update] using hv
  · simp [primary, hu, savePrimary, Stmt.run, Function.update, he, hq]

end PCP.Lang.DerivedCall
