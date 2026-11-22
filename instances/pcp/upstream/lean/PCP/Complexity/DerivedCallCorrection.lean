import PCP.Complexity.DerivedCallState

/-! # Each complete numeric corrected certificate call in the derived check -/

namespace PCP.Lang.DerivedCall

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t] [NeZero m]

-- Fixed loading copies range over 300 registers.
set_option maxRecDepth 2048

attribute [local irreducible] NumericCorrection.program

def prepareCorrection (left : Bool) : Stmt 300 112 := .seq (.assign 200 (.var 240)) (
  .seq (.assign 201 (.var 241)) (
  .seq (.assign 202 (.var 242)) (
  .seq (.assign 203 (.var (if left then 248 else 249))) (
  .seq (.assign 208 (.var 243)) (
  .seq (.assign 212 (.var 250)) (
  .seq (.assign 213 (.var 251)) (
  .seq (.assign 214 (.var 252)) (
  .seq (.assign 215 (.var 253)) (
  .seq (.assign 216 (.var 254)) (
  .seq (.assign 217 (.var 255)) (
  .seq (.assign 218 (.var 244)) (
  .seq (.assign 219 (.var (if left then 246 else 247))) (
  .seq (.copy 100 80) (
  .seq (.copy (if left then 103 else 104) 83) (
  .seq (.copy 105 84) (
  .seq (.copy 101 85) (
  .seq (.copy 102 86) (
  .seq (.copy 107 87) (
  (.copy 108 88))))))))))))))))))))

def correctionCall (k : Certificate) : Stmt 300 112 :=
  call (by decide) (by decide) (NumericCorrection.program k)

def presentPort (left : Bool) : Fin 300 := if left then 271 else 273

def answerPort (left : Bool) : Fin 300 := if left then 272 else 274

def saveCorrection (left : Bool) : Stmt 300 112 :=
  .seq (.assign (presentPort left) (.var 146))
    (.seq (.assign (answerPort left) (.var 147)) (.seq (.rev 49) (.revApp 49 110)))

def correction (k : Certificate) (left : Bool) : Stmt 300 112 :=
  .seq (prepareCorrection left) (.seq (correctionCall k) (saveCorrection left))

def callValue (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) : Option (ZMod 2) :=
  ComputableDerivedZeroOnGrid.call (BinaryMaterializedField.coordinates t)
    nodes ζ (k.oracle (m := m) qs bs) (k.rows a qs bs) a w s

def callQueries (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) : List ℕ :=
  (ComputableBinaryLocalCorrection.queries (BinaryMaterializedField.coordinates t)
    nodes ζ a s.1 s.2.1 s.2.2.1 w s.2.2.2).map (fun q => queryCode (k.physical a q))

theorem prepareCorrection_frame (left : Bool) (st : State 300 112) :
    Frame st ((prepareCorrection left).run st).1 :=
  frame_of_writes (prepareCorrection left)
    (by cases left <;> decide) (by cases left <;> decide) st

theorem correction_frame (k : Certificate) (left : Bool) (st : State 300 112) :
    Frame st ((correction k left).run st).1 :=
  (prepareCorrection_frame left st).trans
    ((call_frame (by decide) (by decide) (NumericCorrection.program k) _).trans
      (frame_of_writes (saveCorrection left)
        (by cases left <;> decide) (by cases left <;> decide) _))

omit [NeZero m] in
theorem prepareCorrection_run (left : Bool) (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (a b : k.Point t n) (w : Fin t → ZMod 2) (mask : Coefficients t 3)
    (weight : OuterBranch.Field t) (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st) :
    CorrectionContext.Public (m := m) k nodes ζ (if left then a else b) w qs bs
      (view (by decide) (by decide) ((prepareCorrection left).run st).1) ∧
    CorrectionSeed.Input (CorrectionContext.coordinateCodec k n)
      (padCall (if left then first else second))
      (view (by decide) (by decide) ((prepareCorrection left).run st).1) := by
  cases left with
  | false =>
      constructor
      · constructor
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.vertices
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.pairs
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.proper
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.inner
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.affineLabels
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.cubicLabels
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.root
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.secondCode
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.secondPoint
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.label
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.modulus
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.nodes
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.history
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.answers
      · constructor
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.width
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.base
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update, CorrectionContext.coordinateCodec] using hc.dimension
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.secondSeed
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.card
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.empty
  | true =>
      constructor
      · constructor
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.vertices
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.pairs
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.proper
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.inner
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.affineLabels
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.cubicLabels
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.root
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.firstCode
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.firstPoint
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.label
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.modulus
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.nodes
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.history
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.answers
      · constructor
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.width
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.base
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update, CorrectionContext.coordinateCodec] using hc.dimension
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.firstSeed
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.card
        · simpa [view, State.restrict, prepareCorrection, Stmt.run,
            Expr.eval, Function.update] using hc.empty

attribute [local irreducible] correctionCall

theorem correction_reg (k : Certificate) (left : Bool) (st : State 300 112)
    (i : Fin 300) (hi : 240 ≤ i.val) (hp : i ≠ presentPort left) (ha : i ≠ answerPort left) :
    ((correction k left).run st).1.regs i = st.regs i := by
  have hsave : ∀ u : State 300 112, ((saveCorrection left).run u).1.regs i = u.regs i := by
    intro u
    apply run_regs_frame
    simp [saveCorrection, Stmt.regWrites, hp, ha]
  have hprep : ((prepareCorrection left).run st).1.regs i = st.regs i := by
    apply run_regs_frame
    have hbound : ∀ j ∈ (prepareCorrection left).regWrites, j.val < 220 := by
      cases left <;> decide
    intro h
    have := hbound i h
    omega
  have hcall := call_reg (by decide) (by decide) (NumericCorrection.program k)
    ((prepareCorrection left).run st).1 i (by omega)
  simpa only [correction, run_seq_fst, hsave, correctionCall] using hcall.trans hprep

theorem correction_run (left : Bool) (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (a b : k.Point t n) (w : Fin t → ZMod 2) (mask : Coefficients t 3)
    (weight : OuterBranch.Field t) (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (hc : Context k nodes ζ a b w mask weight loc first second qs bs st) :
    let x := if left then a else b
    let seed := if left then first else second
    ((correction k left).run st).1.regs (presentPort left) =
      present (callValue k nodes ζ x w seed qs bs) ∧
    ((correction k left).run st).1.regs (answerPort left) =
      answer (callValue k nodes ζ x w seed qs bs) ∧
    ((correction k left).run st).1.lists 110 =
      (callQueries k nodes ζ x w seed).reverse ++ st.lists 110 ∧
    Frame st ((correction k left).run st).1 := by
  have hp := prepareCorrection_run left k nodes ζ a b w mask weight loc first second qs bs st hc
  have h := NumericCorrection.program_run k nodes ζ (if left then a else b) w
    (if left then first else second) qs bs
    (view (by decide) (by decide) ((prepareCorrection left).run st).1) hp.1 hp.2
  rw [← call_result (by decide) (by decide) (NumericCorrection.program k)] at h
  have hkeep := call_list (by decide) (by decide) (NumericCorrection.program k)
    ((prepareCorrection left).run st).1 110 (by decide)
  have hprep : ((prepareCorrection left).run st).1.lists 110 = st.lists 110 :=
    run_lists_frame _ _ (by cases left <;> decide) st
  rw [show call (by decide) (by decide) (NumericCorrection.program k) = correctionCall k by
    unfold correctionCall; rfl] at h hkeep
  generalize hu : ((correctionCall k).run ((prepareCorrection left).run st).1).1 = u at *
  have hvalue : u.regs 146 = present (callValue k nodes ζ (if left then a else b)
      w (if left then first else second) qs bs) := h.1
  have hanswer : u.regs 147 = answer (callValue k nodes ζ (if left then a else b)
      w (if left then first else second) qs bs) := h.2.1
  have hqueries : u.lists 49 =
      (callQueries k nodes ζ (if left then a else b) w (if left then first else second)).reverse :=
    h.2.2
  have h110 := hkeep.trans hprep
  refine ⟨?_, ?_, ?_, correction_frame k left st⟩
  · cases left <;> simpa [correction, run_seq_fst, hu, saveCorrection, presentPort,
      answerPort, Stmt.run, Expr.eval, Function.update] using hvalue
  · cases left <;> simpa [correction, run_seq_fst, hu, saveCorrection, presentPort,
      answerPort, Stmt.run, Expr.eval, Function.update] using hanswer
  · cases left <;> simp [correction, hu, saveCorrection, presentPort,
      answerPort, Stmt.run, Function.update, hqueries, h110]

end PCP.Lang.DerivedCall
