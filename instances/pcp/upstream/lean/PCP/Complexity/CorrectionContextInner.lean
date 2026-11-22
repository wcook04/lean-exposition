import PCP.Complexity.CorrectionContextState

/-! # Loading both inner selector arms inside a numeric correction context -/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection

variable {t n m : ℕ} [NeZero t]

-- Fixed copied payloads range over the 220-register layout.
set_option maxRecDepth 2048

def prepareInner (k : Certificate) : Stmt 220 96 := .seq (.assign 120 (.var 200)) (
    .seq (.assign 121 (.var 201)) (
    .seq (.assign 122 (.var 208)) (
    .seq (.assign 123 (.const (k.outer.tag+4))) (
    .seq (.assign 124 (.var 212)) (
    .seq (.assign 125 (.var 213)) (
    .seq (.assign 126 (.var 214)) (
    .seq (.assign 127 (.var 215)) (
    .seq (.assign 128 (.var 216)) (
    .seq (.assign 129 (.var 217)) (
    .seq (.assign 130 (.var 219)) (
    .seq (.assign 131 (.var 207)) (
    .seq (.assign 132 (.var 204)) (
    .seq (.copy 85 40) (
    .seq (.copy 80 41) ((.copy 86 42))))))))))))))))

def inner : Stmt 220 96 := CorrectionSeed.call (by decide) (by decide) InnerSeed.program

theorem inner_result (st : State 220 96) :
    (innerState (inner.run st).1, (inner.run st).2) = InnerSeed.program.run (innerState st) :=
  CorrectionSeed.call_result (by decide) (by decide) InnerSeed.program st

attribute [local irreducible] inner InnerSeed.program

def materializeInner (k : Certificate) : Stmt 220 96 := .seq (prepareInner k) inner

theorem prepareInner_frame (k : Certificate) (st : State 220 96) :
    Frame st ((prepareInner k).run st).1 :=
  frame_of_writes (prepareInner k) (by simp [prepareInner, Stmt.regWrites])
    (by simp [prepareInner, Stmt.listWrites]) st

theorem inner_frame (st : State 220 96) : Frame st (inner.run st).1 :=
  ⟨fun i hi => by
    simpa only [inner] using
      CorrectionSeed.call_reg (by decide) (by decide) InnerSeed.program st i hi,
    fun L hL => by
      simpa only [inner] using
        CorrectionSeed.call_list (by decide) (by decide) InnerSeed.program st L hL⟩

theorem materializeInner_frame (k : Certificate) (st : State 220 96) :
    Frame st ((materializeInner k).run st).1 :=
  (prepareInner_frame k st).trans (inner_frame _)

theorem prepareInner_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st) (hl : Loaded k s st) :
    InnerSeed.Public m nodes (k.outer.line (a, s.1)) (innerState ((prepareInner k).run st).1) ∧
      (innerState ((prepareInner k).run st).1).regs 132 =
        ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.2).val := by
  have hr : st.regs 207 = k.outer.pointCode (fieldEquiv t) s.1 :=
    hl.data.outer.trans (pointCode_eq k s.1)
  constructor
  · constructor
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using hl.input.width
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using hl.input.base
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update]
        using hl.input.card
    · intro i
      cases k <;> fin_cases i <;>
        simp [InnerSeed.prefixPort, innerState, State.restrict, prepareInner, Stmt.run,
          Expr.eval, Function.update, StandardCorrection.Site.prefix, Certificate.outer,
          OuterBranch.Kind.line, OuterBranch.Kind.tag, hp.vertices, hp.pairs, hp.proper,
          hp.inner, hp.affineLabels, hp.cubicLabels, hp.pointCode, hr,
          OuterBranch.Kind.pointCode, OuterBranch.Kind.vector, OuterBranch.Kind.coordinateEquiv,
          ThreeColorQueryIndex.pairIndex, ThreeColorQueryIndex.properIndex,
          ThreeColorQueryIndex.tupleIndex, Equiv.arrowCongr, Function.comp_def] <;> rfl
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Function.update] using hp.modulus
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Function.update]
        using hl.input.empty
    · simpa [innerState, State.restrict, prepareInner, Stmt.run, Function.update] using hp.nodes
  · simpa [innerState, State.restrict, prepareInner, Stmt.run, Expr.eval, Function.update, padCall]
      using hl.data.inner

theorem materializeInner_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st) (hl : Loaded k s st) :
    InnerSeed.Stored s.2.2.2 (innerState ((materializeInner k).run st).1) ∧
    ((materializeInner k).run st).1.regs 100 = s.2.2.2.1.toNat ∧
    ((materializeInner k).run st).1.regs 104 = (fieldEquiv t s.2.2.2.2.2.1.2).val ∧
    ((materializeInner k).run st).1.regs 119 =
      (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 s.2.2.2.2.1.1).val ∧
    Frame st ((materializeInner k).run st).1 := by
  have hi := prepareInner_run k nodes ζ a w s qs bs st hp hl
  have hs := InnerSeed.program_run nodes (k.outer.line (a,s.1)) s.2.2.2
    (innerState ((prepareInner k).run st).1) hi.1 hi.2
  have hv := InnerSeed.program_scalars nodes (k.outer.line (a,s.1)) s.2.2.2
    (innerState ((prepareInner k).run st).1) hi.1 hi.2
  rw [← inner_result] at hs hv
  refine ⟨?_, ?_, ?_, ?_, materializeInner_frame k st⟩
  · simpa only [materializeInner, run_seq_fst] using hs.2.1
  · exact hv.1
  · exact hv.2.1
  · exact hv.2.2

end PCP.Lang.CorrectionContext
