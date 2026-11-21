import PCP.Complexity.CorrectionContextInner

/-! # Final protected port assembly of an actual correction call -/

namespace PCP.Lang.CorrectionContext

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection

variable {t n m : ℕ} [NeZero t]

-- The terminal loader is a fixed sequence of scalar and list copies.
set_option maxRecDepth 4096

def finalize (k : Certificate) : Stmt 220 96 := .seq (.assign 120 (.var 200)) (
  .seq (.assign 121 (.const 1)) (
  .seq (.assign 122 (.var 201)) (
  .seq (.assign 123 (.var 208)) (
  .seq (.assign 124 (.var 218)) (
  .seq (.assign 125 (.var 206)) (
  .seq (.assign 126 (.var 100)) (
  .seq (.assign 127 (.var 104)) (
  .seq (.assign 128 (.var 202)) (
  .seq (.assign 129 (.const k.outer.tag)) (
  .seq (.assign 130 (.var 212)) (
  .seq (.assign 131 (.var 213)) (
  .seq (.assign 132 (.var 214)) (
  .seq (.assign 133 (.var 215)) (
  .seq (.assign 134 (.var 216)) (
  .seq (.assign 135 (.var 217)) (
  .seq (.assign 136 (.var 219)) (
  .seq (.assign 137 (.var 207)) (
  .seq (.assign 138 (.var 119)) (
  .seq (.copy 85 40) (
  .seq (.copy 80 41) (
  .seq (.copy 83 42) (
  .seq (.copy 81 43) (
  .seq (.copy 82 44) (
  .seq (.copy 84 45) (
  .seq (.copy 86 46) (
  .seq (.copy 87 47) (
  .seq (.copy 88 48) (
  .seq (.copy 20 50) (
  .seq (.copy 21 51) (
  .seq (.copy 22 52) (
  .seq (.copy 23 53) (
  .seq (.copy 20 55) (
  .seq (.copy 21 56) (
  .seq (.copy 22 57) (
  .seq (.copy 23 58) (
  .seq (.copy 32 59) (
  .seq (.copy 33 60) (
  (.copy 34 61)))))))))))))))))))))))))))))))))))))))

theorem finalize_frame (k : Certificate) (st : State 220 96) :
    Frame st ((finalize k).run st).1 :=
  frame_of_writes (finalize k) (by simp [finalize, Stmt.regWrites])
    (by simp [finalize, Stmt.listWrites]) st

set_option maxHeartbeats 800000 in
-- Both certificate constructors copy 39 fixed semantic source fields.
theorem finalize_run (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a : k.Point t n) (w : Fin t → ZMod 2)
    (s : k.Seed t n m) (qs : List ℕ) (bs : List Bool) (st : State 220 96)
    (hp : Public (m := m) k nodes ζ a w qs bs st) (hl : Loaded k s st)
    (hs : InnerSeed.Stored s.2.2.2 (innerState st))
    (hcoin : st.regs 100 = s.2.2.2.1.toNat)
    (hz : st.regs 104 = (fieldEquiv t s.2.2.2.2.2.1.2).val)
    (hx : st.regs 119 =
      (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 s.2.2.2.2.1.1).val) :
    OuterBranch.Context k.outer nodes ζ (k.sample a w s) qs bs
      (outerState ((finalize k).run st).1) := by
  have hr : st.regs 207 = k.outer.pointCode (fieldEquiv t) s.1 :=
    hl.data.outer.trans (pointCode_eq k s.1)
  rcases hs.hadamard with ⟨_, _, _, hb, ha, hlin, hf⟩
  have hlft := hs.left
  have hrgt := hs.right
  have hlabel := hs.label
  simp only [InnerSeed.rowState, innerState, State.restrict_lists] at hb ha hlin hf hlft hrgt hlabel
  have hparam : st.regs 206 = (fieldEquiv t (s.2.1 : OuterBranch.Field t)).val := hl.data.param
  have hdim : st.regs 202 = k.outer.dimension n := hl.input.dimension
  cases k with
  | valid =>
      constructor
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.width
      · simp [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, OuterBranch.Kind.degree]
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.base
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.card
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.root
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hparam
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hcoin
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hz
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hdim
      · simp [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer]
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.vertices
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.pairs
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.proper
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.inner
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.affineLabels
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.cubicLabels
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.pointCode
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hr
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hx
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.modulus
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.empty
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.point
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.outer
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.direction
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.label
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.nodes
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.history
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.answers
      · calc
          _ = st.lists 20 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := hb
      · calc
          _ = st.lists 21 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := ha
      · calc
          _ = st.lists 22 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := hlin
      · calc
          _ = st.lists 23 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := hf
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hb
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using ha
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hlin
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hf
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hlft
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hrgt
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hlabel
  | proper =>
      constructor
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.width
      · simp [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, OuterBranch.Kind.degree]
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.base
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.card
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.root
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hparam
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hcoin
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hz
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hdim
      · simp [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer]
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.vertices
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.pairs
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.proper
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.inner
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.affineLabels
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.cubicLabels
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.pointCode
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hr
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hx
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.modulus
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.input.empty
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.point
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.outer
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hl.direction
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.label
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.nodes
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.history
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hp.answers
      · calc
          _ = st.lists 20 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := hb
      · calc
          _ = st.lists 21 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := ha
      · calc
          _ = st.lists 22 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := hlin
      · calc
          _ = st.lists 23 := by
            simp [outerState, State.restrict, finalize, Stmt.run, Function.update]
          _ = _ := hf
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hb
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using ha
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hlin
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hf
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hlft
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hrgt
      · simpa [outerState, State.restrict, finalize, Stmt.run, Expr.eval, Function.update,
          Certificate.outer, Certificate.sample, OuterBranch.primarySeed] using hlabel

end PCP.Lang.CorrectionContext
