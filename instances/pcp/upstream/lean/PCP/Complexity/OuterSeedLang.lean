import PCP.Complexity.OuterSeedMaterialize
import PCP.Complexity.OuterSeedDecode

/-! # Complete actual outer seed loader -/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

def finalize (k : Kind) : Stmt 180 80 := .seq (.copy 65 54) (
  .seq (.assign 120 (.var 160)) (
  .seq (.assign 121 (.const k.degree)) (
  .seq (.assign 122 (.var 161)) (
  .seq (.assign 123 (.var 162)) (
  .seq (.assign 124 (.var 163)) (
  .seq (.assign 125 (.var 154)) (
  .seq (.assign 128 (.var 164)) (
  .seq (.assign 129 (.const k.tag)) (
  .seq (.assign 130 (.var 165)) (
  .seq (.assign 131 (.var 166)) (
  .seq (.assign 132 (.var 167)) (
  .seq (.assign 133 (.var 168)) (
  .seq (.assign 134 (.var 169)) (
  .seq (.assign 135 (.var 170)) (
  .seq (.assign 136 (.var 156)) (
  .seq (.assign 137 (.var 155)) (
  .seq (.copy 64 40) (
  .seq (.copy 65 41) (
  .seq (.copy 66 46) (
  .seq (.copy 67 47) (
  (.copy 68 48)))))))))))))))))))))
)

theorem finalize_frame (k : Kind) (st : State 180 80) : Frame st ((finalize k).run st).1 :=
  frame_of_writes (finalize k) (by cases k <;> decide) (by cases k <;> decide) st

theorem finalize_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hd : Data k s st) (hs : Stored k s st) :
    OuterBranch.Context k a ζ s qs bs ((finalize k).run st).1 := by
  constructor
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.width
  · simp [finalize, Stmt.run, Expr.eval, Function.update]
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.base
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.card
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.root
  · simpa [finalize, Stmt.run, Expr.eval, Function.update, dataPort, codes] using hd 4
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.coin
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.param
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.dimension
  · simp [finalize, Stmt.run, Expr.eval, Function.update]
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.vertices
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.pairs
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.proper
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.inner
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.affineLabels
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.cubicLabels
  · simpa [finalize, Stmt.run, Expr.eval, Function.update, dataPort, codes] using hd 6
  · simpa [finalize, Stmt.run, Expr.eval, Function.update, dataPort, codes] using hd 5
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.point
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.modulus
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.empty
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.left
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.right
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.direction
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.label
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.nodes
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.history
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hp.answers
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.primary.base
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.primary.auxiliary
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.primary.linear
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.primary.factors
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.base
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.auxiliary
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.linear
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.factors
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.left
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.right
  · simpa [finalize, Stmt.run, Expr.eval, Function.update] using hs.inner.label

def program (k : Kind) : Stmt 180 80 :=
  .seq (unpack k) (.seq (inner k) (.seq (materialize k) (finalize k)))

attribute [local irreducible] unpack inner materialize finalize

/-- All branch work arrays are generated from the actual numeric sampler code. -/
theorem program_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st)
    (hc : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    OuterBranch.Context k a ζ s qs bs ((program k).run st).1 ∧
      Public (n := n) (m := m) k a ζ qs bs ((program k).run st).1 ∧
      Frame st ((program k).run st).1 := by
  have hu := unpack_run k a ζ s qs bs st hp hc
  simp only [program, run_seq_fst]
  generalize hs : ((unpack k).run st).1 = u at *
  have hi := inner_run k a ζ s qs bs u hu.2.1 hu.1
  generalize ht : ((inner k).run u).1 = v at *
  have hm := materialize_run k a ζ s qs bs v hi.2.1 hi.2.2.1 hi.1
  generalize hv : ((materialize k).run v).1 = w at *
  exact ⟨finalize_run k a ζ s qs bs w hm.2.2.1 hm.2.1 hm.1,
    hm.2.2.1.of_frame (finalize_frame k w),
    hu.2.2.trans (hi.2.2.2.trans (hm.2.2.2.trans (finalize_frame k w)))⟩


/-- The unused protected list is initialized, so arbitrary scratch data cannot affect bounds. -/
theorem program_list54 (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st)
    (hc : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ((program k).run st).1.lists 54 = [] := by
  have he := (program_run k a ζ s qs bs st hp hc).2.1.empty
  have hf (u : State 180 80) : ((finalize k).run u).1.lists 54 =
      ((finalize k).run u).1.lists 65 := by
    simp [finalize, Stmt.run, Function.update]
  simp only [program, run_seq_fst] at he ⊢
  exact (hf _).trans he

end PCP.Lang.OuterSeed
