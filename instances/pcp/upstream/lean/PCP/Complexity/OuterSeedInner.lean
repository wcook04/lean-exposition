import PCP.Complexity.OuterSeedState
import PCP.Complexity.InnerSeedLang
import PCP.Complexity.OuterBranchStandard

set_option maxRecDepth 1024

/-! # Materialize and retain the selected inner seed inside the outer loader -/

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

def loadInner (k : Kind) : Stmt 180 80 := .seq (.assign 120 (.var 160))
  (.seq (.assign 121 (.var 161)) (.seq (.assign 122 (.var 162))
    (.seq (.assign 123 (.const (4+k.tag))) (.seq (.assign 124 (.var 165))
      (.seq (.assign 125 (.var 166)) (.seq (.assign 126 (.var 167))
        (.seq (.assign 127 (.var 168)) (.seq (.assign 128 (.var 169))
          (.seq (.assign 129 (.var 170)) (.seq (.assign 130 (.var 156))
            (.seq (.assign 131 (.var 155)) (.seq (.assign 132 (.var 150))
              (.seq (.copy 64 40) (.seq (.copy 65 41) (.copy 66 42)))))))))))))))

def innerCall : Stmt 180 80 := call (by decide) (by decide) InnerSeed.program

abbrev innerState (st : State 180 80) : State 140 44 :=
  st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))

theorem loadInner_public (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hd : Data k s st) :
    InnerSeed.Public m a (k.line s.1) (innerState ((loadInner k).run st).1) := by
  have hleft := hd 6
  have hright := hd 5
  change st.regs 156 = k.pointCode (fieldEquiv t) s.1.1 at hleft
  change st.regs 155 = k.pointCode (fieldEquiv t) s.1.2 at hright
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [innerState, loadInner, Stmt.run, Expr.eval, Function.update, State.restrict]
      using hp.width
  · simpa [innerState, loadInner, Stmt.run, Expr.eval, Function.update, State.restrict]
      using hp.base
  · simpa [innerState, loadInner, Stmt.run, Expr.eval, Function.update, State.restrict]
      using hp.card
  · intro i
    rw [Kind.line_prefix]
    fin_cases i <;> simp [innerState, loadInner, InnerSeed.prefixPort, Stmt.run,
      Expr.eval, Function.update, State.restrict, hp.vertices, hp.pairs, hp.proper,
      hp.inner, hp.affineLabels, hp.cubicLabels, hleft, hright]
  · simpa [innerState, loadInner, Stmt.run, Function.update, State.restrict] using hp.modulus
  · simpa [innerState, loadInner, Stmt.run, Function.update, State.restrict] using hp.empty
  · simpa [innerState, loadInner, Stmt.run, Function.update, State.restrict] using hp.nodes

theorem loadInner_seed (k : Kind) (s : Sample k t n m) (st : State 180 80)
    (hd : Data k s st) :
    (innerState ((loadInner k).run st).1).regs 132 =
      ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv (innerSeed s)).val := by
  simpa [innerState, loadInner, Stmt.run, Expr.eval, Function.update, State.restrict,
    codes, dataPort] using hd 0

theorem loadInner_regs (k : Kind) : ∀ i ∈ (loadInner k).regWrites, i.val < 140 := by
  cases k <;> decide

theorem loadInner_frame (k : Kind) (st : State 180 80) : Frame st ((loadInner k).run st).1 :=
  frame_of_writes (loadInner k)
    (fun i hi => (loadInner_regs k i hi).trans (by decide)) (by cases k <;> decide) st

theorem loadInner_data (k : Kind) (s : Sample k t n m) (st : State 180 80)
    (hd : Data k s st) : Data k s ((loadInner k).run st).1 := by
  intro i
  have hf : ((loadInner k).run st).1.regs (dataPort i) = st.regs (dataPort i) := by
    apply run_regs_frame
    intro h
    have := loadInner_regs k _ h
    simp only [dataPort] at this
    omega
  exact hf.trans (hd i)

structure InnerStored (k : Kind) (s : Sample k t n m) (st : State 180 80) : Prop where
  coin : st.regs 126 = (innerSeed s).1.toNat
  param : st.regs 127 = (fieldEquiv t (interpolationSeed s).1.2).val
  point : st.regs 138 =
    (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (innerHadPoint s)).val
  base : st.lists 55 = BooleanCoefficientList.encode (innerHadSeed s).base
  auxiliary : st.lists 56 = BooleanCoefficientList.encode (innerHadSeed s).auxiliary
  linear : st.lists 57 = BooleanCoefficientList.encode (innerHadSeed s).linear
  factors : st.lists 58 = HadamardRow.factorCodes (innerHadSeed s)
  left : st.lists 59 = List.ofFn (fun i =>
    (fieldEquiv t (StandardCorrection.vector (interpolationSeed s).1.1.1 i)).val)
  right : st.lists 60 = List.ofFn (fun i =>
    (fieldEquiv t (StandardCorrection.vector (interpolationSeed s).1.1.2 i)).val)
  label : st.lists 61 = List.ofFn (fun i => ((interpolationSeed s).2 i).val)

def saveInner : Stmt 180 80 := .seq (.assign 126 (.var 100))
  (.seq (.assign 127 (.var 104)) (.seq (.assign 138 (.var 119))
    (.seq (.copy 20 55) (.seq (.copy 21 56) (.seq (.copy 22 57)
      (.seq (.copy 23 58) (.seq (.copy 32 59) (.seq (.copy 33 60) (.copy 34 61)))))))))

omit [NeZero t] in
theorem saveInner_run (k : Kind) (s : Sample k t n m) (st : State 180 80)
    (hs : InnerSeed.Stored (innerSeed s) (innerState st))
    (hc : st.regs 100 = (innerSeed s).1.toNat)
    (hz : st.regs 104 = (fieldEquiv t (interpolationSeed s).1.2).val)
    (hx : st.regs 119 =
      (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (innerHadPoint s)).val) :
    InnerStored k s (saveInner.run st).1 := by
  rcases hs with ⟨hh, hl, hr, hw⟩
  constructor
  · simpa [saveInner, Stmt.run, Expr.eval, Function.update] using hc
  · simpa [saveInner, Stmt.run, Expr.eval, Function.update] using hz
  · simpa [saveInner, Stmt.run, Expr.eval, Function.update] using hx
  · simpa [saveInner, Stmt.run, Function.update, innerState, InnerSeed.rowState,
      State.restrict] using hh.2.2.2.1
  · simpa [saveInner, Stmt.run, Function.update, innerState, InnerSeed.rowState,
      State.restrict] using hh.2.2.2.2.1
  · simpa [saveInner, Stmt.run, Function.update, innerState, InnerSeed.rowState,
      State.restrict] using hh.2.2.2.2.2.1
  · simpa [saveInner, Stmt.run, Function.update, innerState, InnerSeed.rowState,
      State.restrict] using hh.2.2.2.2.2.2
  · simpa [saveInner, Stmt.run, Function.update] using hl
  · simpa [saveInner, Stmt.run, Function.update] using hr
  · simpa [saveInner, Stmt.run, Function.update] using hw

theorem saveInner_frame (st : State 180 80) : Frame st (saveInner.run st).1 :=
  frame_of_writes saveInner (by decide) (by decide) st

def inner (k : Kind) : Stmt 180 80 := .seq (loadInner k) (.seq innerCall saveInner)

attribute [local irreducible] InnerSeed.program

theorem inner_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hd : Data k s st) :
    InnerStored k s ((inner k).run st).1 ∧ Public (n := n) (m := m) k a ζ qs bs
      ((inner k).run st).1 ∧ Data k s ((inner k).run st).1 ∧ Frame st ((inner k).run st).1 := by
  have hp' := loadInner_public k a ζ s qs bs st hp hd
  have hd' := loadInner_seed k s st hd
  have hr := InnerSeed.program_run a (k.line s.1) (innerSeed s) _ hp' hd'
  have hv := InnerSeed.program_scalars a (k.line s.1) (innerSeed s) _ hp' hd'
  rw [← call_result (by decide) (by decide) InnerSeed.program ((loadInner k).run st).1] at hr hv
  change _ ∧ InnerSeed.Stored (innerSeed s) (innerState (innerCall.run _).1) ∧ _ at hr
  change (innerCall.run _).1.regs 100 = _ ∧ (innerCall.run _).1.regs 104 = _ ∧
    (innerCall.run _).1.regs 119 = _ at hv
  have hf := (loadInner_frame k st).trans
    ((call_frame (by decide) (by decide) InnerSeed.program _).trans (saveInner_frame _))
  refine ⟨saveInner_run k s _ hr.2.1 hv.1 hv.2.1 hv.2.2, hp.of_frame hf, ?_, hf⟩
  intro i
  have hsave : (saveInner.run (innerCall.run ((loadInner k).run st).1).1).1.regs (dataPort i) =
      (innerCall.run ((loadInner k).run st).1).1.regs (dataPort i) := by
    apply run_regs_frame
    simp only [saveInner, Stmt.regWrites, List.mem_append, List.mem_singleton, List.not_mem_nil,
      or_false, not_or]
    simp [dataPort, Fin.ext_iff]
    omega
  exact hsave.trans ((call_reg (by decide) (by decide) InnerSeed.program _ (dataPort i)
    (by simp only [dataPort]; omega)).trans (loadInner_data k s st hd i))

end PCP.Lang.OuterSeed
