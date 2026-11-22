import PCP.Complexity.OuterSeedInner

/-! # Materialize the outer row words and sampled affine coordinates -/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

structure PrimaryStored (k : Kind) (s : Sample k t n m) (st : State 180 80) : Prop where
  base : st.lists 50 = BooleanCoefficientList.encode (primarySeed s).base
  auxiliary : st.lists 51 = BooleanCoefficientList.encode (primarySeed s).auxiliary
  linear : st.lists 52 = BooleanCoefficientList.encode (primarySeed s).linear
  factors : st.lists 53 = HadamardRow.factorCodes (primarySeed s)

def hadPrepare : Stmt 180 80 := .seq (.assign 20 (.var 160))
  (.seq (.copy 65 7) (.assign 96 (.var 151)))

def hadCall (k : Kind) : Stmt 180 80 := call (by decide) (by decide) (HadamardSeed.program k.degree)

def hadSave : Stmt 180 80 := .seq (.copy 20 50)
  (.seq (.copy 21 51) (.seq (.copy 22 52) (.copy 23 53)))

def hadamard (k : Kind) : Stmt 180 80 := .seq hadPrepare (.seq (hadCall k) hadSave)

attribute [local irreducible] HadamardSeed.program hadCall

theorem hadamard_run (k : Kind) (s : Sample k t n m) (st : State 180 80)
    (ht : st.regs 160 = t) (he : st.lists 65 = []) (hd : Data k s st) :
    PrimaryStored k s ((hadamard k).run st).1 := by
  have hs : st.regs 151 = ((hadamardCodec t k.degree).equiv (primarySeed s)).val := hd 1
  have h := HadamardSeed.program_run (primarySeed s)
    ((hadPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using ht)
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using he)
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hs)
  rw [← call_result (by decide) (by decide) (HadamardSeed.program k.degree)] at h
  rw [show call (by decide) (by decide) (HadamardSeed.program k.degree) = hadCall k by
    unfold hadCall; rfl] at h
  generalize hu : ((hadCall k).run (hadPrepare.run st).1).1 = u at *
  rcases h with ⟨_, _, _, hb, ha, hl, hf⟩
  simp only [hadamard, run_seq_fst, hu]
  constructor
  · simpa [hadSave, Stmt.run, Function.update, State.restrict] using hb
  · simpa [hadSave, Stmt.run, Function.update, State.restrict] using ha
  · simpa [hadSave, Stmt.run, Function.update, State.restrict] using hl
  · simpa [hadSave, Stmt.run, Function.update, State.restrict] using hf

structure HadFrame (st out : State 180 80) : Prop where
  regs : ∀ i : Fin 180, 100 ≤ i.val → out.regs i = st.regs i
  lists : ∀ i : Fin 80, 54 ≤ i.val → out.lists i = st.lists i

theorem hadamard_frame (k : Kind) (st : State 180 80) : HadFrame st ((hadamard k).run st).1 := by
  constructor
  · intro i hi
    simp only [hadamard, run_seq_fst, hadSave, run_copy_fst, setList_regs]
    unfold hadCall
    rw [call_reg (by decide) (by decide) (HadamardSeed.program k.degree) _ i hi]
    apply run_regs_frame
    simp only [hadPrepare, Stmt.regWrites, List.mem_append, List.mem_singleton,
      List.not_mem_nil, false_or]
    intro h
    rcases h with h | h
    all_goals have hh := congrArg Fin.val h; omega
  · intro i hi
    have hsave := run_lists_frame hadSave i (by
      simp only [hadSave, Stmt.listWrites, List.mem_append, List.mem_singleton]
      intro h
      rcases h with h | h | h | h
      all_goals have hh := congrArg Fin.val h; omega)
    simp only [hadamard, run_seq_fst, hsave]
    unfold hadCall
    rw [call_list (by decide) (by decide) (HadamardSeed.program k.degree) _ i (by omega)]
    apply run_lists_frame
    simp only [hadPrepare, Stmt.listWrites, List.mem_append, List.not_mem_nil,
      List.mem_singleton, false_or, or_false]
    intro h
    have := congrArg Fin.val h
    omega

theorem HadFrame.public {st out : State 180 80} (h : HadFrame st out) : Frame st out :=
  ⟨fun i hi => h.regs i (by omega), fun i hi => h.lists i (by omega)⟩

theorem HadFrame.data {st out : State 180 80} (h : HadFrame st out)
    (k : Kind) (s : Sample k t n m) (hd : Data k s st) : Data k s out :=
  fun i => (h.regs (dataPort i) (by simp only [dataPort]; omega)).trans (hd i)

omit [NeZero t] in
theorem HadFrame.inner {st out : State 180 80} (h : HadFrame st out)
    (k : Kind) (s : Sample k t n m) (hs : InnerStored k s st) : InnerStored k s out :=
  ⟨(h.regs 126 (by decide)).trans hs.coin, (h.regs 127 (by decide)).trans hs.param,
    (h.regs 138 (by decide)).trans hs.point, (h.lists 55 (by decide)).trans hs.base,
    (h.lists 56 (by decide)).trans hs.auxiliary, (h.lists 57 (by decide)).trans hs.linear,
    (h.lists 58 (by decide)).trans hs.factors, (h.lists 59 (by decide)).trans hs.left,
    (h.lists 60 (by decide)).trans hs.right, (h.lists 61 (by decide)).trans hs.label⟩

def pointPrepare (src len : Fin 180) : Stmt 180 80 := .seq (.assign 0 (.var src))
  (.seq (.assign 5 (.var len)) (.seq (.assign 6 (.var 162)) (.copy 65 2)))

def uniform : Stmt 180 80 := call (by decide) (by decide) UniformDecode.program

def point (src len : Fin 180) (dst : Fin 80) : Stmt 180 80 :=
  .seq (pointPrepare src len) (.seq uniform (.copy 1 dst))

theorem point_run {d : ℕ} (p : Fin d → Field t) (src len : Fin 180) (dst : Fin 80)
    (st : State 180 80)
    (hc : st.regs src = (finFunctionFinEquiv (fun i => fieldEquiv t (p i))).val)
    (hn : st.regs len = d) (hl : 7 ≤ len.val)
    (hq : st.regs 162 = 2 ^ t) (he : st.lists 65 = []) :
    ((point src len dst).run st).1.lists dst = List.ofFn (fun i => (fieldEquiv t (p i)).val) := by
  have hlen : (0 : Fin 180) ≠ len := by intro h; have := congrArg Fin.val h; omega
  have hcode : (((Codec.fin d).function
      (fieldCodec (BinaryMaterializedField.coordinates t))).equiv p).val =
      (finFunctionFinEquiv (fun i => fieldEquiv t (p i))).val := by
    unfold Codec.function Codec.fin
    rw [UniformDecode.fieldCodec_materialized]
    rfl
  have h := UniformDecode.program_fieldPoint (Codec.fin d) p
    (((pointPrepare src len).run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [pointPrepare, Stmt.run, Expr.eval, Function.update, State.restrict]
          using hc.trans hcode.symm)
    (by simpa [pointPrepare, Stmt.run, Expr.eval, Function.update, State.restrict,
      Codec.fin, Ne.symm hlen] using hn)
    (by simpa [pointPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hq)
    (by simpa [pointPrepare, Stmt.run, Function.update, State.restrict] using he)
  rw [← call_result (by decide) (by decide) UniformDecode.program] at h
  change (uniform.run _).1.lists 1 = _ at h
  simp only [point, run_seq_fst, run_copy_fst, setList_lists, Function.update_self]
  exact h


def bitPrepare : Stmt 180 80 := .seq (.assign 0 (.var 152))
  (.seq (.assign 5 (.var 160)) (.seq (.assign 6 (.const 2)) (.copy 65 2)))

def bits : Stmt 180 80 := .seq bitPrepare (.seq uniform (.copy 1 45))

omit [NeZero t] in
theorem bits_run (w : Fin t → ZMod 2) (st : State 180 80)
    (hc : st.regs 152 = ((bitsCodec t).equiv w).val)
    (ht : st.regs 160 = t) (he : st.lists 65 = []) :
    (bits.run st).1.lists 45 = List.ofFn (fun i => (w i).val) := by
  have h := UniformDecode.program_bits w
    (((bitPrepare.run st).1).restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update] using hc)
    (by simpa [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update] using ht)
    (by simp [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update])
    (by simpa [bitPrepare, Stmt.run, State.restrict, Function.update] using he)
  rw [← call_result (by decide) (by decide) UniformDecode.program] at h
  exact h


def directionPrepare : Stmt 180 80 := .seq (.assign 0 (.var 153))
  (.seq (.assign 6 (.const 4)) (.seq (.assign 5 (.mul 6 161))
    (.seq (.assign 6 (.var 162)) (.copy 65 2))))

def direction : Stmt 180 80 := .seq directionPrepare (.seq uniform (.copy 1 44))

theorem direction_run (p : BinaryLocalCorrection.InnerPoint (Field t) m 4)
    (st : State 180 80)
    (hc : st.regs 153 = (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 p).val)
    (hm : st.regs 161 = m) (hq : st.regs 162 = 2 ^ t) (he : st.lists 65 = []) :
    (direction.run st).1.lists 44 = List.ofFn
      (fun i => (fieldEquiv t (StandardCorrection.vector p i)).val) := by
  have h := UniformDecode.program_fieldPoint ((Codec.fin 4).prod (Codec.fin m)) p
    ((directionPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by change st.regs 153 = _
        exact hc.trans (innerPointCodec_materialized p).symm)
    (by simp [directionPrepare, Stmt.run, Expr.eval, State.restrict, hm,
      Function.update, Codec.prod, Codec.fin])
    (by simpa [directionPrepare, Stmt.run, Expr.eval, State.restrict, Function.update] using hq)
    (by simpa [directionPrepare, Stmt.run, State.restrict, Function.update] using he)
  rw [← call_result (by decide) (by decide) UniformDecode.program] at h
  change (uniform.run _).1.lists 1 = _ at h
  exact h

structure WordFrame (dst : Fin 80) (st out : State 180 80) : Prop where
  regs : ∀ i : Fin 180, 7 ≤ i.val → out.regs i = st.regs i
  lists : ∀ i : Fin 80, 3 ≤ i.val → i ≠ dst → out.lists i = st.lists i

theorem coordinate_frame (prep : Stmt 180 80) (dst : Fin 80)
    (hr : ∀ i ∈ prep.regWrites, i.val < 7)
    (hl : ∀ i ∈ prep.listWrites, i.val < 3) (st : State 180 80) :
    WordFrame dst st ((Stmt.seq prep (.seq uniform (.copy 1 dst))).run st).1 := by
  constructor
  · intro i hi
    simp only [run_seq_fst, run_copy_fst, setList_regs]
    unfold uniform
    rw [call_reg (by decide) (by decide) UniformDecode.program _ i hi]
    apply run_regs_frame
    intro h
    have := hr i h
    omega
  · intro i hi hdst
    simp only [run_seq_fst, run_copy_fst, setList_lists, Function.update_of_ne hdst]
    unfold uniform
    rw [call_list (by decide) (by decide) UniformDecode.program _ i hi]
    apply run_lists_frame
    intro h
    have := hl i h
    omega

theorem point_frame (src len : Fin 180) (dst : Fin 80) (st : State 180 80) :
    WordFrame dst st ((point src len dst).run st).1 := by
  apply coordinate_frame (pointPrepare src len) dst
  · simp only [pointPrepare, Stmt.regWrites]; decide
  · simp only [pointPrepare, Stmt.listWrites]; decide

theorem bits_frame (st : State 180 80) : WordFrame 45 st (bits.run st).1 :=
  coordinate_frame bitPrepare 45 (by decide) (by decide) st


theorem direction_frame (st : State 180 80) : WordFrame 44 st (direction.run st).1 :=
  coordinate_frame directionPrepare 44 (by decide) (by decide) st

theorem WordFrame.public {dst : Fin 80} {st out : State 180 80}
    (h : WordFrame dst st out) (hd : dst.val < 64) : Frame st out :=
  ⟨fun i hi => h.regs i (by omega), fun i hi => h.lists i (by omega) (by
    intro he; have := congrArg Fin.val he; omega)⟩

theorem WordFrame.data {dst : Fin 80} {st out : State 180 80}
    (h : WordFrame dst st out) (k : Kind) (s : Sample k t n m) (hs : Data k s st) : Data k s out :=
  fun i => (h.regs (dataPort i) (by simp only [dataPort]; omega)).trans (hs i)

omit [NeZero t] in
theorem WordFrame.inner {dst : Fin 80} {st out : State 180 80}
    (h : WordFrame dst st out) (hd : dst.val < 50)
    (k : Kind) (s : Sample k t n m) (hs : InnerStored k s st) : InnerStored k s out := by
  have hf : ∀ i : Fin 80, 50 ≤ i.val → out.lists i = st.lists i := by
    intro i hi
    exact h.lists i (by omega) (by intro he; have := congrArg Fin.val he; omega)
  exact ⟨(h.regs 126 (by decide)).trans hs.coin, (h.regs 127 (by decide)).trans hs.param,
    (h.regs 138 (by decide)).trans hs.point, (hf 55 (by decide)).trans hs.base,
    (hf 56 (by decide)).trans hs.auxiliary, (hf 57 (by decide)).trans hs.linear,
    (hf 58 (by decide)).trans hs.factors, (hf 59 (by decide)).trans hs.left,
    (hf 60 (by decide)).trans hs.right, (hf 61 (by decide)).trans hs.label⟩

omit [NeZero t] in
theorem WordFrame.primary {dst : Fin 80} {st out : State 180 80}
    (h : WordFrame dst st out) (hd : dst.val < 50)
    (k : Kind) (s : Sample k t n m) (hs : PrimaryStored k s st) : PrimaryStored k s out := by
  have hf : ∀ i : Fin 80, 50 ≤ i.val → out.lists i = st.lists i := by
    intro i hi
    exact h.lists i (by omega) (by intro he; have := congrArg Fin.val he; omega)
  exact ⟨(hf 50 (by decide)).trans hs.base, (hf 51 (by decide)).trans hs.auxiliary,
    (hf 52 (by decide)).trans hs.linear, (hf 53 (by decide)).trans hs.factors⟩

end PCP.Lang.OuterSeed
