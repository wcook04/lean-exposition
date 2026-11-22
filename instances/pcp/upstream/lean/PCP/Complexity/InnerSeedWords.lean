/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedDecode

/-! # Stored Hadamard words and interpolation coordinates from decoded inner seeds -/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

-- The fixed materializers contain nested finite coefficient loops.
set_option maxRecDepth 4096

variable {t n m : ℕ} [NeZero t]

def rowState (st : State 140 44) : State 80 32 :=
  st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))

def hadPrepare : Stmt 140 44 := .seq (.assign 20 (.var 120))
  (.seq (.copy 41 7) (.assign 96 (.var 107)))

def hadCall : Stmt 140 44 := call (by decide) (by decide) (HadamardSeed.program 1)

def hadamard : Stmt 140 44 := .seq hadPrepare hadCall

attribute [local irreducible] HadamardSeed.program hadCall

theorem hadamard_run (s : InnerBranch.Seed t m) (st : State 140 44)
    (ht : st.regs 120 = t) (he : st.lists 41 = []) (hd : Data s st) :
    HadamardRow.Context s.2.1.2 (rowState (hadamard.run st).1) := by
  have hs : st.regs 107 = ((hadamardCodec t 1).equiv s.2.1.2).val := hd 4
  have h := HadamardSeed.program_run s.2.1.2
    ((hadPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using ht)
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using he)
    (by simpa [hadPrepare, Stmt.run, Expr.eval, Function.update, State.restrict] using hs)
  rw [← call_result (by decide) (by decide) (HadamardSeed.program 1)] at h
  rw [show call (by decide) (by decide) (HadamardSeed.program 1) = hadCall by
    unfold hadCall; rfl] at h
  simp only [hadamard, run_seq_fst]
  generalize hu : (hadCall.run (hadPrepare.run st).1).1 = u at *
  exact h

theorem hadamard_frame (st : State 140 44) : Frame st (hadamard.run st).1 := by
  unfold hadamard hadCall
  exact (frame_of_writes hadPrepare (by decide) (by decide) st).trans
    (call_frame (by decide) (by decide) (HadamardSeed.program 1) _)

theorem hadamard_data (s : InnerBranch.Seed t m) (st : State 140 44) (hd : Data s st) :
    Data s (hadamard.run st).1 := by
  intro i
  unfold hadamard hadCall
  exact (call_reg (by decide) (by decide) (HadamardSeed.program 1) _ (dataPort i)
    (by simp only [dataPort]; omega)).trans
    ((run_regs_frame hadPrepare (dataPort i) (by
      simp only [hadPrepare, Stmt.regWrites, List.mem_append, List.mem_singleton,
        List.not_mem_nil, false_or]
      intro h
      rcases h with h | h
      all_goals have hh := congrArg Fin.val h; simp only [dataPort] at hh; omega) st).trans (hd i))

def uniformLists : Fin 3 → Fin 8 := ![0, 1, 7]

def uniform : Stmt 7 8 := UniformDecode.program.rename id uniformLists

theorem uniform_result (st : State 140 44) :
    (((call (by decide) (by decide) uniform).run st).1.restrict
        (Fin.castLE (by decide)) ((Fin.castLE (by decide)) ∘ uniformLists),
      ((call (by decide) (by decide) uniform).run st).2) =
    UniformDecode.program.run (st.restrict (Fin.castLE (by decide))
      ((Fin.castLE (by decide)) ∘ uniformLists)) := by
  have h := UniformDecode.program.run_rename id uniformLists Function.injective_id
    (by decide) (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  change (State.restrict id uniformLists (uniform.run _).1, (uniform.run _).2) = _ at h
  rw [← call_result (by decide) (by decide) uniform st] at h
  exact h

def pointPrepare (src : Fin 140) : Stmt 140 44 := .seq (.assign 0 (.var src))
  (.seq (.assign 6 (.const 4)) (.seq (.assign 5 (.mul 6 121))
    (.seq (.assign 6 (.var 122)) (.copy 41 7))))

def point (src : Fin 140) (dst : Fin 44) : Stmt 140 44 :=
  .seq (pointPrepare src) (.seq (call (by decide) (by decide) uniform) (.copy 1 dst))

theorem point_run (p : Point t m) (src : Fin 140) (dst : Fin 44) (st : State 140 44)
    (hc : st.regs src = ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv p).val)
    (hm : st.regs 121 = m) (hq : st.regs 122 = 2 ^ t) (he : st.lists 41 = []) :
    ((point src dst).run st).1.lists dst = List.ofFn
      (fun i => (BinaryFieldCode.fieldEquiv t (StandardCorrection.vector p i)).val) := by
  unfold innerPointCodec at hc
  have h := UniformDecode.program_fieldPoint ((Codec.fin 4).prod (Codec.fin m)) p
    (((pointPrepare src).run st).1.restrict (Fin.castLE (by decide))
      ((Fin.castLE (by decide)) ∘ uniformLists))
    (by simp only [pointPrepare, run_seq_fst, run_assign_fst, run_copy_fst,
          Expr.eval, State.restrict_regs, setList_regs, setReg_regs]
        simpa [uniformLists, Function.update] using hc)
    (by simp [pointPrepare, Stmt.run, Expr.eval, State.restrict, hm, uniformLists,
      Function.update, Codec.prod, Codec.fin])
    (by simpa [pointPrepare, Stmt.run, Expr.eval, State.restrict, uniformLists,
      Function.update] using hq)
    (by simpa [pointPrepare, Stmt.run, Expr.eval, State.restrict, uniformLists,
      Function.update] using he)
  rw [← uniform_result] at h
  simp only [point, run_seq_fst, run_copy_fst, setList_lists, Function.update_self]
  generalize hu : ((call (by decide) (by decide) uniform).run
    ((pointPrepare src).run st).1).1 = u at *
  change u.lists 1 = _ at h
  convert h using 1
  simp only [StandardCorrection.vector, Codec.prod, Codec.fin]
  rfl

def bitPrepare : Stmt 140 44 := .seq (.assign 0 (.var 103))
  (.seq (.assign 5 (.var 120)) (.seq (.assign 6 (.const 2)) (.copy 41 7)))

def bits : Stmt 140 44 := .seq bitPrepare
  (.seq (call (by decide) (by decide) uniform) (.copy 1 34))

omit [NeZero t] in
theorem bits_run (w : Fin t → ZMod 2) (st : State 140 44)
    (hc : st.regs 103 = ((bitsCodec t).equiv w).val)
    (ht : st.regs 120 = t) (he : st.lists 41 = []) :
    (bits.run st).1.lists 34 = List.ofFn (fun i => (w i).val) := by
  have h := UniformDecode.program_bits w
    (((bitPrepare.run st).1).restrict (Fin.castLE (by decide))
      ((Fin.castLE (by decide)) ∘ uniformLists))
    (by simpa [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update] using hc)
    (by simpa [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update] using ht)
    (by simp [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update])
    (by simpa [bitPrepare, Stmt.run, Expr.eval, State.restrict, uniformLists,
      Function.update] using he)
  rw [← uniform_result] at h
  exact h

/-- The coordinate decoder preserves all larger scalar cells and stored words. -/
structure WordFrame (dst : Fin 44) (st out : State 140 44) : Prop where
  regs : ∀ i : Fin 140, 7 ≤ i.val → out.regs i = st.regs i
  lists : ∀ L : Fin 44, 8 ≤ L.val → L ≠ dst → out.lists L = st.lists L
  empty : out.lists 7 = st.lists 41

theorem coordinate_frame (prep : Stmt 140 44) (dst : Fin 44) (hd : 8 ≤ dst.val)
    (hr : ∀ i ∈ prep.regWrites, i.val < 7)
    (hl : ∀ L ∈ prep.listWrites, L = 7)
    (he : ∀ st, (prep.run st).1.lists 7 = st.lists 41) (st : State 140 44) :
    WordFrame dst st ((Stmt.seq prep (.seq (call (by decide) (by decide) uniform)
      (.copy 1 dst))).run st).1 := by
  have hf := UniformDecode.program_frame ((prep.run st).1.restrict
    (Fin.castLE (by decide)) ((Fin.castLE (by decide)) ∘ uniformLists))
  rw [← uniform_result] at hf
  constructor
  · intro i hi
    simp only [run_seq_fst, run_copy_fst, setList_regs]
    rw [call_reg (by decide) (by decide) uniform _ i hi]
    apply run_regs_frame
    intro h
    have := hr i h
    omega
  · intro L hL hdst
    simp only [run_seq_fst, run_copy_fst, setList_lists, Function.update_of_ne hdst]
    rw [call_list (by decide) (by decide) uniform _ L hL]
    apply run_lists_frame
    intro h
    have := congrArg Fin.val (hl L h)
    omega
  · simp only [run_seq_fst, run_copy_fst]
    generalize hu : ((call (by decide) (by decide) uniform).run (prep.run st).1).1 = u at *
    rw [setList_lists, Function.update_of_ne (show (7 : Fin 44) ≠ dst by
      intro h; have := congrArg Fin.val h; omega)]
    exact hf.2.2.trans (he st)

theorem point_frame (src : Fin 140) (dst : Fin 44) (hd : 8 ≤ dst.val) (st : State 140 44) :
    WordFrame dst st ((point src dst).run st).1 := by
  apply coordinate_frame (pointPrepare src) dst hd
  · simp only [pointPrepare, Stmt.regWrites]
    decide
  · simp only [pointPrepare, Stmt.listWrites]
    decide
  · intro st
    simp [pointPrepare, Stmt.run, Function.update]

theorem bits_frame (st : State 140 44) : WordFrame 34 st (bits.run st).1 := by
  apply coordinate_frame bitPrepare 34 (by decide)
  · decide
  · decide
  · intro st
    simp [bitPrepare, Stmt.run, Function.update]

theorem WordFrame.public {dst : Fin 44} {st out : State 140 44}
    (h : WordFrame dst st out) (hd : dst.val < 40) : Frame st out :=
  ⟨fun i hi => h.regs i (by omega), fun L hL => h.lists L (by omega) (by
    intro he; have := congrArg Fin.val he; omega)⟩

theorem WordFrame.data {dst : Fin 44} {st out : State 140 44}
    (h : WordFrame dst st out) (s : InnerBranch.Seed t m) (hs : Data s st) : Data s out :=
  fun i => (h.regs (dataPort i) (by simp only [dataPort]; omega)).trans (hs i)

omit [NeZero t] in
theorem WordFrame.hadamard {dst : Fin 44} {st out : State 140 44}
    (h : WordFrame dst st out) (hd : 32 ≤ dst.val) (s : InnerBranch.Seed t m)
    (he : st.lists 41 = []) (hs : HadamardRow.Context s.2.1.2 (rowState st)) :
    HadamardRow.Context s.2.1.2 (rowState out) := by
  rcases hs with ⟨h20, h56, _, hb, ha, hl, hf⟩
  refine ⟨(h.regs 20 (by decide)).trans h20, (h.regs 56 (by decide)).trans h56,
    h.empty.trans he, ?_, ?_, ?_, ?_⟩
  · exact (h.lists 20 (by decide) (by
      intro hh; have := congrArg Fin.val hh; omega)).trans hb
  · exact (h.lists 21 (by decide) (by
      intro hh; have := congrArg Fin.val hh; omega)).trans ha
  · exact (h.lists 22 (by decide) (by
      intro hh; have := congrArg Fin.val hh; omega)).trans hl
  · exact (h.lists 23 (by decide) (by
      intro hh; have := congrArg Fin.val hh; omega)).trans hf

end PCP.Lang.InnerSeed
