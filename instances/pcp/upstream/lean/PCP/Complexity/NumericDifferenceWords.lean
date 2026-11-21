import PCP.Complexity.NumericDifferenceDecode

/-! # Materialize the binary coefficient label and load the difference branch -/

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def bitPrepare : Stmt 120 40 := .seq (.assign 0 (.var 90))
  (.seq (.assign 5 (.var 100)) (.seq (.assign 6 (.const 2)) (.copy 32 2)))

def uniform : Stmt 120 40 := call (by decide) (by decide) UniformDecode.program

def bits : Stmt 120 40 := .seq bitPrepare (.seq uniform (.copy 1 17))

omit [NeZero t] in
theorem bits_run (w : Fin t → ZMod 2) (st : State 120 40)
    (hc : st.regs 90 = ((bitsCodec t).equiv w).val)
    (ht : st.regs 100 = t) (he : st.lists 32 = []) :
    (bits.run st).1.lists 17 = List.ofFn (fun i => (w i).val) := by
  have h := UniformDecode.program_bits w
    ((bitPrepare.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    (by simpa [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update] using hc)
    (by simpa [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update] using ht)
    (by simp [bitPrepare, Stmt.run, Expr.eval, State.restrict, Function.update])
    (by simpa [bitPrepare, Stmt.run, State.restrict, Function.update] using he)
  rw [← call_result (by decide) (by decide) UniformDecode.program] at h
  exact h

theorem bits_reg (st : State 120 40) (i : Fin 120) (hi : 7 ≤ i.val) :
    (bits.run st).1.regs i = st.regs i := by
  simp only [bits, run_seq_fst, run_copy_fst, setList_regs]
  unfold uniform
  rw [call_reg (by decide) (by decide) UniformDecode.program _ i hi]
  apply run_regs_frame
  simp only [bitPrepare, Stmt.regWrites, List.mem_append, List.mem_singleton,
    List.not_mem_nil, or_false]
  intro h
  rcases h with h | h | h
  all_goals have := congrArg Fin.val h; omega

theorem bits_frame (st : State 120 40) : Frame st (bits.run st).1 := by
  refine ⟨fun i hi => bits_reg st i (by omega), ?_⟩
  intro i hi
  have h17 : i ≠ 17 := by intro h; have := congrArg Fin.val h; omega
  have h2 : i ≠ 2 := by intro h; have := congrArg Fin.val h; omega
  simp only [bits, run_seq_fst, run_copy_fst, setList_lists, Function.update_of_ne h17]
  unfold uniform
  rw [call_list (by decide) (by decide) UniformDecode.program _ i (by omega)]
  exact run_lists_frame bitPrepare i (by simp [bitPrepare, Stmt.listWrites, h2]) st

def finish : Stmt 120 40 := .seq (.assign 20 (.var 100))
  (.seq (.assign 57 (.var 92)) (.seq (.assign 58 (.var 91))
    (.seq (.assign 59 (.var 104)) (.seq (.assign 60 (.var 105))
      (.seq (.assign 61 (.var 106)) (.seq (.assign 62 (.var 107))
        (.seq (.copy 32 7) (.seq (.copy 33 30) (.copy 34 31)))))))))

def load : Stmt 120 40 := .seq unpack (.seq bits finish)

structure Context (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) : Prop where
  width : st.regs 20 = t
  empty : st.lists 7 = []
  label : st.lists 17 = List.ofFn (fun i => (s.2 i).val)
  history : st.lists 30 = qs
  answers : st.lists 31 = bs.map Bool.toNat
  left : st.regs 57 = codes s 2
  right : st.regs 58 = codes s 1
  vertices : st.regs 59 = (2^t)^n
  pairs : st.regs 60 = (2^t)^(n+n)
  affineLabels : st.regs 61 = 2^BooleanCoefficientIndex.dimension t 1
  cubicLabels : st.regs 62 = 2^BooleanCoefficientIndex.dimension t 3

omit [NeZero t] in
theorem finish_run (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st) (hd : Data s st)
    (hw : st.lists 17 = List.ofFn (fun i => (s.2 i).val)) :
    Context s qs bs (finish.run st).1 := by
  have hl : st.regs 92 = codes s 2 := hd 2
  have hr : st.regs 91 = codes s 1 := hd 1
  constructor <;> simp [finish, Stmt.run, Expr.eval, Function.update, hp.width, hp.empty,
    hp.history, hp.answers, hp.vertices, hp.pairs, hp.affineLabels, hp.cubicLabels, hl, hr, hw]

theorem finish_frame (st : State 120 40) : Frame st (finish.run st).1 :=
  frame_of_writes finish (by simp [finish, Stmt.regWrites])
    (by simp [finish, Stmt.listWrites]) st

attribute [local irreducible] unpack bits

theorem load_run (s : Sample t n) (qs : List ℕ) (bs : List Bool)
    (st : State 120 40) (hp : Public (t := t) n m qs bs st)
    (hs : st.regs 108 = ((seedCodec t n).equiv s).val) :
    Context s qs bs (load.run st).1 ∧ Public (t := t) n m qs bs (load.run st).1 ∧
      Frame st (load.run st).1 := by
  obtain ⟨hd, hp', hf⟩ := unpack_run s qs bs st hp hs
  have hw := bits_run s.2 (unpack.run st).1 (hd 0) hp'.width hp'.empty
  have hd' : Data s (bits.run (unpack.run st).1).1 := fun i =>
    (bits_reg _ (dataPort i) (by simp only [dataPort]; omega)).trans (hd i)
  have hb := bits_frame (unpack.run st).1
  have hc := finish_run s qs bs _ (hp'.of_frame hb) hd' hw
  have hfinal := hf.trans (hb.trans (finish_frame (bits.run (unpack.run st).1).1))
  exact ⟨hc, hp.of_frame hfinal, hfinal⟩

end PCP.Lang.NumericDifference
