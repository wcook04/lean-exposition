import PCP.Complexity.InterpolationBranchState

/-!
# Lagrange constraint weights in the live branch state
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def weightPrepare : Stmt 100 40 := .seq (.copy 35 12)
  (.seq (.assign 42 (.var 80)) (.assign 43 (.var 82)))

def weightCall (i : Fin 5) : Stmt 100 40 :=
  call (by decide) (by decide) (InterpolationWeightLoad.program i)

def weightSave (i : Fin 5) : Stmt 100 40 := .seq (.assign 92 (.var 32))
  (.assign 93 (.var (i.castAdd 95)))

def weightStep (i : Fin 5) : Stmt 100 40 :=
  .seq weightPrepare (.seq (weightCall i) (weightSave i))

theorem weightPrepare_frame (st : State 100 40) : Frame st (weightPrepare.run st).1 := by
  refine ⟨?_, ?_, run_lists_frame weightPrepare 3 (by decide) st,
    run_lists_frame weightPrepare 7 (by decide) st⟩
  · intro i hi hj
    apply run_regs_frame
    simp only [weightPrepare, Stmt.regWrites, List.nil_append, List.mem_append,
      List.mem_singleton, not_or]
    constructor <;> intro he <;> subst i <;> norm_num at hi
  · intro L hL
    apply run_lists_frame
    simp only [weightPrepare, Stmt.listWrites, List.append_nil, List.mem_singleton]
    intro he
    subst L
    norm_num at hL

theorem weightPrepare_context (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (st : State 100 40) (hc : Context a z u v w site st) :
    InterpolationWeightLoad.Context a z ((weightPrepare.run st).1.restrict
      (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  simp [InterpolationWeightLoad.Context, weightPrepare, Stmt.run, Expr.eval,
    Function.update, State.restrict, hc.width, hc.param, hc.modulus, hc.empty, hc.nodes]

theorem weightCall_run (a : Fin 5 → Field t) (z : Field t) (i : Fin 5)
    (st : State 100 40) (hc : InterpolationWeightLoad.Context a z
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))) :
    ((weightCall i).run st).1.regs 32 =
      (fieldEquiv t (FieldQueryArithmetic.interpolationWeight a z i)).val ∧
    ((weightCall i).run st).1.regs (i.castAdd 95) = (fieldEquiv t (a i)).val ∧
    Frame st ((weightCall i).run st).1 := by
  have hr := call_result (by decide) (by decide) (InterpolationWeightLoad.program i) st
  have hp := InterpolationWeightLoad.program_run a z i _ hc
  have hn := InterpolationWeightLoad.program_node a z i i _ hc
  have hf := InterpolationWeightLoad.program_context a z i _ hc
  rw [← hr] at hp hn hf
  refine ⟨hp, ?_, ?_⟩
  · simpa only [weightCall, Prod.fst, State.restrict_regs,
      show Fin.castLE (by decide : 48 ≤ 100) (i.castAdd 43) = i.castAdd 95 from rfl] using hn
  · exact ⟨fun j hj _ => call_reg _ _ _ st j hj,
      fun L hL => call_list _ _ _ st L (by omega),
      hf.2.2.1.trans hc.2.2.1.symm, hf.2.2.2.1.trans hc.2.2.2.1.symm⟩

theorem weightSave_frame (i : Fin 5) (st : State 100 40) :
    Frame st ((weightSave i).run st).1 := by
  have h := Frame.assign st 92 (by decide) (st.regs 32)
  exact h.trans (Frame.assign _ 93 (by decide) _)

theorem weightStep_run (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (i : Fin 5) (st : State 100 40) (hc : Context a z u v w site st) :
    ((weightStep i).run st).1.regs 92 =
      (fieldEquiv t (FieldQueryArithmetic.interpolationWeight a z i)).val ∧
    ((weightStep i).run st).1.regs 93 = (fieldEquiv t (a i)).val ∧
    Frame st ((weightStep i).run st).1 := by
  have hc' := weightPrepare_context a z u v w site st hc
  have hp := weightPrepare_frame st
  generalize hs : (weightPrepare.run st).1 = s at *
  have hw := weightCall_run a z i s hc'
  generalize hu : ((weightCall i).run s).1 = out at *
  have hsave := weightSave_frame i out
  simp only [weightStep, run_seq_fst, hs, hu]
  refine ⟨?_, ?_, hp.trans (hw.2.2.trans hsave)⟩
  · simpa [weightSave, Stmt.run, Expr.eval, Function.update] using hw.1
  · have hi : i.castAdd 95 ≠ (92 : Fin 100) := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simpa [weightSave, Stmt.run, Expr.eval, Function.update, hi] using hw.2.1

theorem weightStep_queries (i : Fin 5) (st : State 100 40) :
    ((weightStep i).run st).1.lists 20 = st.lists 20 := by
  simp only [weightStep, run_seq_fst]
  have hs := run_lists_frame (weightSave i) 20 (by simp [weightSave, Stmt.listWrites])
    ((weightCall i).run
    (weightPrepare.run st).1).1
  rw [hs]
  rw [show ((weightCall i).run (weightPrepare.run st).1).1.lists 20 =
      (weightPrepare.run st).1.lists 20 from call_list _ _ _ _ 20 (by decide)]
  exact run_lists_frame weightPrepare 20 (by decide) st

end PCP.Lang.InterpolationBranch
