import PCP.Complexity.InterpolationBranchState

/-!
# Materializing an affine query point inside the interpolation branch
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

def pointPrepare (src : Fin 100) : Stmt 100 40 :=
  .seq (.copy 32 12) (.seq (.copy 33 13) (.seq (.assign 43 (.var 80))
    (.seq (.assign 45 (.var 81)) (.assign 26 (.var src)))))

def pointCall : Stmt 100 40 := call (by decide) (by decide) StandardCorrection.scalarPoint

def pointStep (src : Fin 100) : Stmt 100 40 :=
  .seq (pointPrepare src) (.seq pointCall (.assign 95 (.var 59)))

theorem pointPrepare_frame (src : Fin 100) (st : State 100 40) :
    Frame st ((pointPrepare src).run st).1 := by
  exact (Frame.copy st 32 12 (by decide) (by decide) (by decide)).trans
    ((Frame.copy _ 33 13 (by decide) (by decide) (by decide)).trans
      ((Frame.assign _ 43 (by decide) _).trans
        ((Frame.assign _ 45 (by decide) _).trans (Frame.assign _ 26 (by decide) _))))

theorem pointPrepare_context (src : Fin 100) (hs : 80 ≤ src.val)
    (a : Fin 5 → Field t) (z : Field t) (u v : Point t m) (w : Fin t → ZMod 2)
    (site : StandardCorrection.Site (Field t) n) (α : Field t)
    (st : State 100 40) (hc : Context a z u v w site st)
    (ha : st.regs src = (fieldEquiv t α).val) :
    StandardCorrection.AffineContext (StandardCorrection.vector u) (StandardCorrection.vector v)
      (((pointPrepare src).run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) ∧
    ((pointPrepare src).run st).1.regs 26 = (fieldEquiv t α).val := by
  have h43 : src ≠ 43 := by intro h; subst src; norm_num at hs
  have h45 : src ≠ 45 := by intro h; subst src; norm_num at hs
  simp [pointPrepare, StandardCorrection.AffineContext, Stmt.run, Expr.eval, Function.update,
    State.restrict, hc.width, hc.card, hc.modulus, hc.empty, hc.left, hc.right, h43, h45, ha]

theorem pointCall_run (u v : Point t m) (α : Field t) (st : State 100 40)
    (hc : StandardCorrection.AffineContext (StandardCorrection.vector u)
      (StandardCorrection.vector v)
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))))
    (ha : st.regs 26 = (fieldEquiv t α).val) :
    (pointCall.run st).1.regs 59 =
      (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (PolynomialLine.point u v α)).val ∧
    Frame st (pointCall.run st).1 := by
  have hr := call_result (by decide) (by decide) StandardCorrection.scalarPoint st
  have hp := StandardCorrection.scalarPoint_run α _ _ _ hc ha
  have hf := StandardCorrection.scalarPoint_context α _ _ _ hc ha
  rw [← hr] at hp hf
  refine ⟨hp, ?_⟩
  exact ⟨fun i hi _ => call_reg _ _ _ st i hi,
    fun L hL => call_list _ _ _ st L (by omega),
    hf.2.2.1.trans hc.2.2.1.symm, hf.2.2.2.1.trans hc.2.2.2.1.symm⟩

theorem pointStep_run (src : Fin 100) (hs : 80 ≤ src.val)
    (a : Fin 5 → Field t) (z : Field t) (u v : Point t m) (w : Fin t → ZMod 2)
    (site : StandardCorrection.Site (Field t) n) (α : Field t)
    (st : State 100 40) (hc : Context a z u v w site st)
    (ha : st.regs src = (fieldEquiv t α).val) :
    ((pointStep src).run st).1.regs 95 =
      (ThreeColorQueryIndex.innerIndex (fieldEquiv t) m 4 (PolynomialLine.point u v α)).val ∧
    Frame st ((pointStep src).run st).1 := by
  have hp := pointPrepare_context src hs a z u v w site α st hc ha
  have hf := pointPrepare_frame src st
  generalize hs' : ((pointPrepare src).run st).1 = s at *
  have hcall := pointCall_run u v α s hp.1 hp.2
  simp only [pointStep, run_seq_fst, hs', run_assign_fst, Expr.eval]
  exact ⟨hcall.1, hf.trans (hcall.2.trans (Frame.assign _ 95 (by decide) _))⟩

theorem pointStep_queries (src : Fin 100) (st : State 100 40) :
    ((pointStep src).run st).1.lists 20 = st.lists 20 := by
  have hr := call_result (by decide) (by decide) StandardCorrection.scalarPoint
    ((pointPrepare src).run st).1
  have hq := StandardCorrection.scalarPoint_lists_outside
    (((pointPrepare src).run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    20 (by decide)
  rw [← hr] at hq
  have hp := run_lists_frame (pointPrepare src) 20 (by simp [pointPrepare, Stmt.listWrites]) st
  exact hq.trans hp

end PCP.Lang.InterpolationBranch
