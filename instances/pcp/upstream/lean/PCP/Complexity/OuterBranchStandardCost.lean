import PCP.Complexity.OuterBranchStandard
import PCP.Complexity.OuterBranchResources

/-!
# Cost of the actual evaluation-point and standard-correction stage
-/

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t] [NeZero m]

attribute [local irreducible] evaluationCall evaluationAt loadStandard callStandard
  EvaluationPoint.program

theorem evaluationAt_cost (src : Fin 180) (hs : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (ha : st.regs src = (fieldEquiv t α).val) :
    ((evaluationAt src).run st).2 ≤ 100000000100 * (t+m+1)^5 := by
  have h24 : src ≠ 24 := by intro h; subst src; norm_num at hs
  have hv : EvaluationPoint.View m α (((evaluationPrepare src).run st).1.restrict
      (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
    simp [evaluationPrepare, EvaluationPoint.View, Stmt.run, Expr.eval, Function.update,
      State.restrict, hc.width, hc.base, hc.modulus, hc.empty, h24, ha]
  have he : ((evaluationPrepare src).run st).1.lists 1 = [] := by
    simp [evaluationPrepare, Stmt.run, Function.update, hc.empty]
  have hp := EvaluationPoint.program_cost m α _ (NeZero.pos m) hv he
  rw [← congrArg Prod.snd (call_result (by decide) (by decide)
    EvaluationPoint.program ((evaluationPrepare src).run st).1)] at hp
  have hcall : (evaluationCall.run ((evaluationPrepare src).run st).1).2 ≤
      100000000000 * (t+m+1)^5 := by
    simpa only [evaluationCall, Prod.snd] using hp
  have hm : listSize (st.lists 40) ≤ 2*t := by
    rw [hc.modulus]; exact InterpolationBranch.coordinateBits_size _
  have ht := size_le_self t
  have hbase := size_le_self m
  have hα : Nat.size (fieldEquiv t α).val ≤ t := Nat.size_le.mpr (fieldEquiv t α).isLt
  have hload : ((evaluationPrepare src).run st).2 ≤ 6*t+2*m+11 := by
    simp only [evaluationPrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
      setList_regs, setList_lists, setReg_regs, Function.update, h24,
      Fin.reduceEq, dite_false, hc.width, hc.base, hc.empty, ha,
      show listSize [] = 0 from rfl]
    omega
  have hpow : t+m+1 ≤ (t+m+1)^5 := Nat.le_pow (by decide)
  rw [evaluationAt, run_seq_snd]
  nlinarith only [hcall, hload, hpow]

set_option maxRecDepth 2048 in
-- The fixed source loader is loop-free and reads one computed evaluation-point list.
theorem loadStandard_cost (W : ℕ) (st : State 180 80) (hb : StoredBound W st) :
    (loadStandard.run st).2 ≤ loaderConstant loadStandard *
      (W+listSize (st.lists 1)+listSize (st.lists 49)+1) := by
  apply loader_cost_extra loadStandard (by unfold loadStandard; decide)
    (by unfold loadStandard; decide) (by unfold loadStandard; decide) W st hb

omit [NeZero m] in
theorem standardQueries_size (site : StandardCorrection.Site (Field t) n)
    (ζ : Field t) (u v : BinaryLocalCorrection.InnerPoint (Field t) m 4)
    (w : Fin t → ZMod 2) (W : ℕ)
    (hb : StandardCorrection.QueryBound site ζ u v w W) :
    listSize ((site.queries ζ (BinaryMaterializedField.coordinates t) u v w).map (fun q =>
      (ThreeColorQueryIndex.equiv (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) q).val)) ≤ 5*(W+1) := by
  rw [StandardCorrection.Site.queries_ofFn]
  simp only [listSize, List.map_ofFn, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin 5, (W+1) := Finset.sum_le_sum fun i _ =>
      by
        simpa only [StandardCorrection.queryCode, StandardCorrection.queryLabel_coe, Function.comp_apply] using
          Nat.add_le_add_right (hb i.val i.isLt).2 1
    _ = _ := by simp

omit [NeZero m] in
theorem callStandard_cost (site : StandardCorrection.Site (Field t) n)
    (ζ : Field t) (u v : BinaryLocalCorrection.InnerPoint (Field t) m 4)
    (w : Fin t → ZMod 2) (W : ℕ) (st : State 180 80)
    (hi : StandardCorrection.Input site ζ u v w
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))))
    (hb : StandardCorrection.QueryBound site ζ u v w W) (he : st.lists 21 = []) :
    (callStandard.run st).2 ≤ StandardCorrection.costConstant *
      (2^t+t+4*m+W+listSize (st.lists 22)+listSize (st.lists 23)+listSize (st.lists 20)+4)^7 := by
  have hp := StandardCorrection.program_cost site ζ u v w W _ hi hb
    (by simpa only [State.restrict_lists,
      show Fin.castLE (by decide : 26 ≤ 80) (21 : Fin 26) = (21 : Fin 80) from rfl,
      he, show listSize [] = 0 from rfl]
      using Nat.zero_le W)
  rw [← congrArg Prod.snd (call_result (by decide) (by decide) StandardCorrection.program st)] at hp
  simpa only [callStandard, Prod.snd, StandardCorrection.budget, State.restrict_lists,
    show Fin.castLE (by decide : 26 ≤ 80) (20 : Fin 26) = (20 : Fin 80) from rfl,
    show Fin.castLE (by decide : 26 ≤ 80) (22 : Fin 26) = (22 : Fin 80) from rfl,
    show Fin.castLE (by decide : 26 ≤ 80) (23 : Fin 26) = (23 : Fin 80) from rfl] using hp

/-- The wrapper charges the sampler, loader, correction, query-copy and result-copy explicitly. -/
theorem standardAt_cost (src : Fin 180) (hsrc : 120 ≤ src.val)
    (k : Kind) (a : Fin 5 → Field t) (ζ α : Field t) (s : Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (hs : StoredBound W st)
    (ha : st.regs src = (fieldEquiv t α).val)
    (hb : StandardCorrection.QueryBound (k.line s.1) ζ (SetMultilinear.evaluationPoint m 4 α)
      s.2.2.1.1 s.2.2.1.2 W) :
    ((standardAt src).run st).2 ≤ 100000000100*(t+m+1)^5 +
      loaderConstant loadStandard*(W+(4*m)*(t+1)+listSize (st.lists 49)+1) +
      StandardCorrection.costConstant*
        (2^t+t+4*m+W+listSize (st.lists 47)+listSize (st.lists 48)+listSize (st.lists 49)+4)^7 +
      5*(W+1)+listSize (st.lists 49)+12 := by
  have he := evaluationAt_run src hsrc k a ζ α s qs bs st hc ha
  have hec := evaluationAt_cost src hsrc k a ζ α s qs bs st hc ha
  have heq := evaluationAt_queries src st
  generalize hE : ((evaluationAt src).run st).1 = e at *
  have hce := hc.of_frame he.2
  have hse := hs.of_frame he.2
  have hp := loadStandard_cost W e hse
  rw [heq] at hp
  have hl1 : listSize (e.lists 1) ≤ (4*m)*(t+1) := by
    rw [he.1]; exact StandardCorrection.fieldCodes_size _
  have hp' := hp.trans (Nat.mul_le_mul_left _ (by omega :
    W+listSize (e.lists 1)+listSize (st.lists 49)+1 ≤
      W+(4*m)*(t+1)+listSize (st.lists 49)+1))
  have hi := loadStandard_input k a ζ α s qs bs e hce he.1
  have hq : (loadStandard.run e).1.lists 22 = st.lists 47 := by
    simpa [loadStandard, Stmt.run, Function.update] using he.2.lists 47 (by decide)
      (by decide) (by decide)
  have hb' : (loadStandard.run e).1.lists 23 = st.lists 48 := by
    simpa [loadStandard, Stmt.run, Function.update] using he.2.lists 48 (by decide)
      (by decide) (by decide)
  have hacc : (loadStandard.run e).1.lists 20 = st.lists 49 := by
    simpa [loadStandard, Stmt.run, Function.update] using heq
  have h21 : (loadStandard.run e).1.lists 21 = [] := by
    simpa [loadStandard, Stmt.run, Function.update] using hce.empty
  have hcall := callStandard_cost (k.line s.1) ζ (SetMultilinear.evaluationPoint m 4 α)
    s.2.2.1.1 s.2.2.1.2 W _ hi hb h21
  rw [hq, hb', hacc] at hcall
  have hout' := callStandard_run k ζ (SetMultilinear.evaluationPoint m 4 α)
    s.2.2.1.1 s.2.2.1.2 qs bs s.1 (loadStandard.run e).1 hi
      (hq.trans hc.history) (hb'.trans hc.answers)
  rw [hacc] at hout'
  have hlist : listSize ((callStandard.run (loadStandard.run e).1).1.lists 20) ≤
      5*(W+1)+listSize (st.lists 49) := by
    have hsize := standardQueries_size (k.line s.1) ζ (SetMultilinear.evaluationPoint m 4 α)
      s.2.2.1.1 s.2.2.1.2 W hb
    rw [hout'.2, listSize_append, listSize_reverse]
    exact Nat.add_le_add_right hsize (listSize (st.lists 49))
  have hbit : Nat.size ((callStandard.run (loadStandard.run e).1).1.regs 48) ≤ 1 := by
    have hn : Nat.size (ComputableBinaryStandardLocalCorrection.correct 4 ζ (BinaryMaterializedField.coordinates t)
        ((k.line s.1).oracle (fieldEquiv t) (BooleanCoefficientIndex.coefficientEquiv t 1)
          (BooleanCoefficientIndex.coefficientEquiv t 3) qs bs)
        (SetMultilinear.evaluationPoint m 4 α) s.2.2.1.1 s.2.2.1.2).val ≤ 1 :=
      Nat.size_le.mpr (ZMod.val_lt _)
    rw [hout'.1]
    exact hn
  rw [standardAt, run_seq_snd, hE, run_seq_snd, run_seq_snd, run_seq_snd]
  simp only [Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs]
  omega

end PCP.Lang.OuterBranch
