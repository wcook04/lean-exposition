import PCP.Complexity.LocalCorrectionSemantics
import PCP.Complexity.OuterBranchInnerCost
import PCP.Complexity.OuterBranchStandardCost
import PCP.Complexity.OuterBranchReadCost

/-!
# Charged cost of the complete weighted certificate corrector
-/

set_option maxRecDepth 1024

namespace PCP.Lang.LocalCorrection

open PCP.Algebraic OuterBranch BinaryFieldCode

variable {t n m : ℕ} [NeZero t] [NeZero m]

attribute [local irreducible] primaryRead selectedInner standardAt finish
  loadStandard loadPrimaryAddress loadInnerConstant loaderConstant
  InnerBranch.costConstant StandardCorrection.costConstant RadixCodec.passConstant
  BooleanLabelTransform.queryConstant WordCodec.passConstant
  StandardCorrection.addressConstant QueryHistory.passConstant

structure Bounds (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (W : ℕ) : Prop where
  inner : InnerBranch.Bounds a (k.line s.1) (innerSeed s) W
  standard : StandardCorrection.QueryBound (k.line s.1) ζ
    (SetMultilinear.evaluationPoint m 4 s.2.1) s.2.2.1.1 s.2.2.1.2 W
  zero : StandardCorrection.QueryBound (k.line s.1) ζ
    (SetMultilinear.evaluationPoint m 4 0) s.2.2.1.1 s.2.2.1.2 W
  read : PrimaryBound (m := m) k (PolynomialLine.point s.1.1 s.1.2 s.2.1)
    (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2) W

def costConstant : ℕ := loadInnerConstant + InnerBranch.costConstant +
  2*100000000100 + 2*loaderConstant loadStandard + 2*StandardCorrection.costConstant +
  (RadixCodec.passConstant+101000100) +
  (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400) +
  loaderConstant loadPrimaryAddress + StandardCorrection.addressConstant +
  (QueryHistory.passConstant+40) + 100

def budget (k : Kind) (t n m W : ℕ) (st : State 180 80) : ℕ :=
  32*(t+4*m+k.dimension n+2^t+W+listSize (st.lists 49)+20)

theorem saveAndZero_cost (st : State 180 80) (hb : Nat.size (st.regs 142) ≤ 1) :
    (saveAndZero.run st).2 ≤ 5 := by
  simp only [saveAndZero, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    Nat.size_zero]
  omega

theorem finish_cost (ok : Bool) (seen checked recovered : ZMod 2)
    (st : State 180 80) (h0 : st.regs 141 = ok.toNat) (h1 : st.regs 143 = seen.val)
    (h2 : st.regs 145 = checked.val) (h3 : st.regs 142 = recovered.val) :
    (finish.run st).2 ≤ 30 := by
  have h := verdict_cost ok seen checked recovered (st.restrict finishRegs Fin.elim0) h0 h1 h2 h3
  rw [← finish_result] at h
  exact h

/-- The actual read, selected inner test, two correctors and final decision have polynomial cost. -/
theorem program_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (hs : StoredBound W st) (hb : Bounds k a ζ s W) :
    (program.run st).2 ≤ costConstant*(budget k t n m W st)^9 := by
  let B := t+4*m+k.dimension n+2^t+W+listSize (st.lists 49)+20
  have hqpos : 0 < 2^t := Nat.two_pow_pos t
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hQ := hs.lists 47 (by decide) (by decide) (by decide)
  have hA := hs.lists 48 (by decide) (by decide) (by decide)
  have hinnerSize := innerQueries_size k a s W hb.inner
  have hstdSize := standardQueries_size (k.line s.1) ζ
    (SetMultilinear.evaluationPoint m 4 s.2.1) s.2.2.1.1 s.2.2.1.2 W hb.standard
  have hP := primaryRead_run k a ζ s qs bs st hc
  have hpc := primaryReadAt_cost 125 (by decide) k a ζ s.2.1 s qs bs W st hc hs
    hc.param hb.read
  rw [show primaryReadAt 125 = primaryRead from by unfold primaryRead; rfl] at hpc
  generalize hps : (primaryRead.run st).1 = p at *
  have hcp := hc.of_frame hP.2.2
  have hsp := hs.of_frame hP.2.2
  have hp49 : listSize (p.lists 49) ≤ listSize (st.lists 49)+(W+1) := by
    rw [hP.2.1]
    have h := hb.read.2
    simpa only [listSize, List.map_cons, List.sum_cons, Nat.add_comm] using
      Nat.add_le_add_right (Nat.add_le_add_right h 1) (listSize (st.lists 49))
  have hI := selectedInner_run k a ζ s qs bs p hcp
  have hic := selectedInner_cost k a ζ s qs bs W p hcp hsp hb.inner
  have hPI := (selectedInner_reg 143 (by decide) (by decide) p).trans hP.1
  generalize his : (selectedInner.run p).1 = i at *
  have hci := hcp.of_frame hI.2.2
  have hsi := hsp.of_frame hI.2.2
  have hi49 : listSize (i.lists 49) ≤ listSize (st.lists 49)+7*(W+1) := by
    rw [hI.2.1, listSize_append, listSize_reverse]
    omega
  have hZ := standardAt_run 125 (by decide) k a ζ s.2.1 s qs bs i hci hci.param
  have hzc := standardAt_cost 125 (by decide) k a ζ s.2.1 s qs bs W i hci hsi
    hci.param hb.standard
  have hif := hP.2.2.trans hI.2.2
  rw [hif.lists 47 (by decide) (by decide) (by decide),
    hif.lists 48 (by decide) (by decide) (by decide)] at hzc
  have hPZ := (standardAt_reg 125 143 (by decide) (by decide) i).trans hPI
  have hIZ := (standardAt_reg 125 141 (by decide) (by decide) i).trans hI.1
  generalize hzs : ((standardAt 125).run i).1 = z at *
  have hcz := hci.of_frame hZ.2.2
  have hsz := hsi.of_frame hZ.2.2
  have hz49 : listSize (z.lists 49) ≤ listSize (st.lists 49)+12*(W+1) := by
    rw [hZ.2.1, listSize_append, listSize_reverse]
    omega
  have hsave := saveAndZero_cost z (by rw [hZ.1]; exact Nat.size_le.mpr (ZMod.val_lt _))
  have hcz' := hcz.of_frame (saveAndZero_frame z)
  have hsz' := hsz.of_frame (saveAndZero_frame z)
  have h145 : (saveAndZero.run z).1.regs 145 = (corrected k ζ s.2.1 s qs bs).val := by
    simpa [saveAndZero, Stmt.run, Expr.eval, Function.update, corrected] using hZ.1
  have h139 : (saveAndZero.run z).1.regs 139 = (fieldEquiv t (0 : Field t)).val := by
    change 0 = (fieldEquiv t (0 : Field t)).val
    exact (FieldExpression.code_zero (t := t)).symm
  have h141 : (saveAndZero.run z).1.regs 141 =
      (InnerBranch.verdict a (k.line s.1) (innerSeed s) qs bs).toNat := by
    simpa [saveAndZero, Stmt.run, Function.update] using hIZ
  have h143 : (saveAndZero.run z).1.regs 143 = (observed k s qs bs).val := by
    simpa [saveAndZero, Stmt.run, Function.update, observed] using hPZ
  have hsl : (saveAndZero.run z).1.lists 49 = z.lists 49 := rfl
  have hsf := hif.trans (hZ.2.2.trans (saveAndZero_frame z))
  generalize hss : (saveAndZero.run z).1 = saved at *
  have ho49 : listSize (saved.lists 49) ≤ listSize (st.lists 49)+12*(W+1) := by
    rw [hsl]; exact hz49
  have hO := standardAt_run 139 (by decide) k a ζ 0 s qs bs saved hcz' h139
  have hoc := standardAt_cost 139 (by decide) k a ζ 0 s qs bs W saved hcz' hsz'
    h139 hb.zero
  rw [hsf.lists 47 (by decide) (by decide) (by decide),
    hsf.lists 48 (by decide) (by decide) (by decide)] at hoc
  have hf0 := (standardAt_reg 139 141 (by decide) (by decide) saved).trans h141
  have hf1 := (standardAt_reg 139 143 (by decide) (by decide) saved).trans h143
  have hf2 := (standardAt_reg 139 145 (by decide) (by decide) saved).trans h145
  generalize hos : ((standardAt 139).run saved).1 = o at *
  have hfinish := finish_cost _ _ _ _ o hf0 hf1 hf2 hO.1
  have hbase : 1 ≤ 32*B := by omega
  have hlin : 32*B ≤ (32*B)^9 := Nat.le_pow (by decide)
  have htwo : (32*B)^2 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have hfive : (32*B)^5 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have hseven : (32*B)^7 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have height : (32*B)^8 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have bi : t+4*m+2^t+3*W+10 ≤ 32*B := by dsimp [B]; omega
  have be : t+m+1 ≤ 32*B := by dsimp [B]; omega
  have bz : 2^t+t+4*m+W+listSize (st.lists 47)+listSize (st.lists 48)+
      listSize (i.lists 49)+4 ≤ 32*B := by dsimp [B]; omega
  have bo : 2^t+t+4*m+W+listSize (st.lists 47)+listSize (st.lists 48)+
      listSize (saved.lists 49)+4 ≤ 32*B := by dsimp [B]; omega
  have brp : t+k.dimension n+2 ≤ 32*B := by dsimp [B]; omega
  have brl : 2^t+7 ≤ 32*B := by dsimp [B]; omega
  have brr : listSize (st.lists 47)+listSize (st.lists 48)+W+2 ≤ 32*B := by
    dsimp [B]; omega
  have bw : W+1 ≤ 32*B := by dsimp [B]; omega
  have bloader (u : ℕ) (hu : u ≤ listSize (st.lists 49)+12*(W+1)) :
      W+(4*m)*(t+1)+u+1 ≤ (32*B)^2 := by
    have hm : 4*m ≤ B := by dsimp [B]; omega
    have ht : t+1 ≤ B := by dsimp [B]; omega
    have hmul := Nat.mul_le_mul hm ht
    have hlow : W+u+1 ≤ 32*B := by dsimp [B]; omega
    nlinarith only [hmul, hlow, hB]
  have breadloader : W+listSize (st.lists 49)+1 ≤ 32*B := by dsimp [B]; omega
  have bil : 6*(W+1)+10 ≤ 32*B := by dsimp [B]; omega
  have bzl : 5*(W+1)+listSize (i.lists 49)+12 ≤ 32*B := by dsimp [B]; omega
  have bol : 5*(W+1)+listSize (saved.lists 49)+12 ≤ 32*B := by dsimp [B]; omega
  have brlinear : listSize (st.lists 49)+3*W+9 ≤ 32*B := by dsimp [B]; omega
  have ci := Nat.mul_le_mul_left InnerBranch.costConstant (Nat.pow_le_pow_left bi 9)
  have ce := Nat.mul_le_mul_left 100000000100 ((Nat.pow_le_pow_left be 5).trans hfive)
  have cz := Nat.mul_le_mul_left StandardCorrection.costConstant
    ((Nat.pow_le_pow_left bz 7).trans
      hseven)
  have co := Nat.mul_le_mul_left StandardCorrection.costConstant
    ((Nat.pow_le_pow_left bo 7).trans
      hseven)
  have crp := Nat.mul_le_mul_left (RadixCodec.passConstant+101000100)
    ((Nat.pow_le_pow_left brp 5).trans hfive)
  have crl := Nat.mul_le_mul_left
    (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400)
    ((Nat.pow_le_pow_left brl 8).trans height)
  have crr := Nat.mul_le_mul_left (QueryHistory.passConstant+40)
    ((Nat.pow_le_pow_left brr 2).trans htwo)
  have cli := Nat.mul_le_mul_left loadInnerConstant (bw.trans hlin)
  have clz := Nat.mul_le_mul_left (loaderConstant loadStandard)
    ((bloader (listSize (i.lists 49)) (by omega)).trans htwo)
  have clo := Nat.mul_le_mul_left (loaderConstant loadStandard)
    ((bloader (listSize (saved.lists 49)) ho49).trans htwo)
  have clr := Nat.mul_le_mul_left (loaderConstant loadPrimaryAddress) (breadloader.trans hlin)
  have ca := Nat.mul_le_mul_left StandardCorrection.addressConstant (bw.trans hlin)
  have hpFinal : (primaryRead.run st).2 ≤
      ((RadixCodec.passConstant+101000100)+
        (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400)+
        loaderConstant loadPrimaryAddress+StandardCorrection.addressConstant+
        (QueryHistory.passConstant+40)+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul] at hpc crp crl crr ⊢
    omega
  have hiFinal : (selectedInner.run p).2 ≤
      (loadInnerConstant+InnerBranch.costConstant+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hzFinal : ((standardAt 125).run i).2 ≤
      (100000000100+loaderConstant loadStandard+StandardCorrection.costConstant+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hoFinal : ((standardAt 139).run saved).2 ≤
      (100000000100+loaderConstant loadStandard+StandardCorrection.costConstant+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hpos : 1 ≤ (32*B)^9 := Nat.one_le_pow 9 (32*B) hbase
  conv_lhs =>
    rw [program, run_seq_snd, hps, run_seq_snd, his, run_seq_snd, hzs,
      run_seq_snd, hss, run_seq_snd, hos]
  change _ ≤ costConstant*(32*B)^9
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hpFinal hiFinal hzFinal hoFinal
  unfold costConstant
  simp only [Nat.add_mul, Nat.mul_assoc]
  clear * - hpFinal hiFinal hzFinal hoFinal hsave hfinish hpos
  omega

end PCP.Lang.LocalCorrection
