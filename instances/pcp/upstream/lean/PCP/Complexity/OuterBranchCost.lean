import PCP.Complexity.OuterBranchLang
import PCP.Complexity.OuterBranchPrimaryCost
import PCP.Complexity.OuterBranchInnerCost
import PCP.Complexity.OuterBranchStandardCost
import PCP.Complexity.OuterBranchReadCost

/-!
# Polynomial charged cost of the complete outer encoded-line branch
-/

set_option maxRecDepth 1024

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t] [NeZero m]

attribute [local irreducible] primaryHadamard selectedInner standardAt primaryRead
  loadStandard loadPrimaryAddress loadPrimaryConstant loadInnerConstant loaderConstant
  HadamardRow.branchConstant InnerBranch.costConstant StandardCorrection.costConstant
  RadixCodec.passConstant BooleanLabelTransform.queryConstant WordCodec.passConstant
  StandardCorrection.addressConstant QueryHistory.passConstant

structure Bounds (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (W : ℕ) : Prop where
  primaryPayload : ∀ i,
    Nat.size ((k.primary (m := m) s.1.1).payload (t := t) (fieldEquiv t) i) ≤ W
  primary : ∀ q ∈ primaryQueries k s, Nat.size q ≤ W
  inner : InnerBranch.Bounds a (k.line s.1) (innerSeed s) W
  standard : StandardCorrection.QueryBound (k.line s.1) ζ
    (SetMultilinear.evaluationPoint m 4 s.2.1) s.2.2.1.1 s.2.2.1.2 W
  read : PrimaryBound (m := m) k (PolynomialLine.point s.1.1 s.1.2 s.2.1)
    (BooleanCoefficientArithmetic.homogeneousIndex k.degree_pos s.2.2.1.2) W

def costConstant : ℕ := loadPrimaryConstant + HadamardRow.branchConstant + loadInnerConstant +
  InnerBranch.costConstant + 100000000100 + loaderConstant loadStandard +
  StandardCorrection.costConstant + (RadixCodec.passConstant+101000100) +
  (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400) +
  loaderConstant loadPrimaryAddress + StandardCorrection.addressConstant +
  (QueryHistory.passConstant+40) + loaderConstant combine*2 + 100

def budget (k : Kind) (t n m W : ℕ) (st : State 180 80) : ℕ :=
  32*(t+4*m+k.dimension n+2^t+W+listSize (st.lists 49)+20)

theorem combine_cost (st : State 180 80)
    (h140 : Nat.size (st.regs 140) ≤ 1) (h141 : Nat.size (st.regs 141) ≤ 1)
    (h142 : Nat.size (st.regs 142) ≤ 1) (h143 : Nat.size (st.regs 143) ≤ 1) :
    (combine.run st).2 ≤ loaderConstant combine*2 := by
  unfold loaderConstant
  apply loopFree_cost_le combine (by decide) st 1
  · intro i hi
    have hh : ∀ j ∈ combine.uses, j = 140 ∨ j = 141 ∨ j = 142 ∨ j = 143 := by decide
    rcases hh i hi with rfl | rfl | rfl | rfl <;> assumption
  · intro i hi
    simp [combine, Stmt.lUses] at hi

attribute [local irreducible] combine

/-- The five actual stateful stages are composed without expanding their arithmetic syntax.
The budget is polynomial in field size, dimensions and stored numeric input sizes. -/
theorem program_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (hs : StoredBound W st) (hb : Bounds k a ζ s W) :
    (program.run st).2 ≤ costConstant*(budget k t n m W st)^9 := by
  let B := t+4*m+k.dimension n+2^t+W+listSize (st.lists 49)+20
  have hqpos : 0 < 2^t := Nat.two_pow_pos t
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hdeg := k.degree_le
  have hQ := hs.lists 47 (by decide) (by decide) (by decide)
  have hA := hs.lists 48 (by decide) (by decide) (by decide)
  have hprimSize := primaryQueries_size k s W hb.primary
  have hinnerSize := innerQueries_size k a s W hb.inner
  have hstdSize := standardQueries_size (k.line s.1) ζ
    (SetMultilinear.evaluationPoint m 4 s.2.1) s.2.2.1.1 s.2.2.1.2 W hb.standard
  have hp := primaryHadamard_run k a ζ s qs bs st hc
  have hpc := primaryHadamard_cost k a ζ s qs bs W st hc hs hb.primaryPayload hb.primary
  generalize hP : (primaryHadamard.run st).1 = p at *
  have hcp := hc.of_frame hp.2.2
  have hsp := hs.of_frame hp.2.2
  have hp49 : listSize (p.lists 49) ≤ listSize (st.lists 49)+10*(W+1) := by
    rw [hp.2.1, listSize_append, listSize_reverse]
    nlinarith only [hprimSize, hdeg, Nat.zero_le W]
  have hi := selectedInner_run k a ζ s qs bs p hcp
  have hic := selectedInner_cost k a ζ s qs bs W p hcp hsp hb.inner
  have hi140 := (selectedInner_reg 140 (by decide) (by decide) p).trans hp.1
  generalize hI : (selectedInner.run p).1 = i at *
  have hci := hcp.of_frame hi.2.2
  have hsi := hsp.of_frame hi.2.2
  have hi49 : listSize (i.lists 49) ≤ listSize (st.lists 49)+16*(W+1) := by
    rw [hi.2.1, listSize_append, listSize_reverse]
    omega
  have hstd := standardAt_run 125 (by decide) k a ζ s.2.1 s qs bs i hci hci.param
  have hstdc := standardAt_cost 125 (by decide) k a ζ s.2.1 s qs bs W i hci hsi
    hci.param hb.standard
  have hs140 := (standardAt_reg 125 140 (by decide) (by decide) i).trans hi140
  have hs141 := (standardAt_reg 125 141 (by decide) (by decide) i).trans hi.1
  have hif := hp.2.2.trans hi.2.2
  rw [hif.lists 47 (by decide) (by decide) (by decide),
    hif.lists 48 (by decide) (by decide) (by decide)] at hstdc
  generalize hS : ((standardAt 125).run i).1 = u at *
  have hcu := hci.of_frame hstd.2.2
  have hsu := hsi.of_frame hstd.2.2
  have hu49 : listSize (u.lists 49) ≤ listSize (st.lists 49)+21*(W+1) := by
    rw [hstd.2.1, listSize_append, listSize_reverse]
    omega
  have hr := primaryRead_run k a ζ s qs bs u hcu
  have hrc := primaryReadAt_cost 125 (by decide) k a ζ s.2.1 s qs bs W u hcu hsu
    hcu.param hb.read
  rw [show primaryReadAt 125 = primaryRead from by unfold primaryRead; rfl] at hrc
  have huf := hif.trans hstd.2.2
  rw [huf.lists 47 (by decide) (by decide) (by decide),
    huf.lists 48 (by decide) (by decide) (by decide)] at hrc
  have hr140 := (primaryRead_reg 140 (by decide) (by decide) (by decide)
    (by decide) (by decide) u).trans hs140
  have hr141 := (primaryRead_reg 141 (by decide) (by decide) (by decide)
    (by decide) (by decide) u).trans hs141
  have hr142 := (primaryRead_reg 142 (by decide) (by decide) (by decide)
    (by decide) (by decide) u).trans hstd.1
  generalize hR : (primaryRead.run u).1 = v at *
  have hcomb := combine_cost v
    (by rw [hr140]; exact InnerBranch.bool_size _)
    (by rw [hr141]; exact InnerBranch.bool_size _)
    (by rw [hr142]; exact Nat.size_le.mpr (ZMod.val_lt _))
    (by rw [hr.1]; exact Nat.size_le.mpr (ZMod.val_lt _))
  have hbase : 1 ≤ 32*B := by omega
  have hlin : 32*B ≤ (32*B)^9 := Nat.le_pow (by decide)
  have htwo : (32*B)^2 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have hfive : (32*B)^5 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have hseven : (32*B)^7 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have height : (32*B)^8 ≤ (32*B)^9 := Nat.pow_le_pow_right hbase (by decide)
  have bp : 2^t+3*k.degree+W+5 ≤ 32*B := by dsimp [B]; omega
  have bi : t+4*m+2^t+3*W+10 ≤ 32*B := by dsimp [B]; omega
  have be : t+m+1 ≤ 32*B := by dsimp [B]; omega
  have bs : 2^t+t+4*m+W+listSize (st.lists 47)+listSize (st.lists 48)+
      listSize (i.lists 49)+4 ≤ 32*B := by dsimp [B]; omega
  have brp : t+k.dimension n+2 ≤ 32*B := by dsimp [B]; omega
  have brl : 2^t+7 ≤ 32*B := by dsimp [B]; omega
  have brr : listSize (st.lists 47)+listSize (st.lists 48)+W+2 ≤ 32*B := by
    dsimp [B]; omega
  have bw : W+1 ≤ 32*B := by dsimp [B]; omega
  have bloader : W+(4*m)*(t+1)+listSize (i.lists 49)+1 ≤ (32*B)^2 := by
    have hm : 4*m ≤ B := by dsimp [B]; omega
    have ht : t+1 ≤ B := by dsimp [B]; omega
    have hmul := Nat.mul_le_mul hm ht
    have hlow : W+listSize (i.lists 49)+1 ≤ 32*B := by dsimp [B]; omega
    nlinarith only [hmul, hlow, hB]
  have breadloader : W+listSize (u.lists 49)+1 ≤ 32*B := by dsimp [B]; omega
  have bpl : (2*k.degree+4)*(W+1)+10 ≤ 32*B := by
    have h' : (2*k.degree+4)*(W+1) ≤ 10*(W+1) :=
      Nat.mul_le_mul_right (W+1) (by omega)
    dsimp [B]
    omega
  have bil : 6*(W+1)+10 ≤ 32*B := by dsimp [B]; omega
  have bsl : 5*(W+1)+listSize (i.lists 49)+12 ≤ 32*B := by dsimp [B]; omega
  have brlinear : listSize (u.lists 49)+3*W+9 ≤ 32*B := by dsimp [B]; omega
  have cp := Nat.mul_le_mul_left HadamardRow.branchConstant (Nat.pow_le_pow_left bp 9)
  have ci := Nat.mul_le_mul_left InnerBranch.costConstant (Nat.pow_le_pow_left bi 9)
  have ce := Nat.mul_le_mul_left 100000000100 ((Nat.pow_le_pow_left be 5).trans hfive)
  have cs := Nat.mul_le_mul_left StandardCorrection.costConstant
    ((Nat.pow_le_pow_left bs 7).trans
      hseven)
  have crp := Nat.mul_le_mul_left (RadixCodec.passConstant+101000100)
    ((Nat.pow_le_pow_left brp 5).trans hfive)
  have crl := Nat.mul_le_mul_left
    (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400)
    ((Nat.pow_le_pow_left brl 8).trans height)
  have crr := Nat.mul_le_mul_left (QueryHistory.passConstant+40)
    ((Nat.pow_le_pow_left brr 2).trans htwo)
  have clp := Nat.mul_le_mul_left loadPrimaryConstant (bw.trans hlin)
  have cli := Nat.mul_le_mul_left loadInnerConstant (bw.trans hlin)
  have cls := Nat.mul_le_mul_left (loaderConstant loadStandard) (bloader.trans htwo)
  have clr := Nat.mul_le_mul_left (loaderConstant loadPrimaryAddress) (breadloader.trans hlin)
  have ca := Nat.mul_le_mul_left StandardCorrection.addressConstant (bw.trans hlin)
  have cc := Nat.mul_le_mul_left (loaderConstant combine*2)
    (Nat.one_le_pow 9 (32*B) hbase)
  have hpFinal : (primaryHadamard.run st).2 ≤
      (loadPrimaryConstant+HadamardRow.branchConstant+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hiFinal : (selectedInner.run p).2 ≤
      (loadInnerConstant+InnerBranch.costConstant+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hsFinal : ((standardAt 125).run i).2 ≤
      (100000000100+loaderConstant loadStandard+StandardCorrection.costConstant+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hrFinal : (primaryRead.run u).2 ≤
      ((RadixCodec.passConstant+101000100)+
        (BooleanLabelTransform.queryConstant+3*WordCodec.passConstant+400)+
        loaderConstant loadPrimaryAddress+StandardCorrection.addressConstant+
        (QueryHistory.passConstant+40)+1)*(32*B)^9 := by
    simp only [Nat.add_mul, Nat.one_mul] at hrc crp crl crr ⊢
    omega
  have hcFinal : (combine.run v).2 ≤ (loaderConstant combine*2)*(32*B)^9 := by
    simp only [Nat.mul_one] at cc
    exact hcomb.trans cc
  have hpos : 1 ≤ (32*B)^9 := Nat.one_le_pow 9 (32*B) hbase
  conv_lhs =>
    rw [program, run_seq_snd, hP, run_seq_snd, hI, run_seq_snd, hS, run_seq_snd, hR]
  change _ ≤ costConstant*(32*B)^9
  simp only [Nat.add_mul, Nat.one_mul] at hpFinal hiFinal hsFinal hrFinal
  unfold costConstant
  simp only [Nat.add_mul]
  clear * - hpFinal hiFinal hsFinal hrFinal hcFinal hpos
  omega


end PCP.Lang.OuterBranch
