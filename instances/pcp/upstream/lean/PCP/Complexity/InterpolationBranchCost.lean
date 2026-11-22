import PCP.Complexity.InterpolationBranchLang
import PCP.Complexity.InterpolationBranchPassCost

/-!
# Polynomial cost of the complete interpolation branch
-/

namespace PCP.Lang.InterpolationBranch

open PCP.Algebraic BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] nodeStep firstQuery passes queries verdict

def costConstant : ℕ := 6*pointCostConstant+6*labelCostConstant+6*emitCostConstant+
  5*InterpolationWeightLoad.constant+8000*(QueryHistory.passConstant+66)+250

def budget (t m W : ℕ) (st : State 100 40) : ℕ :=
  t+4*m+2^t+W+listSize (st.lists 36)+listSize (st.lists 37)+5

theorem passes_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (is : List (Fin 5)) (W : ℕ) (st : State 100 40) (hc : Context a z u v w site st)
    (hb : QueryBound a z u v w site W) :
    ((passes is).run st).2 ≤ is.length*(nodeBudget t m W+1)+1 := by
  induction is generalizing st with
  | nil => simp [passes, Stmt.run]
  | cons i is ih =>
      have hs := nodeStep_run a z u v w site i st hc
      have hsc := nodeStep_cost a z u v w site i W st hc hb
      have hi := ih ((nodeStep i).run st).1 (hc.of_frame hs.2)
      rw [passes, run_seq_snd, List.length_cons]
      nlinarith only [hsc, hi]

theorem nodeQueries_size (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (is : List (Fin 5)) (W : ℕ) (hb : QueryBound a z u v w site W) :
    listSize (is.flatMap (nodeQueries a z u v w site)) ≤ is.length*(W+1) := by
  induction is with
  | nil => simp [listSize]
  | cons i is ih =>
      have hsize := (hb.2 i).2
      change Nat.size (nodeAddress a z u v w site i) ≤ W at hsize
      rw [List.flatMap_cons, listSize_append, List.length_cons]
      by_cases hzero : FieldQueryArithmetic.interpolationWeight a z i = 0
      · simp only [nodeQueries, hzero, ↓reduceIte, listSize, List.map_nil, List.sum_nil]
        dsimp only [listSize] at ih
        nlinarith only [ih]
      · simp only [nodeQueries, hzero, ↓reduceIte, listSize, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        dsimp only [listSize] at ih
        nlinarith only [ih, hsize]

theorem queryCodes_size (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (W : ℕ) (hb : QueryBound a z u v w site W) :
    listSize (queryCodes a z u v w site) ≤ 6*(W+1) := by
  have hs := nodeQueries_size a z u v w site (List.finRange 5) W hb
  simp only [List.length_finRange] at hs
  have hf := hb.1.2
  change Nat.size (firstAddress z u v w site) ≤ W at hf
  rw [queryCodes_eq]
  change Nat.size (firstAddress z u v w site)+1+
    listSize ((List.finRange 5).flatMap (nodeQueries a z u v w site)) ≤ _
  omega

set_option maxRecDepth 1024 in
-- The fixed five-pass AST is nested; arithmetic bodies remain opaque in the proof.
theorem queries_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (W : ℕ) (st : State 100 40) (hc : Context a z u v w site st)
    (hb : QueryBound a z u v w site W) :
    (queries.run st).2 ≤ queryBudget t m W+5*(nodeBudget t m W+1)+6*(W+1)+6 := by
  let s := setList st 20 []
  have hsf : Frame st s := by
    simpa only [hc.empty] using Frame.copy st 7 20 (by decide) (by decide) (by decide)
  have hsc := hc.of_frame hsf
  have hf := firstQuery_run a z u v w site s hsc
  have hfc := firstQuery_cost a z u v w site W s hsc hb
  have hp := passes_cost a z u v w site (List.finRange 5) W (firstQuery.run s).1
    (hsc.of_frame hf.2) hb
  simp only [List.length_finRange] at hp
  let out := ((passes (List.finRange 5)).run (firstQuery.run s).1).1
  have hout : (out.lists 20).reverse = queryCodes a z u v w site := by
    simpa only [queries, run_seq_fst, run_copy_fst, hc.empty, run_rev_fst,
      setList_lists, Function.update_self] using (queries_run a z u v w site st hc).1
  have hsize : listSize (out.lists 20) ≤ 6*(W+1) := by
    have h := queryCodes_size a z u v w site W hb
    rw [← hout] at h
    simpa only [listSize, List.map_reverse, List.sum_reverse] using h
  have hcost : (queries.run st).2 = 1+((firstQuery.run s).2+
      (((passes (List.finRange 5)).run (firstQuery.run s).1).2+
        (listSize (out.lists 20)+1)+1)+1)+1 := by
    simp only [queries, run_seq_snd, run_copy_snd, run_copy_fst, hc.empty,
      run_rev_snd, listSize, List.map_nil, List.sum_nil]
    rfl
  rw [hcost]
  omega

theorem verdict_cost (st : State 100 40) :
    (verdict.run st).2 ≤ (QueryHistory.passConstant+66)*
      (3*(listSize (st.lists 36)+listSize (st.lists 37)+listSize (st.lists 20)+1)+2)^3 := by
  have hp := HistoryParity.program_cost (st.restrict (Fin.castLE (by decide)) verdictLists)
  rw [← congrArg Prod.snd (verdict_result st)] at hp
  exact hp

/-- A degree-seven bound includes all six possible reads, exact zero-weight omission,
field arithmetic, physical address construction, and actual history parity. -/
theorem program_cost (a : Fin 5 → Field t) (z : Field t) (u v : Point t m)
    (w : Fin t → ZMod 2) (site : StandardCorrection.Site (Field t) n)
    (W : ℕ) (st : State 100 40) (hc : Context a z u v w site st)
    (hb : QueryBound a z u v w site W) :
    (program.run st).2 ≤ costConstant*(budget t m W st)^7 := by
  let B := budget t m W st
  have hqpos : 0 < 2^t := Nat.two_pow_pos t
  have hB : 1 ≤ B := by dsimp [B, budget]; omega
  have hlin : B ≤ B^7 := Nat.le_self_pow (by decide) B
  have hthree : B^3 ≤ B^7 := Nat.pow_le_pow_right hB (by decide)
  have hp5 : (t+4*m+2)^5 ≤ B^7 :=
    (Nat.pow_le_pow_left (by dsimp [B, budget]; omega) 5).trans
      (Nat.pow_le_pow_right hB (by decide))
  have hl7 : (2^t+4)^7 ≤ B^7 := Nat.pow_le_pow_left (by dsimp [B, budget]; omega) _
  have hw4 : (t+1)^4 ≤ B^7 :=
    (Nat.pow_le_pow_left (by dsimp [B, budget]; omega) 4).trans
      (Nat.pow_le_pow_right hB (by decide))
  have hW : W+1 ≤ B := by dsimp [B, budget]; omega
  have ht : t+1 ≤ B := by dsimp [B, budget]; omega
  have hq := queries_cost a z u v w site W st hc hb
  have hsem := queries_run a z u v w site st hc
  have hsize := queryCodes_size a z u v w site W hb
  have hv := verdict_cost (queries.run st).1
  rw [hsem.2.lists 36 (by decide), hsem.2.lists 37 (by decide), hsem.1] at hv
  have hhist : 3*(listSize (st.lists 36)+listSize (st.lists 37)+
      listSize (queryCodes a z u v w site)+1)+2 ≤ 20*B := by
    dsimp [B, budget]; omega
  have hv' := hv.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhist 3))
  have hv'' : (verdict.run (queries.run st).1).2 ≤
      8000*(QueryHistory.passConstant+66)*B^7 := by
    have hh := Nat.mul_le_mul_left (8000*(QueryHistory.passConstant+66)) hthree
    rw [mul_pow] at hv'
    norm_num at hv'
    nlinarith only [hv', hh]
  have hp := Nat.mul_le_mul_left pointCostConstant hp5
  have hl := Nat.mul_le_mul_left labelCostConstant hl7
  have hw := Nat.mul_le_mul_left (InterpolationWeightLoad.constant+30) hw4
  have he := Nat.mul_le_mul_left emitCostConstant (hW.trans hlin)
  have hpos : 1 ≤ B^7 := Nat.one_le_pow _ _ hB
  rw [program, run_seq_snd]
  change _ ≤ costConstant*B^7
  dsimp only [queryBudget, nodeBudget] at hq
  dsimp only [costConstant]
  nlinarith only [hq, hv'', hp, hl, hw, he, hW, ht, hlin, hpos]

end PCP.Lang.InterpolationBranch
