import PCP.Complexity.ThreeColorBaseDifference
import PCP.Complexity.ThreeColorBaseOuterResources

/-! # Charged cost of the production difference callback and its trace accumulation -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseDifference

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds
  ThreeColorBaseSetup ThreeColorBaseCardinal ThreeColorBaseResources

open ThreeColorBaseOuter (sourceWidth budget budgetConstant budget_bound)

def loadConstant : ℕ := load.C*(load.width+load.csize+1)

theorem load_cost (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    (load.run st).2 ≤ loadConstant*(sourceWidth N qs bs+1) := by
  have hmeta : metadataWidth N ≤ sourceWidth N qs bs := by unfold sourceWidth; omega
  apply loopFree_cost_le load (by decide) st (sourceWidth N qs bs)
  · intro i hi
    have he : (320 ≤ i.val ∧ i.val < 328) ∨ (328 ≤ i.val ∧ i.val < 334) ∨ i = 356 := by
      simp [load, Stmt.uses, Stmt.mustW, Expr.uses] at hi
      omega
    rcases he with h | h | rfl
    · exact (data_regs N st hd i h.1 h.2).trans hmeta
    · exact (cardinal_regs N st hc i h.1 h.2).trans hmeta
    · exact (seed_regs N bits st hs 356 (by decide) (by decide)).trans hmeta
  · intro L hL
    have he : L = 122 ∨ L = 123 ∨ L = 102 := by simpa [load, Stmt.lUses] using hL
    rcases he with rfl | rfl | rfl
    · exact (data_lists N st hd 122 (by decide) (by decide)).trans hmeta
    · rw [hq]; unfold sourceWidth; omega
    · rw [hb]; exact (ThreeColorContext.bitList_size bs).trans (by unfold sourceWidth; omega)

theorem load_bound (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    NumericDifference.SourceBound (sourceWidth N qs bs)
      ((load.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  have hmeta : metadataWidth N ≤ sourceWidth N qs bs := by unfold sourceWidth; omega
  have hr (i : Fin 400) (hi : 320 ≤ i.val) (hj : i.val < 334) :
      Nat.size (st.regs i) ≤ sourceWidth N qs bs := by
    by_cases h : i.val < 328
    · exact (data_regs N st hd i hi h).trans hmeta
    · exact (cardinal_regs N st hc i (by omega) hj).trans hmeta
  have hseed := (seed_regs N bits st hs 356 (by decide) (by decide)).trans hmeta
  constructor
  · intro i hi hj
    have he : i = 100 ∨ i = 101 ∨ i = 102 ∨ i = 103 ∨ i = 104 ∨ i = 105 ∨
        i = 106 ∨ i = 107 ∨ i = 108 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp [State.restrict, load, Stmt.run, Expr.eval, Function.update]
    all_goals first | exact hr _ (by decide) (by decide) | exact hseed
  · intro L hi hj
    have he : L = 32 ∨ L = 33 ∨ L = 34 := by omega
    rcases he with rfl | rfl | rfl
    all_goals dsimp [State.restrict, load, Stmt.run, Expr.eval, Function.update]
    · exact (data_lists N st hd 122 (by decide) (by decide)).trans hmeta
    · rw [hq]; unfold sourceWidth; omega
    · rw [hb]; exact (ThreeColorContext.bitList_size bs).trans (by unfold sourceWidth; omega)

theorem queries_size {t n m : ℕ} [NeZero t] (s : NumericDifference.Sample t n) :
    listSize (NumericDifference.queries m s) ≤ 3*(QueryAddress.width t n m 4+1) := by
  have hs (q : BinaryDifferenceConsistency.Query (NumericDifference.Field t) (Fin n) t 3) :
      Nat.size (NumericDifference.index t n m q) ≤ QueryAddress.width t n m 4 :=
    QueryAddress.address_size (BinaryFieldCode.fieldEquiv t)
      (ThreeColorVerifier.differenceCheckQuery q)
  unfold NumericDifference.queries
  simp only [ComputableBinaryDifferenceConsistency.queries, List.map_cons, List.map_nil,
    listSize, List.sum_cons, List.sum_nil]
  have h0 := hs (.inr (Sum.elim s.1.1 s.1.2,BooleanCoefficientArithmetic.homogeneousIndex
    (by decide : 1 ≤ 3) s.2))
  have h1 := hs (.inl (s.1.1,BooleanCoefficientArithmetic.homogeneousIndex
    (by decide : 1 ≤ 3) s.2))
  have h2 := hs (.inl (s.1.2,BooleanCoefficientArithmetic.homogeneousIndex
    (by decide : 1 ≤ 3) s.2))
  omega

theorem finish_cost (v : Bool) (qs : List ℕ) (st : State 400 128)
    (hv : st.regs 13 = v.toNat) (hq : st.lists 24 = qs) :
    (finish.run st).2 ≤ listSize qs+5 := by
  cases v <;> simp [finish, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, hv, hq] <;> omega

def costConstant : ℕ := loadConstant+NumericDifference.costConstant+54*QueryAddress.widthConstant+10

attribute [local irreducible] load finish branch NumericDifference.program loadConstant
  NumericDifference.costConstant QueryAddress.widthConstant

theorem program_cost (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    (program.run st).2 ≤ costConstant*(budget N qs bs)^8 := by
  have hp := load_public N qs bs st hd hc hq hb
  have hseed := load_seed N bits st hs
  have hbound := load_bound N bits qs bs st hd hc hs hq hb
  have hload := load_cost N bits qs bs st hd hc hs hq hb
  have hbranch := NumericDifference.program_cost (sample N bits) qs bs (sourceWidth N qs bs)
    _ hp hbound hseed
  rw [← call_result (by decide) (by decide) NumericDifference.program] at hbranch
  rw [show call (by decide) (by decide) NumericDifference.program = branch by
    unfold branch; rfl] at hbranch
  have harg : NumericDifference.budget (binaryDimension (exponent N)) (size (exponent N))
      (size (exponent N)) (sourceWidth N qs bs) ≤ budget N qs bs := by
    dsimp [NumericDifference.budget,budget,fieldWidth,dimension]
    omega
  have hbranch' := hbranch.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 8))
  obtain ⟨htrace,hv⟩ := branch_run N bits qs bs st hd hc hs hq hb
  have hfinish := finish_cost _ _ _ hv htrace
  have hsize := queries_size (m := size (exponent N)) (sample N bits)
  change listSize _ ≤ 3*(QueryAddress.width (fieldWidth N) (dimension N) (dimension N) 4+1)
    at hsize
  have hwidth := query_width N
  let B := budget N qs bs
  have hqpos := Nat.two_pow_pos (fieldWidth N)
  have hB : 1 ≤ B := by dsimp [B,budget]; omega
  have hsource : sourceWidth N qs bs+1 ≤ B := by dsimp [B,budget]; omega
  have hmeta : metadataWidth N ≤ B := by dsimp [B,budget,sourceWidth]; omega
  have hcore : (coreBound N)^2 ≤ B := by
    apply le_trans _ hmeta
    have hh := Nat.pow_le_pow_left (by omega : coreBound N ≤ coreBound N+N+1) 2
    exact hh.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 100000000))
  have hwidth' := hwidth.trans (Nat.mul_le_mul_left _ hcore)
  have hpow : B ≤ B^8 := Nat.le_pow (by decide)
  have hload' := hload.trans (Nat.mul_le_mul_left _ (hsource.trans hpow))
  have h1 : 1 ≤ B^8 := Nat.one_le_pow _ _ hB
  have hfinish' : (finish.run (branch.run (load.run st).1).1).2 ≤
      (54*QueryAddress.widthConstant+8)*B^8 := by
    have hh := Nat.mul_le_mul_left (18*QueryAddress.widthConstant) hpow
    nlinarith only [hfinish,hsize,hwidth',hh,h1]
  simp only [program, run_seq_snd]
  change _ ≤ costConstant*B^8
  change _ ≤ NumericDifference.costConstant*B^8 at hbranch'
  unfold costConstant
  nlinarith only [hload',hbranch',hfinish',h1]

theorem program_input_cost (x bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data (ThreeColorEncoding.vertexCount x) st)
    (hc : Cardinal (fieldWidth (ThreeColorEncoding.vertexCount x))
      (dimension (ThreeColorEncoding.vertexCount x)) st)
    (hs : ThreeColorBaseSeed.Seeds (ThreeColorEncoding.vertexCount x) bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    (program.run st).2 ≤ costConstant*budgetConstant^8*
      (x.length+listSize qs+bs.length+1)^192 := by
  have h := program_cost _ bits qs bs st hd hc hs hq hb
  have hh := budget_bound (ThreeColorEncoding.vertexCount x) qs bs
  have hN := ThreeColorEncoding.size_le_length x
  have hbase : ThreeColorEncoding.vertexCount x+listSize qs+bs.length+1 ≤
      x.length+listSize qs+bs.length+1 := by omega
  have hb' := hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 24))
  exact (h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb' 8))).trans_eq (by
    rw [mul_pow, ← pow_mul]
    simp only [Nat.mul_assoc])

end PCP.Lang.ThreeColorBaseDifference
