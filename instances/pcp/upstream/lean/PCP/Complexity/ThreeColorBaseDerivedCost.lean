import PCP.Complexity.ThreeColorBaseDerivedBudget
import PCP.Complexity.ThreeColorBaseOuterCost
import PCP.Complexity.NumericDerivedPolynomial

/-! Polynomial charged cost for both production derived-grid callbacks. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseDerived

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds
  ThreeColorBaseSetup ThreeColorBaseCardinal ThreeColorBaseResources LocalCorrection
  ThreeColorFullFieldSampling

attribute [local irreducible] load branch finish NumericDerived.program loadConstant

theorem branch_cost_eq (k : Certificate) (st : State 400 128) :
    ((branch k).run st).2 = ((NumericDerived.program k).run (view st)).2 := by
  unfold branch view
  exact (NumericDerived.program k).run_rename_cost _ _ (Fin.castLE_injective _)
    lists_injective st

def loaderConstant : ℕ := loadConstant .valid+loadConstant .proper

theorem loadConstant_le (k : Certificate) : loadConstant k ≤ loaderConstant := by
  cases k <;> unfold loaderConstant <;> omega

/-- Both branches have a single input-polynomial bound with arbitrary physical histories. -/
theorem program_input_cost : ∃ C d : ℕ, ∀ (k : Certificate)
    (x bits : List Bool) (qs : List ℕ) (bs : List Bool) (st : State 400 128),
    Data (ThreeColorEncoding.vertexCount x) st →
    Cardinal (fieldWidth (ThreeColorEncoding.vertexCount x))
      (dimension (ThreeColorEncoding.vertexCount x)) st →
    ThreeColorBaseSeed.Seeds (ThreeColorEncoding.vertexCount x) bits st →
    Valid (ThreeColorBaseSeed.sample (ThreeColorEncoding.vertexCount x) bits) →
    st.lists 100 = x.map Bool.toNat → st.lists 123 = qs →
    st.lists 102 = bs.map Bool.toNat →
    ((program k).run st).2 ≤ C*(x.length+listSize qs+bs.length+1)^d := by
  obtain ⟨C,d,hC⟩ := NumericDerived.program_cost_uniform
  let e := max d 1
  refine ⟨(loaderConstant+C+100)*budgetConstant^e,64*e,?_⟩
  intro k x bits qs bs st hd hc hs hv hx hq hb
  let N := ThreeColorEncoding.vertexCount x
  let B := budget N x qs bs
  have hload := load_cost k N bits x qs bs st hd hc hs hx hq hb
  have hi := load_input k N bits st hd hs hv
  have hp := load_public k N x qs bs st hd hc hx hq hb
  have hbound := load_bound k N bits x qs bs st hd hc hs hx hq hb
  have hqpos := Nat.two_pow_pos (fieldWidth N)
  have htB : fieldWidth N ≤ B := by dsimp only [B,budget]; omega
  have hnB : dimension N ≤ B := by dsimp only [B,budget]; omega
  have hWB : sourceWidth N x qs bs ≤ B := by dsimp only [B,budget]; omega
  have hqB : 2^fieldWidth N ≤ B := by dsimp only [B,budget]; omega
  have hqsB : listSize qs ≤ B := by dsimp only [B,budget]; omega
  have hbsB : bs.length ≤ B := by dsimp only [B,budget]; omega
  have hxB : x.length ≤ B := by dsimp only [B,budget]; omega
  have heB : GridEdge.budget (fieldWidth N) (dimension N) (dimension N) x ≤ B := by
    dsimp only [B,budget]; omega
  have hbranch := hC (fieldWidth N) (dimension N) (dimension N) k
    (nodes (exponent N)) (generator (exponent N)) (dimension N)
    (size_le_fieldCode (exponent N)) x (sample k N bits hv) qs bs
    (sourceWidth N x qs bs) B (view ((load k).run st).1)
    hi hp hbound htB hnB hnB hnB hWB hqB hqsB hbsB hxB heB
  rw [← branch_cost_eq] at hbranch
  have ho := branch_run k N bits x qs bs st hd hc hs hv hx hq hb
  have hfinish := finish_cost k _ _ _ ho.1 ho.2
  have hsize := queries_size k (nodes (exponent N)) (generator (exponent N))
    (FiniteAlphabetIndex.alphabet (BinaryFieldCode.fieldEquiv (fieldWidth N))
      (size_le_fieldCode (exponent N)))
    (DerivedSeed.weight k (dimension N) (size_le_fieldCode (exponent N)) x
      (sample k N bits hv)) (sample k N bits hv)
  have hquery : QueryAddress.width (fieldWidth N) (dimension N) (dimension N) 4 ≤ B := by
    dsimp only [B,budget]; omega
  have he : 0 < e := by dsimp [e]; omega
  have hpow : B+1 ≤ (B+1)^e := Nat.le_pow he
  have hpowd : (B+1)^d ≤ (B+1)^e := Nat.pow_le_pow_right (by omega) (le_max_left d 1)
  have h1 : 1 ≤ (B+1)^e := Nat.one_le_pow _ _ (by omega)
  have hload' : ((load k).run st).2 ≤ loaderConstant*(B+1)^e :=
    hload.trans (Nat.mul_le_mul (loadConstant_le k) ((Nat.add_le_add_right hWB 1).trans hpow))
  have hbranch' := hbranch.trans (Nat.mul_le_mul_left _ hpowd)
  have hfinish' : ((finish k).run ((branch k).run ((load k).run st).1).1).2 ≤
      49*(B+1)^e := by
    change listSize _ ≤ 44*(QueryAddress.width (fieldWidth N) (dimension N)
      (dimension N) 4+1) at hsize
    have hf := hfinish.trans (Nat.add_le_add_right hsize 5)
    nlinarith only [hf,hquery,hpow,h1]
  have htotal := ThreeColorBaseOuter.compose_cost_bound (load k) (branch k) (finish k) st
    loaderConstant C 49 ((B+1)^e) hload' hbranch' hfinish' h1
  have htotal' : ((program k).run st).2 ≤ (loaderConstant+C+100)*(B+1)^e :=
    htotal.trans (Nat.mul_le_mul_right _ (by omega))
  have hbudget := budget_input_bound x qs bs
  change B+1 ≤ budgetConstant*(x.length+listSize qs+bs.length+1)^64 at hbudget
  exact (htotal'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbudget e))).trans_eq (by
    rw [mul_pow,← pow_mul]
    simp only [Nat.mul_assoc])

end PCP.Lang.ThreeColorBaseDerived
