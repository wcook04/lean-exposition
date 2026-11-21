import PCP.Complexity.ThreeColorBaseOuterResources

/-! # Charged polynomial cost of the complete production outer callbacks -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseOuter

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds
  ThreeColorBaseSetup ThreeColorBaseCardinal ThreeColorBaseResources OuterBranch

attribute [local irreducible] load finish branch NumericOuter.program loadConstant
  NumericOuter.costConstant
  QueryAddress.widthConstant

theorem compose_cost_bound (p q r : Stmt 400 128) (st : State 400 128)
    (C D E B : ℕ) (hp : (p.run st).2 ≤ C * B)
    (hq : (q.run (p.run st).1).2 ≤ D * B)
    (hr : (r.run (q.run (p.run st).1).1).2 ≤ E * B) (hB : 1 ≤ B) :
    ((Stmt.seq p (.seq q r)).run st).2 ≤ (C+D+E+2)*B := by
  simp only [run_seq_snd]
  nlinarith only [hp,hq,hr,hB]

theorem branch_cost_eq (k : Kind) (st : State 400 128) :
    ((branch k).run st).2 = ((NumericOuter.program k).run
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))).2 := by
  unfold branch ThreeColorBaseSetup.call
  exact (NumericOuter.program k).run_rename_cost _ _ (Fin.castLE_injective _)
    (Fin.castLE_injective _) st

theorem numeric_budget_eq (N : ℕ) (qs : List ℕ) (bs : List Bool) (st : State 400 128)
    (he : st.lists 49 = []) :
    NumericOuter.budget (fieldWidth N) (dimension N) (dimension N) (sourceWidth N qs bs) qs bs
      ((st.restrict (Fin.castLE (by decide : 180 ≤ 400))
        (Fin.castLE (by decide : 80 ≤ 128))).lists 49) = budget N qs bs := by
  change NumericOuter.budget _ _ _ _ _ _ (st.lists 49) = _
  rw [he]
  simp only [NumericOuter.budget,budget,listSize,List.map_nil,List.sum_nil,Nat.add_zero]
  omega

theorem branch_cost (k : Kind) (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    ((branch k).run ((load k).run st).1).2 ≤
      NumericOuter.costConstant k*(budget N qs bs)^18 := by
  have hp := load_public k N qs bs st hd hc hq hb
  have hseed := load_seed k N bits st hs
  have hbound := load_bound k N bits qs bs st hd hc hs hq hb
  have hbranch := NumericOuter.program_cost_uniform k (nodes (exponent N))
    (generator (exponent N)) (sample k N bits) qs bs (sourceWidth N qs bs) _ hp hbound hseed
  rw [← branch_cost_eq k ((load k).run st).1] at hbranch
  change ((branch k).run ((load k).run st).1).2 ≤ NumericOuter.costConstant k*
    (NumericOuter.budget (fieldWidth N) (dimension N) (dimension N) (sourceWidth N qs bs)
      qs bs ((((load k).run st).1.restrict (Fin.castLE (by decide : 180 ≤ 400))
        (Fin.castLE (by decide : 80 ≤ 128))).lists 49))^18 at hbranch
  rw [numeric_budget_eq N qs bs _ (load_empty k st hd.empty)] at hbranch
  exact hbranch

theorem program_cost (k : Kind) (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    ((program k).run st).2 ≤ costConstant k*(budget N qs bs)^18 := by
  have hload := load_cost k N bits qs bs st hd hc hs hq hb
  have hbranch' := branch_cost k N bits qs bs st hd hc hs hq hb
  obtain ⟨hv,htrace⟩ := branch_run k N bits qs bs st hd hc hs hq hb
  have hfinish := finish_cost k _ _ _ hv htrace
  have hsize := queryCodes_size k (nodes (exponent N)) (generator (exponent N)) (sample k N bits)
  change listSize _ ≤ 26*(QueryAddress.width (fieldWidth N) (dimension N) (dimension N) 4+1)
    at hsize
  have hwidth := query_width N
  have hqpos := Nat.two_pow_pos (fieldWidth N)
  let B := budget N qs bs
  have hB : 1 ≤ B := by dsimp [B,budget]; omega
  have hsource : sourceWidth N qs bs+1 ≤ B := by dsimp [B,budget]; omega
  have hmeta : metadataWidth N ≤ B := by dsimp [B,budget,sourceWidth]; omega
  have hcore : (coreBound N)^2 ≤ B := by
    apply le_trans _ hmeta
    have hh := Nat.pow_le_pow_left (by omega : coreBound N ≤ coreBound N+N+1) 2
    exact hh.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 100000000))
  have hwidth' := hwidth.trans (Nat.mul_le_mul_left _ hcore)
  have hpow : B ≤ B^18 := Nat.le_pow (by decide)
  have hload' := hload.trans (Nat.mul_le_mul_left _ (hsource.trans hpow))
  have h1 : 1 ≤ B^18 := Nat.one_le_pow _ _ hB
  have hfinish' : ((finish k).run ((branch k).run ((load k).run st).1).1).2 ≤
      (936*QueryAddress.widthConstant+59)*B^18 := by
    have hh := Nat.mul_le_mul_left (18*QueryAddress.widthConstant) hpow
    nlinarith only [hfinish,hsize,hwidth',hh,h1]
  change _ ≤ NumericOuter.costConstant k*B^18 at hbranch'
  have htotal := compose_cost_bound (load k) (branch k) (finish k) st
    (loadConstant k) (NumericOuter.costConstant k) (936*QueryAddress.widthConstant+59)
    (B^18) hload' hbranch' hfinish' h1
  exact htotal.trans (Nat.mul_le_mul_right _ (by unfold costConstant; omega))

theorem program_input_cost (k : Kind) (x bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data (ThreeColorEncoding.vertexCount x) st)
    (hc : Cardinal (fieldWidth (ThreeColorEncoding.vertexCount x))
      (dimension (ThreeColorEncoding.vertexCount x)) st)
    (hs : ThreeColorBaseSeed.Seeds (ThreeColorEncoding.vertexCount x) bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    ((program k).run st).2 ≤ costConstant k*budgetConstant^18*
      (x.length+listSize qs+bs.length+1)^432 := by
  have h := program_cost k _ bits qs bs st hd hc hs hq hb
  have hh := budget_bound (ThreeColorEncoding.vertexCount x) qs bs
  have hN := ThreeColorEncoding.size_le_length x
  have hbase : ThreeColorEncoding.vertexCount x+listSize qs+bs.length+1 ≤
      x.length+listSize qs+bs.length+1 := by omega
  have hb' := hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 24))
  exact (h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb' 18))).trans_eq (by
    rw [mul_pow, ← pow_mul]
    simp only [Nat.mul_assoc])

end PCP.Lang.ThreeColorBaseOuter
