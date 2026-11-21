import PCP.Complexity.ThreeColorBaseOuter
import PCP.Complexity.ThreeColorBaseResources

/-! # Charged cost of the four production outer callbacks and trace accumulation -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseOuter

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds
  ThreeColorBaseSetup ThreeColorBaseCardinal ThreeColorBaseResources OuterBranch

def sourceWidth (N : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  metadataWidth N+listSize qs+2*bs.length+1

def loadConstant (k : Kind) : ℕ := (load k).C*((load k).width+(load k).csize+1)

theorem load_cost (k : Kind) (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    ((load k).run st).2 ≤ loadConstant k*(sourceWidth N qs bs+1) := by
  have hmeta : metadataWidth N ≤ sourceWidth N qs bs := by unfold sourceWidth; omega
  apply loopFree_cost_le (load k) (by cases k <;> decide) st (sourceWidth N qs bs)
  · intro i hi
    have he : (320 ≤ i.val ∧ i.val < 328) ∨ (328 ≤ i.val ∧ i.val < 334) ∨
        (350 ≤ i.val ∧ i.val < 357) := by
      cases k <;> simp [load, Stmt.uses, Stmt.mustW, Expr.uses, index,
        ThreeColorBaseSeed.port] at hi <;> omega
    rcases he with h | h | h
    · exact (data_regs N st hd i h.1 h.2).trans hmeta
    · exact (cardinal_regs N st hc i h.1 h.2).trans hmeta
    · exact (seed_regs N bits st hs i h.1 h.2).trans hmeta
  · intro L hL
    have he : L = 120 ∨ L = 122 ∨ L = 121 ∨ L = 123 ∨ L = 102 := by
      simpa [load, Stmt.lUses, or_assoc, or_left_comm, or_comm] using hL
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact (data_lists N st hd 120 (by decide) (by decide)).trans hmeta
    · exact (data_lists N st hd 122 (by decide) (by decide)).trans hmeta
    · exact (data_lists N st hd 121 (by decide) (by decide)).trans hmeta
    · rw [hq]; unfold sourceWidth; omega
    · rw [hb]
      exact (ThreeColorContext.bitList_size bs).trans (by unfold sourceWidth; omega)

theorem load_bound (k : Kind) (N : ℕ) (bits : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hq : st.lists 123 = qs) (hb : st.lists 102 = bs.map Bool.toNat) :
    OuterSeed.SourceBound (sourceWidth N qs bs)
      (((load k).run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  have hmeta : metadataWidth N ≤ sourceWidth N qs bs := by unfold sourceWidth; omega
  have hr (i : Fin 400) (hi : 320 ≤ i.val) (hj : i.val < 334) :
      Nat.size (st.regs i) ≤ sourceWidth N qs bs := by
    by_cases h : i.val < 328
    · exact (data_regs N st hd i hi h).trans hmeta
    · exact (cardinal_regs N st hc i (by omega) hj).trans hmeta
  have hseed (i : Fin 400) (hi : 350 ≤ i.val) (hj : i.val < 357) :
      Nat.size (st.regs i) ≤ sourceWidth N qs bs :=
    (seed_regs N bits st hs i hi hj).trans hmeta
  have hl (L : Fin 128) (hi : 120 ≤ L.val) (hj : L.val < 123) :
      listSize (st.lists L) ≤ sourceWidth N qs bs := (data_lists N st hd L hi hj).trans hmeta
  have hdim (c : ℕ) (hh : c ≤ 4) : Nat.size (c*st.regs 322) ≤ sourceWidth N qs bs := by
    rw [hd.dimension]
    have h := (metadata_basic N).2.1
    change 4*size (exponent N)+4 ≤ metadataWidth N at h
    exact (size_le_self _).trans ((Nat.mul_le_mul_right _ hh).trans (by omega))
  constructor
  · intro i hi hj
    have he : i = 160 ∨ i = 161 ∨ i = 162 ∨ i = 163 ∨ i = 164 ∨ i = 165 ∨
        i = 166 ∨ i = 167 ∨ i = 168 ∨ i = 169 ∨ i = 170 ∨ i = 171 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases k <;> dsimp [State.restrict, load, Stmt.run, Expr.eval, Function.update,
      factor, index, ThreeColorBaseSeed.port]
    all_goals
      first
      | exact hr _ (by decide) (by decide)
      | exact hseed _ (by decide) (by decide)
      | exact hdim _ (by decide)
  · intro L hi hj
    have he : L = 64 ∨ L = 65 ∨ L = 66 ∨ L = 67 ∨ L = 68 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp only [State.restrict_lists] <;>
      dsimp [load, Stmt.run, Expr.eval, Function.update]
    · exact hl 120 (by decide) (by decide)
    · exact hl 122 (by decide) (by decide)
    · exact hl 121 (by decide) (by decide)
    · rw [hq]; unfold sourceWidth; omega
    · rw [hb]; exact (ThreeColorContext.bitList_size bs).trans (by unfold sourceWidth; omega)

theorem queryCodes_size {t n m : ℕ} [NeZero t] (k : Kind)
    (a : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (s : OuterBranch.Sample k t n m) :
    listSize (OuterBranch.queryCodes k a ζ s) ≤ 26*(QueryAddress.width t n m 4+1) := by
  have hlen : (k.queries (BinaryMaterializedField.coordinates t) a ζ s).length ≤ 26 := by
    simp only [Kind.queries, List.length_map, ComputableEncodedLineLowDegreeTest.queries_eq]
    have hh := EncodedLineLowDegreeTest.queries_length_le k.degree_pos
      (BinaryMaterializedField.coordinates t) a ζ s
    have hd := k.degree_le
    omega
  have hsize (xs : List (ThreeColorVerifier.Query (OuterBranch.Field t) n m 4 t)) :
      listSize (xs.map (fun q => (ThreeColorQueryIndex.equiv (BinaryFieldCode.fieldEquiv t)
        (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) q).val)) ≤
      xs.length*(QueryAddress.width t n m 4+1) := by
    induction xs with
    | nil => simp [listSize]
    | cons q xs ih =>
      have hh := QueryAddress.address_size (BinaryFieldCode.fieldEquiv t) q
      change Nat.size _ ≤ QueryAddress.width t n m 4 at hh
      simp only [List.map_cons, List.length_cons, listSize, List.sum_cons] at ih ⊢
      nlinarith only [hh,ih]
  exact (hsize _).trans (Nat.mul_le_mul_right _ hlen)

theorem finish_cost (k : Kind) (v : Bool) (qs : List ℕ) (st : State 400 128)
    (hv : st.regs 144 = v.toNat) (hq : st.lists 49 = qs.reverse) :
    ((finish k).run st).2 ≤ 2*listSize qs+7 := by
  cases v <;> simp [finish, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    hv, hq, listSize_reverse] <;> omega

def budget (N : ℕ) (qs : List ℕ) (bs : List Bool) : ℕ :=
  fieldWidth N+2*dimension N+2^fieldWidth N+sourceWidth N qs bs+
    listSize qs+2*bs.length+30

def costConstant (k : Kind) : ℕ :=
  loadConstant k+NumericOuter.costConstant k+936*QueryAddress.widthConstant+100

def budgetConstant : ℕ := 100000000*(coreConstant+1)^2+4*coreConstant+40

theorem budget_bound (N : ℕ) (qs : List ℕ) (bs : List Bool) :
    budget N qs bs ≤ budgetConstant*(N+listSize qs+bs.length+1)^24 := by
  obtain ⟨hcore,ht,hn,hq⟩ := core_bounds N
  let A := N+listSize qs+bs.length+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hlin : A ≤ A^12 := Nat.le_pow (by decide)
  have h12 : A^12 ≤ A^24 := Nat.pow_le_pow_right hA (by decide)
  have h1 : 1 ≤ A^24 := Nat.one_le_pow _ _ hA
  have hN : N+1 ≤ A^12 := (by dsimp [A]; omega : N+1 ≤ A).trans hlin
  have hB : coreBound N ≤ coreConstant*A^12 := by
    unfold coreBound
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [A]; omega) 12)
  have hsum : coreBound N+N+1 ≤ (coreConstant+1)*A^12 := by nlinarith only [hB,hN]
  have hmeta := Nat.mul_le_mul_left 100000000 (Nat.pow_le_pow_left hsum 2)
  have hB' := hB.trans (Nat.mul_le_mul_left _ h12)
  have hl : listSize qs+2*bs.length+1 ≤ 2*A^24 := by
    have hh : A ≤ A^24 := Nat.le_pow (by decide)
    dsimp [A] at hh
    omega
  change metadataWidth N ≤ _ at hmeta
  rw [mul_pow, ← pow_mul] at hmeta
  change metadataWidth N ≤ 100000000*((coreConstant+1)^2*A^24) at hmeta
  unfold budget sourceWidth budgetConstant
  change _ ≤ (100000000*(coreConstant+1)^2+4*coreConstant+40)*A^24
  nlinarith only [hmeta,hB',ht,hn,hq,hl,h1]

end PCP.Lang.ThreeColorBaseOuter
