import PCP.Complexity.ThreeColorBaseDerivedLang
import PCP.Complexity.DerivedSeedOutputBound
import PCP.Complexity.ProductionEdgeCost
import PCP.Complexity.ThreeColorBaseResources

/-! Bounds for the numeric derived-grid callback sources and physical trace. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseDerived

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds
  ThreeColorBaseSetup ThreeColorBaseCardinal ThreeColorBaseResources LocalCorrection DerivedGrid

def sourceWidth (N : ℕ) (x : List Bool) (qs : List ℕ) (bs : List Bool) : ℕ :=
  metadataWidth N+2*x.length+listSize qs+2*bs.length+1

def loadConstant (k : Certificate) : ℕ := (load k).C*((load k).width+(load k).csize+1)

theorem load_cost (k : Certificate) (N : ℕ) (bits x : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hx : st.lists 100 = x.map Bool.toNat) (hq : st.lists 123 = qs)
    (hb : st.lists 102 = bs.map Bool.toNat) :
    ((load k).run st).2 ≤ loadConstant k*(sourceWidth N x qs bs+1) := by
  have hmeta : metadataWidth N ≤ sourceWidth N x qs bs := by unfold sourceWidth; omega
  apply loopFree_cost_le (load k) (by cases k <;> decide) st (sourceWidth N x qs bs)
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
    have he : L = 120 ∨ L = 122 ∨ L = 121 ∨ L = 123 ∨ L = 102 ∨ L = 100 := by
      simpa [load, Stmt.lUses, or_assoc, or_left_comm, or_comm] using hL
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (data_lists N st hd 120 (by decide) (by decide)).trans hmeta
    · exact (data_lists N st hd 122 (by decide) (by decide)).trans hmeta
    · exact (data_lists N st hd 121 (by decide) (by decide)).trans hmeta
    · rw [hq]; unfold sourceWidth; omega
    · rw [hb]
      exact (ThreeColorContext.bitList_size bs).trans (by unfold sourceWidth; omega)
    · rw [hx]
      exact (ThreeColorContext.bitList_size x).trans (by unfold sourceWidth; omega)

theorem load_bound (k : Certificate) (N : ℕ) (bits x : List Bool) (qs : List ℕ) (bs : List Bool)
    (st : State 400 128) (hd : Data N st)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (hx : st.lists 100 = x.map Bool.toNat) (hq : st.lists 123 = qs)
    (hb : st.lists 102 = bs.map Bool.toNat) :
    DerivedSeed.SourceBound (sourceWidth N x qs bs)
      (view ((load k).run st).1) := by
  have hmeta : metadataWidth N ≤ sourceWidth N x qs bs := by unfold sourceWidth; omega
  have hr (i : Fin 400) (hi : 320 ≤ i.val) (hj : i.val < 334) :
      Nat.size (st.regs i) ≤ sourceWidth N x qs bs := by
    by_cases h : i.val < 328
    · exact (data_regs N st hd i hi h).trans hmeta
    · exact (cardinal_regs N st hc i (by omega) hj).trans hmeta
  have hseed (i : Fin 400) (hi : 350 ≤ i.val) (hj : i.val < 357) :
      Nat.size (st.regs i) ≤ sourceWidth N x qs bs :=
    (seed_regs N bits st hs i hi hj).trans hmeta
  have hl (L : Fin 128) (hi : 120 ≤ L.val) (hj : L.val < 123) :
      listSize (st.lists L) ≤ sourceWidth N x qs bs := (data_lists N st hd L hi hj).trans hmeta
  have hdim (c : ℕ) (hh : c ≤ 4) : Nat.size (c*st.regs 322) ≤ sourceWidth N x qs bs := by
    rw [hd.dimension]
    have h := (metadata_basic N).2.1
    change 4*size (exponent N)+4 ≤ metadataWidth N at h
    exact (size_le_self _).trans ((Nat.mul_le_mul_right _ hh).trans (by omega))
  constructor
  · intro i
    fin_cases i
    all_goals cases k <;> dsimp [DerivedSeed.inputPort, view, State.restrict, load,
      Stmt.run, Expr.eval, Function.update, factor, index, ThreeColorBaseSeed.port]
    all_goals first
      | exact hr _ (by decide) (by decide)
      | exact hseed _ (by decide) (by decide)
      | exact hdim _ (by decide)
  · intro i hi
    have he : i = 244 ∨ i = 250 ∨ i = 251 ∨ i = 252 ∨ i = 253 ∨ i = 254 ∨
        i = 255 ∨ i = 279 ∨ i = 280 := by simpa [DerivedSeed.publicRegs] using hi
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp [view, State.restrict, load, Stmt.run, Expr.eval, Function.update]
    all_goals exact hr _ (by decide) (by decide)
  · intro L hL
    have he : L = 101 ∨ L = 102 ∨ L = 107 ∨ L = 108 ∨ L = 111 := by
      simpa [DerivedSeed.publicLists] using hL
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      dsimp [view, State.restrict, lists, load, Stmt.run, Expr.eval, Function.update]
    · exact hl 120 (by decide) (by decide)
    · exact hl 121 (by decide) (by decide)
    · rw [hq]; unfold sourceWidth; omega
    · rw [hb]; exact (ThreeColorContext.bitList_size bs).trans (by unfold sourceWidth; omega)
    · rw [hx]; exact (ThreeColorContext.bitList_size x).trans (by unfold sourceWidth; omega)

theorem queries_size {t n m : ℕ} [NeZero t] (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (H : Finset (OuterBranch.Field t)) (weight : OuterBranch.Field t)
    (s : DerivedGrid.Sample k t n m) :
    listSize (DerivedGrid.queries k nodes ζ H weight s) ≤
      44*(QueryAddress.width t n m 4+1) := by
  rw [queries_parts, listSize_append, listSize_append]
  have hp := DerivedCall.primaryQueries_size (weighted k) weight s.2.1.1 s.2.2
    (primaryLocation (m := m) k s.1)
  have ha := DerivedCall.callQueries_size k nodes ζ (firstPoint k s) s.2.1.1 (firstSeed k s)
  have hb := DerivedCall.callQueries_size k nodes ζ (secondPoint k H s) s.2.1.1 (secondSeed k s)
  omega

theorem finish_cost (k : Certificate) (v : Bool) (qs : List ℕ) (st : State 400 128)
    (hv : st.regs 275 = v.toNat) (hq : st.lists 113 = qs) :
    ((finish k).run st).2 ≤ listSize qs+5 := by
  cases v <;> simp [finish, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, hv, hq] <;> omega

end PCP.Lang.ThreeColorBaseDerived
