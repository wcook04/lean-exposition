import PCP.Complexity.OuterBranchPrimary
import PCP.Complexity.OuterBranchResources

/-! # Charged cost of the actual outer primary-row wrapper -/

-- The input loader has twenty nested sequence nodes.
set_option maxRecDepth 2048

namespace PCP.Lang.OuterBranch

open PCP.Algebraic BinaryFieldCode BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] callHadamard loadPrimary HadamardRow.branch

def loadPrimaryConstant : ℕ := loadPrimary.C * (loadPrimary.width + loadPrimary.csize + 1)

theorem loadPrimary_cost (W : ℕ) (st : State 180 80) (hb : StoredBound W st) :
    (loadPrimary.run st).2 ≤ loadPrimaryConstant * (W + 1) := by
  apply loopFree_cost_le loadPrimary (by unfold loadPrimary; decide) st W
  · intro i hi
    have h : ∀ i ∈ loadPrimary.uses, 120 ≤ i.val ∧ i.val < 139 := by
      unfold loadPrimary
      decide
    exact hb.regs i (h i hi).1 (h i hi).2
  · intro L hL
    have h : ∀ L ∈ loadPrimary.lUses, 40 ≤ L.val ∧ L.val < 62 ∧ L ≠ 49 := by
      unfold loadPrimary
      decide
    exact hb.lists L (h L hL).1 (h L hL).2.1 (h L hL).2.2

omit [NeZero t] in
theorem primaryQueries_size (k : Kind) (s : Sample k t n m) (W : ℕ)
    (hb : ∀ q ∈ primaryQueries k s, Nat.size q ≤ W) :
    listSize (primaryQueries k s) ≤ (2 * k.degree + 4) * (W + 1) := by
  have h := HadamardRow.listSize_bounded (primaryQueries k s) W hb
  simpa only [primaryQueries, List.length_map, ComputableHadamardTest.queries_eq,
    Hadamard.testQueries_length] using h

theorem primaryHadamard_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hc : Context k a ζ s qs bs st) (hs : StoredBound W st)
    (hp : ∀ i, Nat.size ((k.primary (m := m) s.1.1).payload (t := t) (fieldEquiv t) i) ≤ W)
    (hq : ∀ q ∈ primaryQueries k s, Nat.size q ≤ W) :
    (primaryHadamard.run st).2 ≤ loadPrimaryConstant * (W + 1) +
      HadamardRow.branchConstant * (2 ^ t + 3 * k.degree + W + 5) ^ 9 +
        (2 * k.degree + 4) * (W + 1) + 10 := by
  have hl := loadPrimary_cost W st hs
  have hsrc := loadPrimary_sources k a ζ s qs bs st hc
  have hpay := loadPrimary_payload k a ζ s qs bs st hc
  have hhist : (loadPrimary.run st).1.lists 30 = qs := by
    simpa [loadPrimary, Stmt.run, Function.update] using hc.history
  have hans : (loadPrimary.run st).1.lists 31 = bs.map Bool.toNat := by
    simpa [loadPrimary, Stmt.run, Function.update] using hc.answers
  have hstack : (loadPrimary.run st).1.lists 27 = [] := by
    simpa [loadPrimary, Stmt.run, Function.update] using hc.empty
  have hqs : listSize qs ≤ W := hc.history ▸ hs.lists 47 (by decide) (by decide) (by decide)
  have hbs : listSize (bs.map Bool.toNat) ≤ W :=
    hc.answers ▸ hs.lists 48 (by decide) (by decide) (by decide)
  have haddr : ∀ p ∈ ComputableHadamardTest.queries k.degree_pos (primarySeed s),
      Nat.size (HadamardRow.address ((k.primary (m := m) s.1.1).payload (t := t) (fieldEquiv t))
        (HadamardLabel.code p)) ≤ W := by
    intro p hp'
    rw [HadamardRow.Location.address_eq]
    exact hq _ (List.mem_map.mpr ⟨p, hp', rfl⟩)
  have hc' := HadamardRow.branch_cost k.degree_pos (primarySeed s) _ qs bs W
    ((loadPrimary.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
    hsrc hpay hhist hans hp (by
      change listSize ((loadPrimary.run st).1.lists 27) ≤ W
      rw [hstack]
      exact Nat.zero_le W)
    hqs hbs haddr
  have hout := HadamardRow.branch_location (fieldEquiv t) (k.primary s.1.1) k.degree_pos
    (primarySeed s) qs bs _ hsrc hpay hhist hans
  have hr := call_result (by decide) (by decide) HadamardRow.branch (loadPrimary.run st).1
  rw [← hr] at hc' hout
  rw [show call _ _ HadamardRow.branch = callHadamard from by unfold callHadamard; rfl] at hc'
  have hsize := primaryQueries_size k s W hq
  have hflag : Nat.size (ComputableHadamardTest.test k.degree_pos
      (primaryOracle (m := m) k qs bs s.1.1) (primarySeed s)).toNat ≤ 1 := by
    cases ComputableHadamardTest.test k.degree_pos
      (primaryOracle (m := m) k qs bs s.1.1) (primarySeed s) <;> decide
  simp only [primaryHadamard, run_seq_snd]
  generalize hu : (loadPrimary.run st).1 = u at *
  rw [show call _ _ HadamardRow.branch = callHadamard from by unfold callHadamard; rfl] at hout
  generalize hv : (callHadamard.run u).1 = v at *
  change v.lists 26 = primaryQueries k s ∧ v.regs 63 =
    (ComputableHadamardTest.test k.degree_pos
      (primaryOracle (m := m) k qs bs s.1.1) (primarySeed s)).toNat at hout
  simp only [run_assign_fst, run_revApp_snd, setReg_lists]
  change (loadPrimary.run st).2 + ((callHadamard.run u).2 +
    (Nat.size (v.regs 63) + Nat.size (v.regs 63) + 1 + (listSize (v.lists 26) + 1) + 1) + 1) + 1 ≤ _
  rw [hout.1, hout.2]
  omega

end PCP.Lang.OuterBranch
