import PCP.Complexity.OuterBranchState

/-!
# Stored-source size bounds for the outer branch

These bounds concern the actual immutable numeric sample and history cells.
Every outer stage retains them. They provide a common cost interface for the
fixed loaders, independently of the mutable accumulated query trace.
-/

namespace PCP.Lang.OuterBranch

structure StoredBound (W : ℕ) (st : State 180 80) : Prop where
  regs : ∀ i : Fin 180, 120 ≤ i.val → i.val < 139 → Nat.size (st.regs i) ≤ W
  lists : ∀ i : Fin 80, 40 ≤ i.val → i.val < 62 → i ≠ 49 → listSize (st.lists i) ≤ W

theorem StoredBound.of_frame {W : ℕ} {st out : State 180 80}
    (hb : StoredBound W st) (hf : Frame st out) : StoredBound W out := by
  constructor
  · intro i hi hj
    rw [hf.regs i hi hj]
    exact hb.regs i hi hj
  · intro i hi hj hk
    rw [hf.lists i hi hj hk]
    exact hb.lists i hi hj hk

def loaderConstant (p : Stmt 180 80) : ℕ := p.C * (p.width + p.csize + 1)

/-- A fixed loader reads only the protected input cells. -/
theorem loader_cost (p : Stmt 180 80) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, 120 ≤ i.val ∧ i.val < 139)
    (hl : ∀ i ∈ p.lUses, 40 ≤ i.val ∧ i.val < 62 ∧ i ≠ 49)
    (W : ℕ) (st : State 180 80) (hb : StoredBound W st) :
    (p.run st).2 ≤ loaderConstant p * (W+1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    exact hb.regs i (hr i hi).1 (hr i hi).2
  · intro i hi
    exact hb.lists i (hl i hi).1 (hl i hi).2.1 (hl i hi).2.2

/-- Additional work-list reads are charged separately from immutable sources. -/
theorem loader_cost_extra (p : Stmt 180 80) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, 120 ≤ i.val ∧ i.val < 139)
    (hl : ∀ i ∈ p.lUses, (40 ≤ i.val ∧ i.val < 62 ∧ i ≠ 49) ∨ i = 1 ∨ i = 49)
    (W : ℕ) (st : State 180 80) (hb : StoredBound W st) :
    (p.run st).2 ≤ loaderConstant p *
      (W+listSize (st.lists 1)+listSize (st.lists 49)+1) := by
  apply loopFree_cost_le p hp st (W+listSize (st.lists 1)+listSize (st.lists 49))
  · intro i hi
    have := hb.regs i (hr i hi).1 (hr i hi).2
    omega
  · intro i hi
    rcases hl i hi with h | rfl | rfl
    · have := hb.lists i h.1 h.2.1 h.2.2
      omega
    · omega
    · omega

end PCP.Lang.OuterBranch
