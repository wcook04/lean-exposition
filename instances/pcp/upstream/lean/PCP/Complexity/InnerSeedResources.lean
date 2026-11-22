/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerSeedLang

/-! # Numeric source bounds for the actual inner-seed loader -/

namespace PCP.Lang.InnerSeed

open PCP.Algebraic ThreeColorSeedIndex InterpolationBranch

variable {t n m : ℕ} [NeZero t]

structure SourceBound (W : ℕ) (st : State 140 44) : Prop where
  regs : ∀ i : Fin 140, 120 ≤ i.val → i.val < 133 → Nat.size (st.regs i) ≤ W
  lists : ∀ L : Fin 44, 40 ≤ L.val → L.val < 43 → listSize (st.lists L) ≤ W

theorem SourceBound.of_frame {W : ℕ} {st out : State 140 44}
    (hb : SourceBound W st) (hf : Frame st out) : SourceBound W out :=
  ⟨fun i hi hj => by rw [hf.regs i hi]; exact hb.regs i hi hj,
    fun L hL hU => by rw [hf.lists L hL]; exact hb.lists L hL hU⟩

def fixedConstant (p : Stmt 140 44) : ℕ := p.C * (p.width + p.csize + 1)

def budget (t m W : ℕ) : ℕ := t + m + 2 ^ t + W + 10

theorem budget_basic (t m W : ℕ) :
    10 ≤ budget t m W ∧ W + 1 ≤ budget t m W ∧ t + m + 1 ≤ budget t m W ∧
      W + t + m + 5 ≤ budget t m W ∧ 2 ^ t + W + 6 ≤ budget t m W ∧
      t + 1 ≤ budget t m W ∧ m ≤ budget t m W := by
  have h : ∀ q : ℕ, 10 ≤ t + m + q + W + 10 ∧ W + 1 ≤ t + m + q + W + 10 ∧
      t + m + 1 ≤ t + m + q + W + 10 ∧ W + t + m + 5 ≤ t + m + q + W + 10 ∧
      q + W + 6 ≤ t + m + q + W + 10 ∧ t + 1 ≤ t + m + q + W + 10 ∧
      m ≤ t + m + q + W + 10 := by intro q; omega
  exact h (2 ^ t)

theorem codes_split (s : InnerBranch.Seed t m) :
    (MixedRadixDecode.split
      ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val
      (NestedSeed.innerLayout (BinaryMaterializedField.coordinates t) m 4).radices).1 =
      List.ofFn (codes s) := by
  rw [(NestedSeed.innerLayout (BinaryMaterializedField.coordinates t) m 4).decode]
  simp only [NestedSeed.innerLayout, SeedLayout.prod, SeedLayout.leaf, codes,
    List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.cons_append, List.nil_append]

theorem code_size (s : InnerBranch.Seed t m) (i : Fin 7) :
    Nat.size (codes s i) ≤ Nat.size
      ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val := by
  apply Nat.size_le_size
  apply MixedRadixDecode.split_digit_le _
    (NestedSeed.innerLayout (BinaryMaterializedField.coordinates t) m 4).radices
  rw [codes_split]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem codes_listSize (s : InnerBranch.Seed t m) (W : ℕ)
    (hW : Nat.size ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val ≤ W) :
    listSize (List.ofFn (codes s)) ≤ 7 * (W + 1) := by
  rw [← codes_split]
  have h := MixedRadixDecode.split_listSize
    ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val
    (NestedSeed.innerLayout (BinaryMaterializedField.coordinates t) m 4).radices
  have hl :
      (NestedSeed.innerLayout (BinaryMaterializedField.coordinates t) m 4).radices.length = 7 :=
    rfl
  rw [hl] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hW 1))

def DataBound (W : ℕ) (st : State 140 44) : Prop :=
  ∀ i : Fin 7, Nat.size (st.regs (dataPort i)) ≤ W

theorem Data.bound (s : InnerBranch.Seed t m) (W : ℕ) (st : State 140 44)
    (hd : Data s st)
    (hW : Nat.size ((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s).val ≤ W) :
    DataBound W st := by
  intro i
  rw [hd i]
  exact (code_size s i).trans hW

theorem source_cost (p : Stmt 140 44) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, 120 ≤ i.val ∧ i.val < 133)
    (hl : ∀ L ∈ p.lUses, 40 ≤ L.val ∧ L.val < 43)
    (W : ℕ) (st : State 140 44) (hb : SourceBound W st) :
    (p.run st).2 ≤ fixedConstant p * (W + 1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    exact hb.regs i (hr i hi).1 (hr i hi).2
  · intro L hL
    exact hb.lists L (hl L hL).1 (hl L hL).2

/-- Data cells hold only genuine component codes, each bounded by the original code. -/
theorem fixed_cost (p : Stmt 140 44) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, (120 ≤ i.val ∧ i.val < 133) ∨ (103 ≤ i.val ∧ i.val < 110))
    (hl : ∀ L ∈ p.lUses, 40 ≤ L.val ∧ L.val < 43)
    (W : ℕ) (st : State 140 44) (hb : SourceBound W st) (hd : DataBound W st) :
    (p.run st).2 ≤ fixedConstant p * (W + 1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    rcases hr i hi with h | h
    · exact hb.regs i h.1 h.2
    · have he : dataPort ⟨i.val - 103, by omega⟩ = i := by
        apply Fin.ext
        simp only [dataPort]
        omega
      rw [← he]
      exact hd _
  · intro L hL
    exact hb.lists L (hl L hL).1 (hl L hL).2

end PCP.Lang.InnerSeed
