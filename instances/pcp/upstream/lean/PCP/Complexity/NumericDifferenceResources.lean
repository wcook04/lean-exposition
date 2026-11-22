import PCP.Complexity.NumericDifferenceLang
import PCP.Complexity.InnerSeedCost

/-! # Source and decoded-word bounds for the numeric difference sampler -/

namespace PCP.Lang.NumericDifference

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode

variable {t n m : ℕ} [NeZero t]

structure SourceBound (W : ℕ) (st : State 120 40) : Prop where
  regs : ∀ i : Fin 120, 100 ≤ i.val → i.val < 109 → Nat.size (st.regs i) ≤ W
  lists : ∀ i : Fin 40, 32 ≤ i.val → i.val < 35 → listSize (st.lists i) ≤ W

theorem SourceBound.of_frame {W : ℕ} {st out : State 120 40}
    (hb : SourceBound W st) (hf : Frame st out) : SourceBound W out :=
  ⟨fun i hi hj => by rw [hf.regs i hi]; exact hb.regs i hi hj,
    fun i hi hj => by rw [hf.lists i hi]; exact hb.lists i hi hj⟩

def fixedConstant (p : Stmt 120 40) : ℕ := p.C * (p.width + p.csize + 1)

def budget (t d m W : ℕ) : ℕ := t+d+m+2^t+W+20

theorem budget_basic (t d m W : ℕ) :
    20 ≤ budget t d m W ∧ W+1 ≤ budget t d m W ∧ t+1 ≤ budget t d m W ∧
      d ≤ budget t d m W ∧ m ≤ budget t d m W ∧ 2^t+W+10 ≤ budget t d m W := by
  have := Nat.two_pow_pos t
  unfold budget
  omega

theorem codes_split (s : Sample t n) :
    (MixedRadixDecode.split ((seedCodec t n).equiv s).val
      (NestedSeed.differenceLayout (BinaryMaterializedField.coordinates t) n).radices).1 =
      List.ofFn (codes s) := by
  unfold seedCodec
  rw [(NestedSeed.differenceLayout (BinaryMaterializedField.coordinates t) n).decode]
  simp only [NestedSeed.differenceLayout, SeedLayout.prod, SeedLayout.leaf, codes,
    List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.cons_append, List.nil_append, point_code]

theorem code_size (s : Sample t n) (i : Fin 3) :
    Nat.size (codes s i) ≤ Nat.size ((seedCodec t n).equiv s).val := by
  apply Nat.size_le_size
  apply MixedRadixDecode.split_digit_le _
    (NestedSeed.differenceLayout (BinaryMaterializedField.coordinates t) n).radices
  rw [codes_split]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem codes_listSize (s : Sample t n) (W : ℕ)
    (hW : Nat.size ((seedCodec t n).equiv s).val ≤ W) :
    listSize (List.ofFn (codes s)) ≤ 3*(W+1) := by
  rw [← codes_split]
  have h := MixedRadixDecode.split_listSize ((seedCodec t n).equiv s).val
    (NestedSeed.differenceLayout (BinaryMaterializedField.coordinates t) n).radices
  have hl : (NestedSeed.differenceLayout (BinaryMaterializedField.coordinates t) n).radices.length
      = 3 := rfl
  rw [hl] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hW 1))

def DataBound (W : ℕ) (st : State 120 40) : Prop :=
  ∀ i : Fin 3, Nat.size (st.regs (dataPort i)) ≤ W

theorem Data.bound (s : Sample t n) (W : ℕ) (st : State 120 40)
    (hd : Data s st) (hW : Nat.size ((seedCodec t n).equiv s).val ≤ W) : DataBound W st := by
  intro i
  rw [hd i]
  exact (code_size s i).trans hW

theorem source_cost (p : Stmt 120 40) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, 100 ≤ i.val ∧ i.val < 109)
    (hl : ∀ i ∈ p.lUses, 32 ≤ i.val ∧ i.val < 35)
    (W : ℕ) (st : State 120 40) (hb : SourceBound W st) :
    (p.run st).2 ≤ fixedConstant p*(W+1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    exact hb.regs i (hr i hi).1 (hr i hi).2
  · intro i hi
    exact hb.lists i (hl i hi).1 (hl i hi).2

theorem fixed_cost (p : Stmt 120 40) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, (100 ≤ i.val ∧ i.val < 109) ∨ (90 ≤ i.val ∧ i.val < 93))
    (hl : ∀ i ∈ p.lUses, 32 ≤ i.val ∧ i.val < 35)
    (W : ℕ) (st : State 120 40) (hb : SourceBound W st) (hd : DataBound W st) :
    (p.run st).2 ≤ fixedConstant p*(W+1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    rcases hr i hi with h | h
    · exact hb.regs i h.1 h.2
    · have he : dataPort ⟨i.val-90, by omega⟩ = i := by
        apply Fin.ext
        simp only [dataPort]
        omega
      rw [← he]
      exact hd _
  · intro i hi
    exact hb.lists i (hl i hi).1 (hl i hi).2

end PCP.Lang.NumericDifference
