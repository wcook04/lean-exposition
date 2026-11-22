import PCP.Complexity.OuterSeedLang
import PCP.Complexity.InnerSeedCost

/-! # Source and decoded-word bounds for the numeric outer sampler -/

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

structure SourceBound (W : ℕ) (st : State 180 80) : Prop where
  regs : ∀ i : Fin 180, 160 ≤ i.val → i.val < 172 → Nat.size (st.regs i) ≤ W
  lists : ∀ i : Fin 80, 64 ≤ i.val → i.val < 69 → listSize (st.lists i) ≤ W

theorem SourceBound.of_frame {W : ℕ} {st out : State 180 80}
    (hb : SourceBound W st) (hf : Frame st out) : SourceBound W out :=
  ⟨fun i hi hj => by rw [hf.regs i hi]; exact hb.regs i hi hj,
    fun i hi hj => by rw [hf.lists i hi]; exact hb.lists i hi hj⟩

def fixedConstant (p : Stmt 180 80) : ℕ := p.C * (p.width + p.csize + 1)

def budget (t d m W : ℕ) : ℕ := t+d+m+2^t+W+20

theorem budget_basic (t d m W : ℕ) :
    20 ≤ budget t d m W ∧ W+1 ≤ budget t d m W ∧ t+1 ≤ budget t d m W ∧
      d ≤ budget t d m W ∧ m ≤ budget t d m W ∧ 2^t+W+10 ≤ budget t d m W := by
  have := Nat.two_pow_pos t
  unfold budget
  omega

theorem codes_split (k : Kind) (s : Sample k t n m) :
    (MixedRadixDecode.split ((seedCodec k t n m).equiv s).val
      (NestedSeed.outerLayout (BinaryMaterializedField.coordinates t)
        (k.codec n) m 4 k.degree).radices).1 = List.ofFn (codes k s) := by
  unfold seedCodec
  rw [(NestedSeed.outerLayout (BinaryMaterializedField.coordinates t)
    (k.codec n) m 4 k.degree).decode]
  simp only [NestedSeed.outerLayout, SeedLayout.prod, SeedLayout.leaf, codes,
    List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.cons_append, List.nil_append, UniformDecode.fieldCodec_materialized,
    Kind.codec_point, innerPointCodec_materialized]
  rfl

theorem code_size (k : Kind) (s : Sample k t n m) (i : Fin 7) :
    Nat.size (codes k s i) ≤ Nat.size ((seedCodec k t n m).equiv s).val := by
  apply Nat.size_le_size
  apply MixedRadixDecode.split_digit_le _ (NestedSeed.outerLayout
    (BinaryMaterializedField.coordinates t) (k.codec n) m 4 k.degree).radices
  rw [codes_split]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem codes_listSize (k : Kind) (s : Sample k t n m) (W : ℕ)
    (hW : Nat.size ((seedCodec k t n m).equiv s).val ≤ W) :
    listSize (List.ofFn (codes k s)) ≤ 7*(W+1) := by
  rw [← codes_split]
  have h := MixedRadixDecode.split_listSize ((seedCodec k t n m).equiv s).val
    (NestedSeed.outerLayout (BinaryMaterializedField.coordinates t)
      (k.codec n) m 4 k.degree).radices
  have hl : (NestedSeed.outerLayout (BinaryMaterializedField.coordinates t)
    (k.codec n) m 4 k.degree).radices.length = 7 := rfl
  rw [hl] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hW 1))

def DataBound (W : ℕ) (st : State 180 80) : Prop :=
  ∀ i : Fin 7, Nat.size (st.regs (dataPort i)) ≤ W

theorem Data.bound (k : Kind) (s : Sample k t n m) (W : ℕ) (st : State 180 80)
    (hd : Data k s st) (hW : Nat.size ((seedCodec k t n m).equiv s).val ≤ W) : DataBound W st := by
  intro i
  rw [hd i]
  exact (code_size k s i).trans hW

theorem source_cost (p : Stmt 180 80) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, 160 ≤ i.val ∧ i.val < 172)
    (hl : ∀ i ∈ p.lUses, 64 ≤ i.val ∧ i.val < 69)
    (W : ℕ) (st : State 180 80) (hb : SourceBound W st) :
    (p.run st).2 ≤ fixedConstant p*(W+1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    exact hb.regs i (hr i hi).1 (hr i hi).2
  · intro i hi
    exact hb.lists i (hl i hi).1 (hl i hi).2

theorem fixed_cost (p : Stmt 180 80) (hp : p.loopFree = true)
    (hr : ∀ i ∈ p.uses, (160 ≤ i.val ∧ i.val < 172) ∨ (150 ≤ i.val ∧ i.val < 157))
    (hl : ∀ i ∈ p.lUses, 64 ≤ i.val ∧ i.val < 69)
    (W : ℕ) (st : State 180 80) (hb : SourceBound W st) (hd : DataBound W st) :
    (p.run st).2 ≤ fixedConstant p*(W+1) := by
  apply loopFree_cost_le p hp st W
  · intro i hi
    rcases hr i hi with h | h
    · exact hb.regs i h.1 h.2
    · have he : dataPort ⟨i.val-150, by omega⟩ = i := by
        apply Fin.ext
        simp only [dataPort]
        omega
      rw [← he]
      exact hd _
  · intro i hi
    exact hb.lists i (hl i hi).1 (hl i hi).2

end PCP.Lang.OuterSeed
