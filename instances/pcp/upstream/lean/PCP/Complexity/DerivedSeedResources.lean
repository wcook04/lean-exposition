/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedMaterialize
import PCP.Complexity.DerivedSeedContext
import PCP.Complexity.CorrectionSeedResources

/-! # Actual source and decoded-component sizes for raw derived seeds -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid
variable {t n m : ℕ} [NeZero t]

def inputPort : Fin 5 → Fin 300 := ![240,241,256,257,243]
def dataPort : Fin 5 → Fin 300 := ![277,249,248,258,259]

def InputBound (W : ℕ) (st : State 300 112) : Prop :=
  ∀ i : Fin 5, Nat.size (st.regs (inputPort i)) ≤ W

def DataBound (W : ℕ) (st : State 300 112) : Prop :=
  ∀ i : Fin 5, Nat.size (st.regs (dataPort i)) ≤ W

structure SourceBound (W : ℕ) (st : State 300 112) : Prop where
  input : InputBound W st
  regs : ∀ i ∈ publicRegs, Nat.size (st.regs i) ≤ W
  lists : ∀ L ∈ publicLists, listSize (st.lists L) ≤ W

def components (k : Certificate) (s : DerivedGrid.RawSample k t n m) : Fin 5 → ℕ :=
  ![((coefficientCodec t 3).equiv s.2.2).val,
    ((callCodec (BinaryMaterializedField.coordinates t)
      ((Codec.fin (baseDimension k n)).sum (Codec.fin (baseDimension k n))) m 4).equiv
        s.2.1.2.2).val,
    ((callCodec (BinaryMaterializedField.coordinates t)
      ((Codec.fin (baseDimension k n)).sum (Codec.fin (baseDimension k n))) m 4).equiv
        s.2.1.2.1).val,
    ((bitsCodec t).equiv s.2.1.1).val,
    (((Codec.fin (baseDimension k n)).function
      (fieldCodec (BinaryMaterializedField.coordinates t))).equiv s.1).val]

theorem components_split (k : Certificate) (s : DerivedGrid.RawSample k t n m) :
    (MixedRadixDecode.split
      ((derivedCodec (BinaryMaterializedField.coordinates t) (baseDimension k n) m 4 3).equiv
        s).val
      ((NestedSeed.derivedLayout (BinaryMaterializedField.coordinates t)
        (baseDimension k n) m 4).radices ++ List.replicate 2 1)).1 =
      List.ofFn (components k s) ++ [0,0] := by
  rw [(NestedSeed.derivedLayout (BinaryMaterializedField.coordinates t)
    (baseDimension k n) m 4).decode_padded s 2]
  simp only [NestedSeed.derivedLayout, SeedLayout.prod, SeedLayout.leaf, components,
    List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.cons_append, List.nil_append]
  rfl

theorem component_size (k : Certificate) (s : DerivedGrid.RawSample k t n m) (i : Fin 5) :
    Nat.size (components k s i) ≤ Nat.size
      ((derivedCodec (BinaryMaterializedField.coordinates t) (baseDimension k n) m 4 3).equiv
        s).val := by
  apply Nat.size_le_size
  apply MixedRadixDecode.split_digit_le _
    ((NestedSeed.derivedLayout (BinaryMaterializedField.coordinates t)
      (baseDimension k n) m 4).radices ++ List.replicate 2 1)
  rw [components_split]
  exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i,rfl⟩))

theorem Data.components {k : Certificate} {s : DerivedGrid.RawSample k t n m}
    {st : State 300 112} (hd : Data k s st) :
    ∀ i : Fin 5, st.regs (dataPort i) = components k s i := by
  intro i
  fin_cases i
  · exact hd.mask
  · exact hd.second
  · exact hd.first
  · exact hd.label
  · exact hd.point

theorem Data.bound {k : Certificate} {s : DerivedGrid.RawSample k t n m}
    {st : State 300 112} (hd : Data k s st) (W : ℕ)
    (hW : Nat.size
      ((derivedCodec (BinaryMaterializedField.coordinates t) (baseDimension k n) m 4 3).equiv
        s).val ≤ W) : DataBound W st := by
  intro i
  rw [hd.components i]
  exact (component_size k s i).trans hW

theorem InputBound.split {W : ℕ} {st : State 300 112} (h : InputBound W st) :
    InputBound W (split.run st).1 := by
  intro i
  rw [split_reg st (inputPort i) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
  exact h i

theorem InputBound.of_regs {W : ℕ} {st out : State 300 112} (h : InputBound W st)
    (hr : ∀ i : Fin 300, 220 ≤ i.val → out.regs i = st.regs i) : InputBound W out := by
  intro i
  rw [hr (inputPort i) (by fin_cases i <;> decide)]
  exact h i

def fixedConstant (p : Stmt 300 112) : ℕ := p.C*(p.width+p.csize+1)

end PCP.Lang.DerivedSeed
