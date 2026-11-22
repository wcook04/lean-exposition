/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.CorrectionSeedMaterialization
import PCP.Complexity.StandardCorrectionPointLang

/-! # Actual numeric source and component bounds for correction-seed loading -/

namespace PCP.Lang.CorrectionSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode

variable {t m : ℕ} [NeZero t] {σ : Type*}

def inputPort : Fin 5 → Fin 220 := ![200, 201, 202, 203, 208]
def dataPort (i : Fin 4) : Fin 220 := ⟨204 + i.val, by omega⟩

def SourceBound (W : ℕ) (st : State 220 96) : Prop :=
  ∀ i : Fin 5, Nat.size (st.regs (inputPort i)) ≤ W

def DataBound (W : ℕ) (st : State 220 96) : Prop :=
  ∀ i : Fin 4, Nat.size (st.regs (dataPort i)) ≤ W

def components (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) : Fin 4 → ℕ :=
  ![((innerCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.2).val,
    ((innerPointCodec (BinaryMaterializedField.coordinates t) m 4).equiv s.2.2.1).val,
    (fieldEquiv t s.2.1).val,
    ((σc.function (fieldCodec (BinaryMaterializedField.coordinates t))).equiv s.1).val]

theorem components_split (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) :
    (MixedRadixDecode.split
      ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val
      ((NestedSeed.callLayout (BinaryMaterializedField.coordinates t) σc m 4).radices ++
        List.replicate 3 1)).1 = List.ofFn (components σc s) ++ [0, 0, 0] := by
  rw [(NestedSeed.callLayout (BinaryMaterializedField.coordinates t) σc m 4).decode_padded s 3]
  simp only [NestedSeed.callLayout, SeedLayout.prod, SeedLayout.leaf, components,
    List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.cons_append, List.nil_append, UniformDecode.fieldCodec_materialized]
  rfl

theorem component_size (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (i : Fin 4) :
    Nat.size (components σc s i) ≤ Nat.size
      ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val := by
  apply Nat.size_le_size
  apply MixedRadixDecode.split_digit_le _
    ((NestedSeed.callLayout (BinaryMaterializedField.coordinates t) σc m 4).radices ++
      List.replicate 3 1)
  rw [components_split]
  exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem Data.components {σc : Codec σ}
    {s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t} {st : State 220 96}
    (hd : Data σc s st) : ∀ i : Fin 4, st.regs (dataPort i) = components σc s i := by
  intro i
  fin_cases i
  · exact hd.inner
  · exact hd.direction
  · exact hd.param
  · exact hd.outer

theorem Data.bound {σc : Codec σ}
    {s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t} {st : State 220 96}
    (hd : Data σc s st) (W : ℕ)
    (hc : Nat.size ((callCodec (BinaryMaterializedField.coordinates t) σc m 4).equiv s).val ≤ W) :
    DataBound W st := by
  intro i
  rw [hd.components i]
  exact (component_size σc s i).trans hc

/-- The source bound itself is computed from dimensions and the actual input-code bit size. -/
theorem Input.sourceBound {σc : Codec σ}
    {s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t} {st : State 220 96}
    (hc : Input σc s st) :
    SourceBound (t + m + σc.size + Nat.size (st.regs 203) + 3) st := by
  intro i
  fin_cases i
  · change Nat.size (st.regs 200) ≤ _
    rw [hc.width]
    exact (size_le_self t).trans (by omega)
  · change Nat.size (st.regs 201) ≤ _
    rw [hc.base]
    exact (size_le_self m).trans (by omega)
  · change Nat.size (st.regs 202) ≤ _
    rw [hc.dimension]
    exact (size_le_self σc.size).trans (by omega)
  · change Nat.size (st.regs 203) ≤ _
    omega
  · change Nat.size (st.regs 208) ≤ _
    rw [hc.card, Nat.size_pow]
    omega

theorem SourceBound.split {W : ℕ} {st : State 220 96} (hb : SourceBound W st) :
    SourceBound W (splitSeed.run st).1 := by
  intro i
  have h := splitSeed_reg st (inputPort i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
  rw [h]
  exact hb i

theorem SourceBound.vector {W : ℕ} {st : State 220 96} (hb : SourceBound W st)
    (src len : Fin 220) (dst : Fin 96) : SourceBound W ((vector src len dst).run st).1 := by
  intro i
  rw [vector_reg src len (inputPort i) dst (by fin_cases i <;> decide)]
  exact hb i

theorem SourceBound.dimension {W : ℕ} {st : State 220 96} (hb : SourceBound W st) :
    SourceBound W (dimension.run st).1 := by
  intro i
  rw [run_regs_frame CorrectionSeed.dimension (inputPort i) (by fin_cases i <;> decide)]
  exact hb i

attribute [local irreducible] splitSeed vector

theorem SourceBound.program {W : ℕ} {st : State 220 96} (hb : SourceBound W st) :
    SourceBound W (program.run st).1 := by
  simp only [CorrectionSeed.program, run_seq_fst]
  exact ((hb.split.dimension).vector 207 202 81).vector 205 211 82

/-- Materialized coordinate storage is linear in the actual number of field coordinates. -/
theorem program_lists_size (σc : Codec σ)
    (s : RawCallSeed (BinaryMaterializedField.Element t) σ m 4 t) (st : State 220 96)
    (hc : Input σc s st) :
    listSize ((program.run st).1.lists 81) ≤ σc.size * (t + 1) ∧
      listSize ((program.run st).1.lists 82) ≤ (4 * m) * (t + 1) := by
  have h := program_run σc s st hc
  rw [h.2.2.1, h.2.2.2]
  exact ⟨StandardCorrection.fieldCodes_size _, StandardCorrection.fieldCodes_size _⟩

end PCP.Lang.CorrectionSeed
