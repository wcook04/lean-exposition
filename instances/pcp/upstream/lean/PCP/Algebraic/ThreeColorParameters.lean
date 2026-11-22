/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorFields
import PCP.Algebraic.PointLineConstants
import PCP.Algebraic.BinarySeedPadding
import PCP.Algebraic.FiniteAlphabetIndex

/-!
# An actual parameter family for the three-color verifier

For `a ≥ 2`, take inner degree four, dimension and inner base `n = m = 2^a`,
and a grid alphabet of size `2^a`. The field has cardinality `2^32 * n^12`
and binary dimension `12*a+32`. The grid alphabet consists of the first `2^a`
integer codes under the supplied binary field coordinates, and comes with its
explicit index. This file also discharges the verifier's capacity and field-size
inequalities. The field, its coefficient coordinates, and the finite root
searches are computable.

Choosing `a` from the input size, bounding the resulting proof length, and
certifying efficient constructions are separate from these mathematical facts.
-/

namespace PCP.Algebraic.ThreeColorParameters

/-- Outer dimension, inner base, and grid alphabet size in this family. -/
def size (a : ℕ) : ℕ := 2 ^ a

theorem size_pos (a : ℕ) : 0 < size a := by
  exact Nat.pow_pos (by decide)

instance sizeNeZero (a : ℕ) : NeZero (size a) := ⟨(size_pos a).ne'⟩

theorem four_le_size {a : ℕ} (ha : 2 ≤ a) : 4 ≤ size a := by
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha

/-- The chosen field has room for the cubic soundness bound on outer degree. -/
def fieldIndex (a : ℕ) : ℕ := 3 * a + 7

abbrev Field (a : ℕ) := ThreeColorFields.FieldFamily (fieldIndex a)

/-- The binary coordinate dimension, written to match the field construction. -/
def binaryDimension (a : ℕ) : ℕ := 4 * (fieldIndex a + 1)

theorem binaryDimension_eq (a : ℕ) : binaryDimension a = 12 * a + 32 := by
  simp only [binaryDimension, fieldIndex]
  omega

def coordinates (a : ℕ) :
    Field a ≃ₗ[ZMod 2] (Fin (binaryDimension a) → ZMod 2) :=
  ThreeColorFields.coordinates (fieldIndex a)

/-- The field's explicit integer code, relative to the selected binary coordinates. -/
def fieldCode (a : ℕ) : Field a ≃ Fin (2 ^ binaryDimension a) :=
  (coordinates a).toEquiv.trans (BinarySeedPadding.finSeedEquiv (binaryDimension a)).symm

def cubeRoot (a : ℕ) : Field a := ThreeColorFields.cubeRoot (fieldIndex a)

theorem cubeRoot_spec (a : ℕ) : IsPrimitiveRoot (cubeRoot a) 3 :=
  ThreeColorFields.cubeRoot_spec (fieldIndex a)

def generator (a : ℕ) : Field a := ThreeColorFields.generator (fieldIndex a)

theorem generator_goodNodes (a : ℕ) : StandardLocalCorrection.GoodNodes 4 (generator a) :=
  ThreeColorFields.generator_goodNodes (fieldIndex a)

def nodes (a : ℕ) : Fin (4 + 1) ↪ Field a :=
  ThreeColorFields.nodes (fieldIndex a)

theorem generator_spec (a : ℕ) :
    IsPrimitiveRoot (generator a) (Fintype.card (Field a) - 1) :=
  ThreeColorFields.generator_spec (fieldIndex a)

theorem nodes_spec (a : ℕ) : GeneratorLowDegreeTest.IsGeneratorNodes (nodes a) :=
  ThreeColorFields.nodes_spec (fieldIndex a)

theorem card_field_pow_two (a : ℕ) : Fintype.card (Field a) = 2 ^ (12 * a + 32) := by
  rw [ThreeColorFields.card_fieldFamily]
  change (2 ^ 4) ^ (fieldIndex a + 1) = _
  rw [← pow_mul]
  congr 1
  simp only [fieldIndex]
  omega

/-- The field cardinality is a fixed constant times the twelfth power of the dimension. -/
theorem card_field (a : ℕ) : Fintype.card (Field a) = 2 ^ 32 * size a ^ 12 := by
  rw [card_field_pow_two, size, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem size_le_card (a : ℕ) : size a ≤ Fintype.card (Field a) := by
  rw [card_field]
  calc
    size a = size a ^ 1 := (pow_one _).symm
    _ ≤ size a ^ 12 := Nat.pow_le_pow_right (size_pos a) (by decide)
    _ ≤ 2 ^ 32 * size a ^ 12 := Nat.le_mul_of_pos_left _ (by decide)

/-- The field-code interval contains every requested grid-alphabet code. -/
theorem size_le_fieldCode (a : ℕ) : size a ≤ 2 ^ binaryDimension a := by
  rw [binaryDimension_eq]
  simpa only [card_field_pow_two] using size_le_card a

/-- The actual grid alphabet uses the initial segment of the field's integer codes. -/
def grid (a : ℕ) : Finset (Field a) :=
  FiniteAlphabetIndex.alphabet (fieldCode a) (size_le_fieldCode a)

@[simp] theorem card_grid (a : ℕ) : (grid a).card = size a :=
  FiniteAlphabetIndex.card_alphabet (fieldCode a) (size_le_fieldCode a)

/-- The grid's own integer index is inherited from the ambient field code. -/
def gridCode (a : ℕ) : grid a ≃ Fin (size a) :=
  FiniteAlphabetIndex.code (fieldCode a) (size_le_fieldCode a)

/-- Membership in the actual grid is the initial-code comparison. -/
@[simp] theorem mem_grid_iff (a : ℕ) (x : Field a) :
    x ∈ grid a ↔ (fieldCode a x).val < size a :=
  FiniteAlphabetIndex.mem_alphabet (fieldCode a) (size_le_fieldCode a) x

@[simp] theorem gridCode_apply_val (a : ℕ) (x : grid a) :
    (gridCode a x).val = (fieldCode a x.val).val := rfl

@[simp] theorem gridCode_symm_coe (a : ℕ) (i : Fin (size a)) :
    ((gridCode a).symm i).val =
      (fieldCode a).symm (Fin.castLE (size_le_fieldCode a) i) := rfl

theorem grid_nonempty (a : ℕ) : (grid a).Nonempty := by
  rw [← Finset.card_pos, card_grid]
  exact size_pos a

/-- Enough capacity for the honest vertex, difference, and both certificate polynomials. -/
theorem capacity {a : ℕ} (ha : 2 ≤ a) :
    5 * (((grid a).card - 1) * size a) < size a ^ 4 := by
  rw [card_grid]
  have hn := four_le_size ha
  calc
    5 * ((size a - 1) * size a) ≤ 5 * (size a * size a) := by
      exact Nat.mul_le_mul_left 5 (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    _ < (size a * size a) * (size a * size a) :=
      Nat.mul_lt_mul_of_pos_right (by nlinarith) (Nat.mul_pos (size_pos a) (size_pos a))
    _ = size a ^ 4 := by ring

/-- The full point-line field bound for decoded outer degree `4*n^4`. -/
theorem soundness_field_bound (a : ℕ) :
    PointLineConstants.fieldFactor * (4 * size a ^ 4) ^ 3 ≤ Fintype.card (Field a) := by
  rw [card_field]
  calc
    PointLineConstants.fieldFactor * (4 * size a ^ 4) ^ 3 = 64000000 * size a ^ 12 := by
      simp only [PointLineConstants.fieldFactor]
      ring
    _ ≤ 2 ^ 32 * size a ^ 12 := Nat.mul_le_mul_right _ (by decide)

/-- The second field bound controls both grid distance and local-correction losses. -/
theorem grid_field_bound (a : ℕ) :
    100 * (4 * size a ^ 4) * (grid a).card ≤ Fintype.card (Field a) := by
  rw [card_grid, card_field]
  calc
    100 * (4 * size a ^ 4) * size a = 400 * size a ^ 5 := by ring
    _ ≤ 2 ^ 32 * size a ^ 12 := Nat.mul_le_mul (by decide)
      (Nat.pow_le_pow_right (size_pos a) (by decide))

/-- The grid can hold this explicit number of vertices. -/
theorem grid_capacity (a : ℕ) : (grid a).card ^ size a = 2 ^ (a * 2 ^ a) := by
  rw [card_grid, size, ← pow_mul]

/-- Every field, root, node, nonemptiness, and numeric premise for fixed degree four. -/
theorem parameter_bounds {a : ℕ} (ha : 2 ≤ a) :
    Function.Injective (nodes a) ∧ StandardLocalCorrection.GoodNodes 4 (generator a) ∧
      IsPrimitiveRoot (cubeRoot a) 3 ∧ (grid a).Nonempty ∧
      PointLineConstants.fieldFactor * (4 * size a ^ 4) ^ 3 ≤ Fintype.card (Field a) ∧
      100 * (4 * size a ^ 4) * (grid a).card ≤ Fintype.card (Field a) ∧
      5 * (((grid a).card - 1) * size a) < size a ^ 4 :=
  ⟨(nodes a).injective, generator_goodNodes a, cubeRoot_spec a, grid_nonempty a,
    soundness_field_bound a, grid_field_bound a, capacity ha⟩

end PCP.Algebraic.ThreeColorParameters
