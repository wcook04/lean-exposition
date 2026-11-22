/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryMaterializedField
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Log
import PCP.Algebraic.BinarySeedPadding
import PCP.Algebraic.FiniteRootSearch
import PCP.Algebraic.FiniteGeneratorSearch
import PCP.Algebraic.StandardLocalCorrection

/-!
# Field parameters for inner degree four

The fields `GF(2^(4*(k+1)))` have binary coordinates, a primitive cube root of
unity, a generator of the full multiplicative group, and the five distinct
interpolation nodes given by its first five nonzero powers. A ceiling logarithm
chooses a member above any requested threshold with only a constant-factor
increase in cardinality.

The field elements store arrays of binary coefficients modulo the computed monic
irreducible polynomial. Arithmetic materializes its results, inversion uses binary
powering, and coordinates read the stored cells directly.
Roots are found by bounded search in the induced numeric order. These are
computable constructions. This file proves their field and parameter properties;
the production verifier's concrete use of these constructions is covered by
`PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.ThreeColorFields

/-- The common field family for the degree-four tester and the three colors. -/
abbrev FieldFamily (k : ℕ) := BinaryMaterializedField.Element (4 * (k + 1))

/-- Every extension exponent is positive, including the first member. -/
theorem extensionDegree_pos (k : ℕ) : 0 < 4 * (k + 1) := by omega

instance extensionDegreeNeZero (k : ℕ) : NeZero (4 * (k + 1)) :=
  ⟨(extensionDegree_pos k).ne'⟩

instance fieldFamilyFintype (k : ℕ) : Fintype (FieldFamily k) :=
  inferInstanceAs (Fintype (BinaryMaterializedField.Element (4 * (k + 1))))

/-- The precise field cardinality, starting at sixteen. -/
@[simp] theorem card_fieldFamily (k : ℕ) : Fintype.card (FieldFamily k) = 16 ^ (k + 1) := by
  rw [BinaryMaterializedField.card_element, pow_mul]
  norm_num

/-- The binary dimension follows from the explicit coefficient equivalence. -/
theorem finrank_fieldFamily (k : ℕ) :
    Module.finrank (ZMod 2) (FieldFamily k) = 4 * (k + 1) := by
  rw [(BinaryMaterializedField.coordinates (4 * (k + 1))).finrank_eq]
  simp

/-- The verifier's binary linear coordinates read the stored array coefficients. -/
def coordinates (k : ℕ) :
    FieldFamily k ≃ₗ[ZMod 2] (Fin (4 * (k + 1)) → ZMod 2) :=
  BinaryMaterializedField.coordinates (4 * (k + 1))

/-- Numeric field codes in the order determined by the supplied binary coordinates. -/
def fieldCode (k : ℕ) : FieldFamily k ≃ Fin (2 ^ (4 * (k + 1))) :=
  (coordinates k).toEquiv.trans (BinarySeedPadding.finSeedEquiv _).symm

theorem sixteen_le_card (k : ℕ) : 16 ≤ Fintype.card (FieldFamily k) := by
  rw [card_fieldFamily]
  simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 16) (by omega : 1 ≤ k + 1)

/-- Both required root orders divide the multiplicative group order. -/
theorem fifteen_dvd_card_sub_one (k : ℕ) : 15 ∣ Fintype.card (FieldFamily k) - 1 := by
  rw [card_fieldFamily]
  exact Nat.sub_one_dvd_pow_sub_one 16 (k + 1)

theorem exists_primitive_cube_root (k : ℕ) : ∃ ω : FieldFamily k, IsPrimitiveRoot ω 3 := by
  classical
  have hd : 3 ∣ Fintype.card (FieldFamily k)ˣ := by
    rw [Fintype.card_units]
    exact (by decide : 3 ∣ 15).trans (fifteen_dvd_card_sub_one k)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (FieldFamily k)ˣ) 3 hd
  exact ⟨u, IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)⟩

/-- Search the coordinate-induced field order for the first nontrivial cube root. -/
def cubeRoot (k : ℕ) : FieldFamily k := by
  letI : DecidableEq (FieldFamily k) := (fieldCode k).decidableEq
  exact FiniteRootSearch.root (fieldCode k) 3

theorem cubeRoot_spec (k : ℕ) : IsPrimitiveRoot (cubeRoot k) 3 := by
  let : DecidableEq (FieldFamily k) := (fieldCode k).decidableEq
  exact FiniteRootSearch.root_spec (fieldCode k) (by decide) (exists_primitive_cube_root k)

/-- Least numeric code of a full multiplicative generator. -/
def generator (k : ℕ) : FieldFamily k := by
  letI : DecidableEq (FieldFamily k) := (fieldCode k).decidableEq
  exact FiniteGeneratorSearch.root (fieldCode k) (Fintype.card (FieldFamily k) - 1)

theorem generator_spec (k : ℕ) :
    IsPrimitiveRoot (generator k) (Fintype.card (FieldFamily k) - 1) := by
  let : DecidableEq (FieldFamily k) := (fieldCode k).decidableEq
  exact FiniteGeneratorSearch.root_spec (fieldCode k)
    (by have := sixteen_le_card k; omega) GeneratorLowDegreeTest.exists_generator

theorem generator_goodNodes (k : ℕ) : StandardLocalCorrection.GoodNodes 4 (generator k) :=
  StandardLocalCorrection.goodNodes_of_generator
    (by have := sixteen_le_card k; omega) (generator_spec k)

/-- Exactly the five consecutive noncentral generator powers in the paper. -/
def nodes (k : ℕ) : Fin 5 ↪ FieldFamily k where
  toFun := GeneratorLowDegreeTest.nodes 4 (generator k)
  inj' := (generator_goodNodes k).1

theorem nodes_spec (k : ℕ) : GeneratorLowDegreeTest.IsGeneratorNodes (nodes k) :=
  ⟨generator k, generator_spec k, rfl⟩

/-- Choose the least positive power of sixteen reaching the requested threshold. -/
def index (M : ℕ) : ℕ := max 1 (Nat.clog 16 M) - 1

theorem index_add_one (M : ℕ) : index M + 1 = max 1 (Nat.clog 16 M) := by
  unfold index
  omega

/-- The selected field, with all the same roots and coordinate constructions. -/
abbrev Chosen (M : ℕ) := FieldFamily (index M)

@[simp] theorem card_chosen (M : ℕ) :
    Fintype.card (Chosen M) = 16 ^ max 1 (Nat.clog 16 M) := by
  rw [card_fieldFamily, index_add_one]

/-- The selected cardinality meets the requested threshold, also at zero. -/
theorem le_card_chosen (M : ℕ) : M ≤ Fintype.card (Chosen M) := by
  rw [card_chosen]
  exact (Nat.le_pow_clog (by decide) M).trans
    (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

/-- Ceiling-logarithm selection increases cardinality by at most a factor sixteen. -/
theorem card_chosen_le (M : ℕ) : Fintype.card (Chosen M) ≤ 16 * max 1 M := by
  rw [card_chosen]
  by_cases hM : M ≤ 1
  · have hc : Nat.clog 16 M = 0 := Nat.clog_of_right_le_one hM 16
    simp only [hc, max_eq_left (by omega : 0 ≤ 1), pow_one,
      max_eq_left hM, mul_one, le_refl]
  · have hM' : 1 < M := by omega
    have hc := Nat.clog_pos (by decide : 1 < 16) hM'
    rw [max_eq_right hc, max_eq_right (by omega : 1 ≤ M)]
    have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 16) hM'
    have he : Nat.clog 16 M = (Nat.clog 16 M).pred + 1 :=
      (Nat.succ_pred_eq_of_pos hc).symm
    calc
      16 ^ Nat.clog 16 M = 16 ^ (Nat.clog 16 M).pred * 16 := by
        conv_lhs => rw [he]
        rw [pow_succ]
      _ ≤ M * 16 := Nat.mul_le_mul_right 16 (Nat.le_of_lt hpred)
      _ = 16 * M := Nat.mul_comm _ _

/-- A slightly looser size form that retains the first field's size explicitly. -/
theorem card_chosen_le_sixteen_max (M : ℕ) :
    Fintype.card (Chosen M) ≤ 16 * max 16 M :=
  (card_chosen_le M).trans (Nat.mul_le_mul_left 16 (max_le_max_right M (by decide)))

/-- The selected binary coordinate count. -/
def binaryDimension (M : ℕ) : ℕ := 4 * (index M + 1)

theorem binaryDimension_eq (M : ℕ) :
    binaryDimension M = 4 * max 1 (Nat.clog 16 M) := by
  rw [binaryDimension, index_add_one]

def chosenCoordinates (M : ℕ) :
    Chosen M ≃ₗ[ZMod 2] (Fin (binaryDimension M) → ZMod 2) := coordinates (index M)

/-- All mathematical field parameters for the fixed inner degree four are supplied together. -/
theorem chosen_parameters (M : ℕ) :
    M ≤ Fintype.card (Chosen M) ∧ Fintype.card (Chosen M) ≤ 16 * max 1 M ∧
      Function.Injective (nodes (index M)) ∧
      StandardLocalCorrection.GoodNodes 4 (generator (index M)) ∧
      IsPrimitiveRoot (cubeRoot (index M)) 3 :=
  ⟨le_card_chosen M, card_chosen_le M, (nodes (index M)).injective,
    generator_goodNodes (index M), cubeRoot_spec (index M)⟩

end PCP.Algebraic.ThreeColorFields
