/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorVerifier

/-!
# Exact size of the three-color verifier's finite sampler

The original sampler has four nonzero-field draws; every other random choice
has a power-of-two cardinality when the field has `2^t` elements. All exponents
below count the actual product sampler, including the unused seed of each fair
choice inside the binary low-degree test.
-/

namespace PCP.Algebraic.ThreeColorSeedSize

open Finset BinaryPolynomialSpace

/-- Number of bits in one degree-`r` coefficient mask. -/
def coefficientBits (t r : ℕ) : ℕ := ∑ k ∈ range (r + 1), t.choose k

/-- Exact randomness of all the Hadamard checks, including their factor masks. -/
def hadamardBits (t r : ℕ) : ℕ :=
  2 * coefficientBits t r + coefficientBits t 1 +
    ∑ k : Fin (r - 1), coefficientBits t (k.val + 1)

/-- Exact cardinality of one coefficient mask. -/
theorem card_coefficients (t r : ℕ) : Fintype.card (Coefficients t r) =
    2 ^ coefficientBits t r := BinaryPolynomialSpace.card_coefficients t r

/-- Exact cardinality of HadTest's actual finite seed. -/
theorem card_hadamard (t r : ℕ) : Fintype.card (Hadamard.TestRandomness t r) =
    2 ^ hadamardBits t r := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    card_coefficients, card_coefficients, Fintype.card_pi]
  simp_rw [card_coefficients]
  rw [prod_pow_eq_pow_sum]
  simp only [← pow_add]
  congr 1
  unfold hadamardBits
  omega

@[simp] theorem coefficientBits_one (t : ℕ) : coefficientBits t 1 = 1 + t := by
  simp [coefficientBits, sum_range_succ]

@[simp] theorem coefficientBits_two (t : ℕ) :
    coefficientBits t 2 = 1 + t + t.choose 2 := by
  simp [coefficientBits, sum_range_succ]

@[simp] theorem coefficientBits_three (t : ℕ) :
    coefficientBits t 3 = 1 + t + t.choose 2 + t.choose 3 := by
  simp [coefficientBits, sum_range_succ]

@[simp] theorem hadamardBits_one (t : ℕ) : hadamardBits t 1 = 3 * (1 + t) := by
  simp [hadamardBits]
  omega

@[simp] theorem hadamardBits_three (t : ℕ) :
    hadamardBits t 3 = 5 + 5 * t + 3 * t.choose 2 + 2 * t.choose 3 := by
  simp [hadamardBits, Fin.sum_univ_succ]
  omega

/-- All randomness in the inner binary low-degree tester. -/
def innerBits (m c t : ℕ) : ℕ := 1 + 3 * t * (c * m) + 2 * t + hadamardBits t 1

/-- All randomness in one encoded-line low-degree branch on `d` field coordinates. -/
def outerBits (d m c t r : ℕ) : ℕ :=
  2 * t * d + 2 * t + t * (c * m) + hadamardBits t r + innerBits m c t

/-- The power-of-two part of one derived-grid branch on `d` field coordinates. -/
def derivedBits (d m c t r : ℕ) : ℕ :=
  5 * t * d + t + 2 * t * (c * m) + 2 * innerBits m c t + coefficientBits t r

/-- Explicit exponent remaining after factoring out the four nonzero-field draws. -/
def originalBits (n m c t : ℕ) : ℕ :=
  35 * t * n + 32 * t * c * m + 69 * t + 50 + 8 * t.choose 2 + 6 * t.choose 3

/-- Replacing all four nonzero draws by full-field draws adds exactly `4t` bits. -/
def rawBits (n m c t : ℕ) : ℕ := originalBits n m c t + 4 * t

section Finite

variable {F σ : Type*} [Fintype F] [Fintype σ] [DecidableEq σ] {m c t r : ℕ}

local instance : Fintype (BinaryLocalCorrection.InnerPoint F m c) := inferInstance
local instance : Fintype (BinaryLocalCorrection.InnerSeed F m c t) := inferInstance
local instance : Fintype
    (Hadamard.TestRandomness t r × BinaryLocalCorrection.InnerSeed F m c t) := inferInstance
local instance : Fintype (EncodedLineLowDegreeTest.Sample F σ m c t r) := inferInstance

/-- Count the actual binary low-degree product seed, including its choice bit. -/
theorem card_binaryLowDegree (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (BinaryLowDegreeTest.TestRandomness F σ t r) =
      2 ^ (1 + 3 * t * Fintype.card σ + 2 * t + hadamardBits t r) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, card_hadamard]
  simp only [BinaryLowDegreeTest.InterpolationRandomness, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fun, Fintype.card_fin, ZMod.card, hF]
  rw [show (2 : ℕ) = 2 ^ 1 by rfl]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

/-- The inner tester specializes to `c*m` field coordinates. -/
theorem card_inner (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (BinaryLocalCorrection.InnerSeed F m c t) = 2 ^ innerBits m c t := by
  simpa only [innerBits, SetMultilinear.Variables, Fintype.card_prod, Fintype.card_fin] using
    card_binaryLowDegree (σ := SetMultilinear.Variables m c) (r := 1) hF

/-- Count a complete encoded-line branch. -/
theorem card_outer (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (EncodedLineLowDegreeTest.Sample F σ m c t r) =
      2 ^ outerBits (Fintype.card σ) m c t r := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_prod, card_hadamard, card_inner hF]
  simp only [Fintype.card_fun, BinaryLocalCorrection.InnerPoint, SetMultilinear.Variables,
    Fintype.card_prod, Fintype.card_fin, ZMod.card, hF, ← pow_mul, ← pow_add]
  congr 1
  unfold outerBits
  ring

end Finite
section Field

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]
variable {n m c t r : ℕ}

local instance : Fintype (BinaryLocalCorrection.InnerPoint F m c) := inferInstance
local instance : Fintype (BinaryLocalCorrection.InnerSeed F m c t) := inferInstance
local instance : Fintype (BinaryZeroOnGridCorrection.CallSeed F σ m c t) := inferInstance
local instance : Fintype (BinaryZeroOnGridCorrection.CallSeed F (Fin n ⊕ Fin n) m c t) :=
  inferInstance
local instance : Fintype (DerivedZeroOnGrid.GridRandomness F n m c t) := inferInstance
local instance : Fintype (DerivedZeroOnGrid.TestSample F n m c t r) := inferInstance

/-- One corrector seed has exactly one nonzero-field draw. -/
theorem card_call (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (BinaryZeroOnGridCorrection.CallSeed F σ m c t) =
      (Fintype.card F - 1) *
        2 ^ (t * Fintype.card σ + t * (c * m) + innerBits m c t) := by
  classical
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, card_inner hF,
    Fintype.card_units]
  simp only [Fintype.card_fun, BinaryLocalCorrection.InnerPoint, SetMultilinear.Variables,
    Fintype.card_prod, Fintype.card_fin, hF, ← pow_mul]
  simp only [pow_add]
  ring

/-- A derived-grid branch has two nonzero draws and an independent coefficient mask. -/
theorem card_derived (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (DerivedZeroOnGrid.TestSample F n m c t r) =
      (Fintype.card F - 1) ^ 2 * 2 ^ derivedBits n m c t r := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    card_call hF, card_coefficients]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_sum, ZMod.card, hF, ← pow_mul]
  calc
    _ = (2 ^ t - 1) ^ 2 *
        (2 ^ (t * n) * 2 ^ t *
          (2 ^ (t * (n + n) + t * (c * m) + innerBits m c t) *
            2 ^ (t * (n + n) + t * (c * m) + innerBits m c t)) *
          2 ^ coefficientBits t r) := by ring
    _ = _ := by
      simp only [← pow_add]
      congr 2
      unfold derivedBits
      ring

/-- Sum the seven branch exponents into the explicit closed formula. -/
theorem originalBits_eq_sum (n m c t : ℕ) :
    originalBits n m c t =
      outerBits n m c t 3 + outerBits (n + n) m c t 1 +
      outerBits (n + n) m c t 3 + outerBits ((n + n) + (n + n)) m c t 1 +
      derivedBits n m c t 3 + derivedBits (n + n) m c t 3 + (2 * t * n + t) := by
  simp only [originalBits, outerBits, derivedBits, innerBits, hadamardBits_one,
    hadamardBits_three, coefficientBits_three]
  ring

omit [Field F] [DecidableEq F] in
/-- The shared-label difference check samples two vertex points and one binary label. -/
theorem card_difference (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (((Fin n → F) × (Fin n → F)) × (Fin t → ZMod 2)) =
      2 ^ (2 * t * n + t) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    hF, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- The seven branch cardinalities, in their actual sampling order. -/
theorem card_branch (hF : Fintype.card F = 2 ^ t) (i : Fin 7) :
    Fintype.card (ThreeColorVerifier.BranchSeed F n m c t i) =
      ![2 ^ outerBits n m c t 3, 2 ^ outerBits (n + n) m c t 1,
        2 ^ outerBits (n + n) m c t 3, 2 ^ outerBits ((n + n) + (n + n)) m c t 1,
        (Fintype.card F - 1) ^ 2 * 2 ^ derivedBits n m c t 3,
        (Fintype.card F - 1) ^ 2 * 2 ^ derivedBits (n + n) m c t 3,
        2 ^ (2 * t * n + t)] i := by
  fin_cases i
  · calc
      _ = Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n) m c t 3) :=
        Fintype.card_congr (Equiv.refl _)
      _ = _ := by simpa only [Fintype.card_fin, Matrix.cons_val_zero',
          Matrix.cons_val_succ'] using
        card_outer (σ := Fin n) (m := m) (c := c) (r := 3) hF
  · calc
      _ = Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 1) :=
        Fintype.card_congr (Equiv.refl _)
      _ = _ := by simpa only [Fintype.card_sum, Fintype.card_fin,
          Matrix.cons_val_zero', Matrix.cons_val_succ'] using
        card_outer (σ := Fin n ⊕ Fin n) (m := m) (c := c) (r := 1) hF
  · calc
      _ = Fintype.card (EncodedLineLowDegreeTest.Sample F (Fin n ⊕ Fin n) m c t 3) :=
        Fintype.card_congr (Equiv.refl _)
      _ = _ := by simpa only [Fintype.card_sum, Fintype.card_fin,
          Matrix.cons_val_zero', Matrix.cons_val_succ'] using
        card_outer (σ := Fin n ⊕ Fin n) (m := m) (c := c) (r := 3) hF
  · calc
      _ = Fintype.card
          (EncodedLineLowDegreeTest.Sample F (Fin (n + n) ⊕ Fin (n + n)) m c t 1) :=
        Fintype.card_congr (Equiv.refl _)
      _ = _ := by simpa only [Fintype.card_sum, Fintype.card_fin,
          Matrix.cons_val_zero', Matrix.cons_val_succ'] using
        card_outer (σ := Fin (n + n) ⊕ Fin (n + n)) (m := m) (c := c) (r := 1) hF
  · exact card_derived hF
  · exact card_derived hF
  · exact card_difference hF

/-- Exact cardinality of the original seven-branch sampler. -/
theorem card_sample (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (ThreeColorVerifier.Sample F n m c t) =
      (Fintype.card F - 1) ^ 4 * 2 ^ originalBits n m c t := by
  rw [Fintype.card_pi]
  simp_rw [card_branch hF]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    mul_one]
  rw [originalBits_eq_sum]
  simp only [pow_add]
  ring

end Field
end PCP.Algebraic.ThreeColorSeedSize
