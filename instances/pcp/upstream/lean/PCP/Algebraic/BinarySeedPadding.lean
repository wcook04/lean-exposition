/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.FiniteDistance
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact padding of binary seeds

Restriction to an initial segment of a uniformly sampled bit vector is exactly
uniform. An explicit prefix/suffix equivalence gives the normalized statement
and both fiber counts, including zero-length segments. An explicit base-two
equivalence also identifies integer seeds with bit vectors of the stated length.
This representation alone carries no running-time claim.
-/

namespace PCP.Algebraic.BinarySeedPadding

abbrev Seed (b : ℕ) := Fin b → ZMod 2

/-- Keep exactly the initial `r` bits of a longer seed. -/
def «prefix» {r b : ℕ} (h : r ≤ b) (s : Seed b) : Seed r := s ∘ Fin.castLE h

/-- Split the coordinates into the prefix followed by the remaining suffix. -/
def splitCoordinates {r b : ℕ} (h : r ≤ b) : Fin b ≃ Fin r ⊕ Fin (b - r) :=
  (finCongr (Nat.add_sub_of_le h)).symm.trans finSumFinEquiv.symm

/-- A padded seed is exactly an independent prefix and suffix. -/
def splitSeedEquiv {r b : ℕ} (h : r ≤ b) : Seed b ≃ Seed r × Seed (b - r) :=
  (Equiv.arrowCongr (splitCoordinates h) (Equiv.refl (ZMod 2))).trans
    (Equiv.sumArrowEquivProdArrow (Fin r) (Fin (b - r)) (ZMod 2))

@[simp] theorem splitSeedEquiv_fst {r b : ℕ} (h : r ≤ b) (s : Seed b) :
    (splitSeedEquiv h s).1 = «prefix» h s := by
  funext i
  rfl

/-- The unused suffix, whose randomness does not change any prefix-only test. -/
def suffix {r b : ℕ} (h : r ≤ b) (s : Seed b) : Seed (b - r) := (splitSeedEquiv h s).2

/-- Fixing the prefix leaves precisely all possible suffixes. -/
def prefixFiberEquiv {r b : ℕ} (h : r ≤ b) (x : Seed r) :
    {s : Seed b // «prefix» h s = x} ≃ Seed (b - r) where
  toFun s := suffix h s.1
  invFun y := ⟨(splitSeedEquiv h).symm (x, y), by
    rw [← splitSeedEquiv_fst, Equiv.apply_symm_apply]⟩
  left_inv s := by
    apply Subtype.ext
    apply (splitSeedEquiv h).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact s.property.symm
    · rfl
  right_inv y := by simp only [suffix, Equiv.apply_symm_apply]

/-- Fixing the suffix leaves precisely all possible prefixes. -/
def suffixFiberEquiv {r b : ℕ} (h : r ≤ b) (y : Seed (b - r)) :
    {s : Seed b // suffix h s = y} ≃ Seed r where
  toFun s := «prefix» h s.1
  invFun x := ⟨(splitSeedEquiv h).symm (x, y), by
    simp only [suffix, Equiv.apply_symm_apply]⟩
  left_inv s := by
    apply Subtype.ext
    apply (splitSeedEquiv h).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact (splitSeedEquiv_fst h s.1).symm
    · exact s.property.symm
  right_inv x := by
    change «prefix» h ((splitSeedEquiv h).symm (x, y)) = x
    exact (splitSeedEquiv_fst h _).symm.trans
      (congrArg Prod.fst ((splitSeedEquiv h).apply_symm_apply (x, y)))

open scoped Classical in
/-- Every prefix has exactly the same number of completions. -/
theorem card_prefix_fiber {r b : ℕ} (h : r ≤ b) (x : Seed r) :
    Fintype.card {s : Seed b // «prefix» h s = x} = 2 ^ (b - r) := by
  rw [Fintype.card_congr (prefixFiberEquiv h x)]
  simp [Seed]

open scoped Classical in
/-- Every fixed suffix accompanies exactly all `2^r` prefixes. -/
theorem card_suffix_fiber {r b : ℕ} (h : r ≤ b) (y : Seed (b - r)) :
    Fintype.card {s : Seed b // suffix h s = y} = 2 ^ r := by
  rw [Fintype.card_congr (suffixFiberEquiv h y)]
  simp [Seed]

/-- Padding with independently uniform unused bits preserves normalized disagreement exactly. -/
theorem relativeDistance_prefix {B : Type*} [DecidableEq B] {r b : ℕ} (h : r ≤ b)
    (f g : Seed r → B) :
    relativeDistance (fun s => f («prefix» h s)) (fun s => g («prefix» h s)) =
      relativeDistance f g := by
  have hs := relativeDistance_comp_equiv (splitSeedEquiv h)
    (fun p : Seed r × Seed (b - r) => f p.1) (fun p => g p.1)
  exact hs.trans (relativeDistance_comp_fst f g)

/-- A finite integer seed represents a bit vector of the exact stated length. -/
def finSeedEquiv (b : ℕ) : Fin (2 ^ b) ≃ Seed b :=
  (@finFunctionFinEquiv 2 b).symm.trans
    (Equiv.arrowCongr (Equiv.refl (Fin b)) (ZMod.finEquiv 2).toEquiv)

/-- Integer-to-bit conversion followed by prefix restriction remains exactly uniform. -/
theorem relativeDistance_finSeed_prefix {B : Type*} [DecidableEq B] {r b : ℕ}
    (h : r ≤ b) (f g : Seed r → B) :
    relativeDistance (fun s : Fin (2 ^ b) => f («prefix» h (finSeedEquiv b s)))
      (fun s => g («prefix» h (finSeedEquiv b s))) = relativeDistance f g :=
  (relativeDistance_comp_equiv (finSeedEquiv b)
    (fun s => f («prefix» h s)) (fun s => g («prefix» h s))).trans
      (relativeDistance_prefix h f g)

/-- Boolean bits and binary-field bits agree by the usual explicit zero/one encoding. -/
def boolEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv := by decide
  right_inv := by decide

@[simp] theorem boolEquiv_false : boolEquiv false = 0 := rfl

@[simp] theorem boolEquiv_true : boolEquiv true = 1 := rfl

end PCP.Algebraic.BinarySeedPadding
