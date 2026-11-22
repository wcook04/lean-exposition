/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinarySeedPadding
import PCP.Complexity.SeedBits

/-!
# Compatibility with the verifier's actual random-bit lists

The explicit integer-to-field-bit equivalence reads the same little-endian bits
as `PCP.bitsOfFin`. A total decoder uses the available list cells, pads missing
cells with false and ignores cells beyond the specified width. Prefix extraction
therefore agrees with the actual canonical finite-seed semantics. These are
representation equalities, with no running-time claim.
-/

namespace PCP.Algebraic.SeedBitCompatibility

open BinarySeedPadding

/-- The explicit seed equivalence reads the indicated least-significant-first bit. -/
theorem finSeedEquiv_apply_testBit (b : ℕ) (r : Fin (2 ^ b)) (i : Fin b) :
    finSeedEquiv b r i = boolEquiv (r.val.testBit i.val) := by
  apply Fin.ext
  change r.val / 2 ^ i.val % 2 =
    (if r.val.testBit i.val then (1 : Fin 2) else 0).val
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (r.val / 2 ^ i.val) with h | h <;> simp [h]

/-- Every in-range lookup of the machine's seed list is the corresponding integer bit. -/
theorem bitsOfFin_getD (b : ℕ) (r : Fin (2 ^ b)) (i : Fin b) :
    (bitsOfFin b r).getD i.val false = r.val.testBit i.val := by
  rw [List.getD_eq_getElem _ _ (by simpa only [length_bitsOfFin] using i.isLt)]
  simp [bitsOfFin]

/-- The field-bit seed and the machine's list agree coordinate by coordinate. -/
theorem finSeedEquiv_apply_getD (b : ℕ) (r : Fin (2 ^ b)) (i : Fin b) :
    finSeedEquiv b r i = boolEquiv ((bitsOfFin b r).getD i.val false) := by
  rw [bitsOfFin_getD, finSeedEquiv_apply_testBit]

/-- Read a fixed-width field-bit seed from a Boolean list, padding with false. -/
def seedOfBits (b : ℕ) (bits : List Bool) : Seed b :=
  fun i => boolEquiv (bits.getD i.val false)

/-- The actual seed list reconstructs the exact field-bit seed used by the verifier. -/
theorem seedOfBits_bitsOfFin (b : ℕ) (r : Fin (2 ^ b)) :
    seedOfBits b (bitsOfFin b r) = finSeedEquiv b r := by
  funext i
  exact (finSeedEquiv_apply_getD b r i).symm

/-- A total explicit decoder of the first `b` list cells, with false padding. -/
def decodeSeed (b : ℕ) (bits : List Bool) : Fin (2 ^ b) :=
  (finSeedEquiv b).symm (seedOfBits b bits)

/-- Decoding an arbitrary list preserves each available bit within the requested width. -/
@[simp] theorem finSeedEquiv_decodeSeed (b : ℕ) (bits : List Bool) :
    finSeedEquiv b (decodeSeed b bits) = seedOfBits b bits :=
  (finSeedEquiv b).apply_symm_apply _

/-- Decoding the actual machine input recovers its exact original finite seed. -/
@[simp] theorem decodeSeed_bitsOfFin (b : ℕ) (r : Fin (2 ^ b)) :
    decodeSeed b (bitsOfFin b r) = r := by
  rw [decodeSeed, seedOfBits_bitsOfFin, Equiv.symm_apply_apply]

/-- Prefix extraction from any list is independent of the larger requested width. -/
theorem prefix_seedOfBits {a b : ℕ} (h : a ≤ b) (bits : List Bool) :
    BinarySeedPadding.prefix h (seedOfBits b bits) = seedOfBits a bits := rfl

/-- The requested initial cells of the actual input list are the canonical seed prefix. -/
theorem prefix_seedOfBits_bitsOfFin {a b : ℕ} (h : a ≤ b) (r : Fin (2 ^ b)) :
    seedOfBits a (bitsOfFin b r) = BinarySeedPadding.prefix h (finSeedEquiv b r) := by
  rw [← seedOfBits_bitsOfFin, prefix_seedOfBits]

/-- Reconstructing a list seed and then restricting it uses precisely the given prefix. -/
theorem prefix_finSeedEquiv_decodeSeed {a b : ℕ} (h : a ≤ b) (bits : List Bool) :
    BinarySeedPadding.prefix h (finSeedEquiv b (decodeSeed b bits)) =
      seedOfBits a bits := by
  rw [finSeedEquiv_decodeSeed, prefix_seedOfBits]

end PCP.Algebraic.SeedBitCompatibility
