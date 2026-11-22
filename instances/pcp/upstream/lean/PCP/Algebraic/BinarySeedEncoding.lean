/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorSeedSize
import PCP.Algebraic.ThreeColorFullFieldSeeds

/-!
# An exact fair-bit representation of the full-field sampler

Replacing the four nonzero-field draws by field draws makes the actual sample
space have cardinality `2^R`, with the explicit arithmetic exponent `rawBits`.
A finite equivalence therefore turns uniform bit vectors into exactly uniform
raw samples, preserving every normalized rejection probability. The equivalence
uses classical finite choice and is not itself an efficient sampler; the explicit
seed codec of `ThreeColorSeedIndex` serves that purpose.
-/

namespace PCP.Algebraic.ThreeColorSeedSize

open ThreeColorFullFieldSampling

variable {F : Type*} [Field F] [Fintype F] {n m c t : ℕ}

/-- The full-field replacement has the stated exact power-of-two cardinality. -/
theorem card_rawSample (hF : Fintype.card F = 2 ^ t) :
    Fintype.card (RawSample F n m c t) = 2 ^ rawBits n m c t := by
  classical
  apply Nat.eq_of_mul_eq_mul_right
    (pow_pos (Nat.sub_pos_of_lt (Fintype.one_lt_card (α := F))) 4)
  calc
    _ = Fintype.card (ThreeColorVerifier.Sample F n m c t) * Fintype.card F ^ 4 :=
      (card_sample_mul_card_pow (F := F) (n := n) (m := m) (c := c) (t := t)).symm
    _ = _ := by
      rw [card_sample hF, hF, rawBits, pow_add, ← pow_mul, Nat.mul_comm t 4]
      ring

/-- Binary field coordinates certify the field cardinality used by the seed count. -/
theorem card_field_of_coordinates [Algebra (ZMod 2) F]
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) : Fintype.card F = 2 ^ t := by
  calc
    Fintype.card F = Fintype.card (Fin t → ZMod 2) := Fintype.card_congr ρ.toEquiv
    _ = _ := by simp

/-- Exact finite fair-bit representation, with the explicit fixed seed length. -/
noncomputable def seedEquiv (hF : Fintype.card F = 2 ^ t) :
    RawSample F n m c t ≃ (Fin (rawBits n m c t) → ZMod 2) :=
  Fintype.equivOfCardEq ((card_rawSample hF).trans (by simp))

/-- Every normalized disagreement probability is unchanged by the actual seed equivalence. -/
theorem relativeDistance_seedEquiv {B : Type*} [DecidableEq B]
    (hF : Fintype.card F = 2 ^ t) (f g : RawSample F n m c t → B) :
    relativeDistance (fun b => f ((seedEquiv hF).symm b))
      (fun b => g ((seedEquiv hF).symm b)) = relativeDistance f g :=
  relativeDistance_comp_equiv (seedEquiv hF).symm f g

/-- A Boolean test consequently has exactly the same rejection under independent fair bits. -/
theorem rejection_seedEquiv (hF : Fintype.card F = 2 ^ t)
    (f : RawSample F n m c t → Bool) :
    relativeDistance (fun b => f ((seedEquiv hF).symm b)) (fun _ => true) =
      relativeDistance f (fun _ => true) :=
  relativeDistance_seedEquiv hF f (fun _ => true)

end PCP.Algebraic.ThreeColorSeedSize
