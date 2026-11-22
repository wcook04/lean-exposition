import PCP.Complexity.ThreeColorRawSeedLang
import PCP.Complexity.LangSeedValue

/-!
# Exact identification of the decoded seven branch seeds
-/

namespace PCP.Lang.RawSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorSeedSize ThreeColorFullFieldSampling SeedArithmetic

theorem split_mod_product (code : ℕ) (rs : List ℕ) :
    (MixedRadixDecode.split (code % rs.prod) rs).1 = (MixedRadixDecode.split code rs).1 := by
  induction rs generalizing code with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.prod_cons, MixedRadixDecode.split, Nat.mod_mul_right_mod,
        Nat.mod_mul_right_div_self, ih]

theorem split_codecPi {k : ℕ} {A : Fin k → Type*} (cs : ∀ i, Codec (A i)) (s : ∀ i, A i) :
    (MixedRadixDecode.split ((Codec.piFin cs).equiv s).val
      (List.ofFn (fun i => (cs i).size))).1 = List.ofFn (fun i => ((cs i).equiv (s i)).val) := by
  rw [MixedRadixDecode.split_finPi (fun i => (cs i).size) ((Codec.piFin cs).equiv s)]
  congr 1
  funext i
  change (finPiFinEquiv.symm (finPiFinEquiv (fun j => (cs j).equiv (s j))) i).val = _
  rw [Equiv.symm_apply_apply]

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}

/-- Actual inputs, without an assumed precomputed radix list. -/
theorem program_sample (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ)
    (sample : RawSample F n m c t) (st : State 16 4)
    (hc : Context n m c t ((rawCodec ρ n m c).equiv sample).val st) :
    (program.run st).1.lists 1 =
      List.ofFn (fun i => ((branchCodec ρ n m c i).equiv (sample i)).val) := by
  rw [program_run n m c t _ st hc]
  simp only [← branchCodec_size ρ n m c]
  exact split_codecPi (branchCodec ρ n m c) sample

/-- Arbitrary-length public bits decode the exact production seed, with zero padding. -/
theorem program_bits (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) (bits : List Bool)
    (st : State 16 4) (hc : Context n m c t (Machine.bitsValue bits) st) :
    (program.run st).1.lists 1 = List.ofFn (fun i => ((branchCodec ρ n m c i).equiv
      (((ThreeColorSeedIndex.equiv ρ n m c).symm
        (SeedBitCompatibility.seedOfBits (rawBits n m c t) bits)) i)).val) := by
  rw [program_run n m c t _ st hc]
  let sample := (ThreeColorSeedIndex.equiv ρ n m c).symm
    (SeedBitCompatibility.seedOfBits (rawBits n m c t) bits)
  have hcode := SeedValue.rawSeed_code ρ n m c bits
  have hprod : (List.ofFn (fun i => 2 ^ branchBits n m c t i)).prod =
      2 ^ rawBits n m c t := by
    rw [List.prod_ofFn, Finset.prod_pow_eq_pow_sum, branchBits_sum]
  rw [← split_mod_product, hprod, ← hcode]
  simp only [← branchCodec_size ρ n m c]
  exact split_codecPi (branchCodec ρ n m c) sample

end PCP.Lang.RawSeed
