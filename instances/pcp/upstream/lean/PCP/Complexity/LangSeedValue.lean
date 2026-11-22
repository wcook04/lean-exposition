import PCP.Complexity.LangWordCodec
import PCP.Algebraic.SeedBitCompatibility
import PCP.Algebraic.ThreeColorSeedIndex

/-!
# Numeric value of arbitrary production seed lists

Missing seed bits are zero and excess bits are ignored. The stored word decoder's
value therefore agrees with the production structural seed after reduction by
the exact seed cardinality.
-/

namespace PCP.Lang.SeedValue

open PCP.Algebraic SeedBitCompatibility BinarySeedPadding ThreeColorSeedIndex

theorem bitsValue_testBit (bs : List Bool) (i : ℕ) :
    (Machine.bitsValue bs).testBit i = bs.getD i false := by
  induction bs generalizing i with
  | nil => simp
  | cons b bs ih =>
      cases i with
      | zero => simp [Machine.bitsValue_cons]
      | succ i => simpa [Machine.bitsValue_cons, Nat.testBit_bit_succ] using ih i

theorem decodeSeed_val (b : ℕ) (bs : List Bool) :
    (decodeSeed b bs).val = Machine.bitsValue bs % 2 ^ b := by
  have h : decodeSeed b bs = ⟨Machine.bitsValue bs % 2 ^ b,
      Nat.mod_lt _ (by positivity)⟩ := by
    apply (finSeedEquiv b).injective
    rw [finSeedEquiv_decodeSeed]
    funext i
    rw [finSeedEquiv_apply_testBit]
    simp [seedOfBits, Nat.testBit_mod_two_pow, i.isLt, bitsValue_testBit]
  exact congrArg Fin.val h

/-- All seven seeds use the same numeric residue as the public bit-list convention. -/
theorem rawSeed_code {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) (bs : List Bool) :
    ((rawCodec ρ n m c).equiv ((ThreeColorSeedIndex.equiv ρ n m c).symm
      (seedOfBits (ThreeColorSeedSize.rawBits n m c t) bs))).val =
      Machine.bitsValue bs % 2 ^ ThreeColorSeedSize.rawBits n m c t := by
  have h := congrArg (fun z => ((finSeedEquiv (ThreeColorSeedSize.rawBits n m c t)).symm z).val)
    ((ThreeColorSeedIndex.equiv ρ n m c).apply_symm_apply
      (seedOfBits (ThreeColorSeedSize.rawBits n m c t) bs))
  simp only [ThreeColorSeedIndex.equiv, Equiv.trans_apply, Equiv.symm_apply_apply] at h
  exact h.trans (decodeSeed_val _ bs)

end PCP.Lang.SeedValue
