import PCP.Complexity.LangSeedValue
import PCP.Complexity.LangTakePad
import PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

/-! Exact random-block slicing for the concrete amplified verifier. -/

namespace PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

open SeedBitCompatibility

theorem blockSeed_getD (k b : ℕ) (bits : List Bool) (i : Fin k) (j : Fin b) :
    (bitsOfFin b (FiniteRepetition.blockSeedEquiv k b (decodeSeed (k*b) bits) i)).getD
      j.val false = bits.getD (b*i.val+j.val) false := by
  rw [bitsOfFin_getD]
  change (((finFunctionFinEquiv.symm
    (finCongr _ (decodeSeed (k*b) bits))) i).val).testBit j.val = _
  rw [finFunctionFinEquiv_symm_apply_val]
  change (((decodeSeed (k*b) bits).val / (2^b)^i.val) % 2^b).testBit j.val = _
  rw [PCP.Lang.SeedValue.decodeSeed_val]
  rw [Nat.testBit_mod_two_pow, ← Nat.pow_mul, Nat.testBit_div_two_pow,
    Nat.testBit_mod_two_pow]
  have hi : j.val + b*i.val < k*b := by nlinarith [i.isLt, j.isLt]
  simp only [j.isLt, decide_true, Bool.true_and, hi, PCP.Lang.SeedValue.bitsValue_testBit]
  congr 1
  omega

theorem blockBits_getD (k : ℕ) (x bits : List Bool) (i : Fin k)
    (j : Fin (ThreeColorCanonicalVerifier.randomBudget x.length)) :
    (blockBits k x bits i).getD j.val false =
      bits.getD (ThreeColorCanonicalVerifier.randomBudget x.length*i.val+j.val) false :=
  blockSeed_getD _ _ _ _ _

/-- Numeric blocks used by the concrete list routine are exactly the verifier's bit blocks. -/
theorem blockSeed_map (k b : ℕ) (bits : List Bool) (i : Fin k) :
    (bitsOfFin b (FiniteRepetition.blockSeedEquiv k b (decodeSeed (k*b) bits) i)).map
      Bool.toNat = PCP.Lang.TakePad.take b ((bits.map Bool.toNat).drop (b*i.val)) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hji : j < b := by simpa only [List.length_map, length_bitsOfFin] using hj
    have h := congrArg Bool.toNat (blockSeed_getD k b bits i ⟨j, hji⟩)
    rw [List.getD_eq_getElem _ _ (by simpa only [length_bitsOfFin] using hji)] at h
    rw [List.getElem_map, h]
    rw [← List.getD_eq_getElem _ 0 hj', PCP.Lang.TakePad.getD_take b j _ hji]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map]
    exact (Option.getD_map Bool.toNat false (bits[b*i.val+j]?)).symm

theorem blockBits_map (k : ℕ) (x bits : List Bool) (i : Fin k) :
    (blockBits k x bits i).map Bool.toNat = PCP.Lang.TakePad.take
      (ThreeColorCanonicalVerifier.randomBudget x.length)
      ((bits.map Bool.toNat).drop (ThreeColorCanonicalVerifier.randomBudget x.length*i.val)) :=
  blockSeed_map _ _ _ _

/-- A fixed-width Boolean prefix; missing random cells contribute false. -/
def paddedBits (b : ℕ) (bits : List Bool) : List Bool :=
  bits.take b ++ List.replicate (b-bits.length) false

@[simp] theorem paddedBits_length (b : ℕ) (bits : List Bool) :
    (paddedBits b bits).length = b := by
  simp [paddedBits]
  omega

theorem paddedBits_map (b : ℕ) (bits : List Bool) :
    (paddedBits b bits).map Bool.toNat = PCP.Lang.TakePad.take b (bits.map Bool.toNat) := by
  simp [paddedBits, PCP.Lang.TakePad.take, List.map_take]

theorem blockBits_eq_padded (k : ℕ) (x bits : List Bool) (i : Fin k) :
    blockBits k x bits i = paddedBits (ThreeColorCanonicalVerifier.randomBudget x.length)
      (bits.drop (ThreeColorCanonicalVerifier.randomBudget x.length*i.val)) := by
  have hb : Function.Injective Bool.toNat := by decide
  apply (List.map_inj_right fun _ _ h => hb h).mp
  rw [blockBits_map, paddedBits_map, List.map_drop]

end PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm
