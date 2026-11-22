/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialMaterializationCost
import PCP.Complexity.LangWordCodec
import PCP.Complexity.BinaryFieldInverseLang
import PCP.Algebraic.ThreeColorFields

/-!
# Numeric codes of stored binary field words

The fixed-width encoder and decoder agree with the coordinate-induced numeric
order used by the production root search. Zero padding is retained throughout.
-/

namespace PCP.Lang.BinaryFieldWordCode

open PCP.Algebraic BinaryField BinaryPolynomialSelector

/-- Equal-length binary words are determined by their little-endian integer value. -/
theorem value_injective {a b : List ℕ} (ha : Bits a) (hb : Bits b)
    (hlen : a.length = b.length) (hv : WordCodec.value a = WordCodec.value b) : a = b := by
  induction a generalizing b with
  | nil => simpa using hlen.symm
  | cons x a ih =>
    cases b with
    | nil => simp at hlen
    | cons y b =>
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have hxval := congrArg (fun n => n % 2) hv
      have htail := congrArg (fun n => n / 2) hv
      simp only [WordCodec.value] at hxval htail
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hxval
      simp only [Nat.add_mul_div_left _ _ (by decide : 0 < 2),
        Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, Nat.zero_add] at htail
      exact congrArg₂ List.cons hxval (ih (fun z hz => ha z (by simp [hz]))
        (fun z hz => hb z (by simp [hz])) (by simpa using hlen) htail)

theorem value_digits (t n : ℕ) (hn : n < 2 ^ t) : WordCodec.value (digits t n) = n := by
  induction t generalizing n with
  | zero =>
    have hn' : n = 0 := by simpa using hn
    simp [digits, WordCodec.value, hn']
  | succ t ih =>
    have hdiv : n / 2 < 2 ^ t := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa only [pow_succ] using hn
    rw [digits, WordCodec.value, ih _ hdiv]
    exact Nat.mod_add_div _ _

/-- The stored word at a numeric code, using the same bit convention as field coordinates. -/
def word (t : ℕ) (i : Fin (2 ^ t)) : BinaryWordMaterialization.Word t :=
  BinaryWordMaterialization.ofWord ((BinaryIrreduciblePolynomial.coefficientEquiv t).symm i)

theorem encode_word (t : ℕ) (i : Fin (2 ^ t)) : encode (word t i) = digits t i.val := by
  rw [digits_ofFn, encode, word]
  simp only [BinaryWordMaterialization.toWord_ofWord]
  rfl

theorem value_encode_word (t : ℕ) (i : Fin (2 ^ t)) : WordCodec.value (encode (word t i)) = i := by
  rw [encode_word]
  exact value_digits _ _ i.isLt

theorem value_encode_one (t : ℕ) (ht : 0 < t) :
    WordCodec.value (encode (BinaryWordMaterialization.one t)) = 1 := by
  rw [BinaryFieldPower.encode_one ht]
  have hz : WordCodec.value (List.replicate (t - 1) 0) = 0 := by
    induction t - 1 with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, WordCodec.value, ih]
  simp [WordCodec.value, hz]

theorem value_encode_eq_one_iff {t : ℕ} (ht : 0 < t) (w : BinaryWordMaterialization.Word t) :
    WordCodec.value (encode w) = 1 ↔ w = BinaryWordMaterialization.one t := by
  constructor
  · intro h
    apply BinaryFieldInverse.encode_injective
    exact value_injective (encode_bits _) (encode_bits _) (by simp)
      (h.trans (value_encode_one t ht).symm)
  · rintro rfl
    exact value_encode_one t ht

/-- The stored word at an address is exactly the field element at that production address. -/
theorem fieldCode_symm (k : ℕ) (i : Fin (2 ^ (4 * (k + 1)))) :
    (ThreeColorFields.fieldCode k).symm i =
      (⟨word (4 * (k + 1)) i⟩ : ThreeColorFields.FieldFamily k) := by
  rfl

theorem value_power_eq_one_iff {t : ℕ} [NeZero t]
    (w : BinaryWordMaterialization.Word t) (p : ℕ) :
    WordCodec.value (encode (BinaryWordMaterialization.fieldPower w p)) = 1 ↔
      (⟨w⟩ : BinaryMaterializedField.Element t) ^ p = 1 := by
  rw [value_encode_eq_one_iff (Nat.pos_of_ne_zero (NeZero.ne t))]
  have hpow : BinaryMaterializedField.reference
      ((⟨w⟩ : BinaryMaterializedField.Element t) ^ p) =
        BinaryWordMaterialization.toField w ^ p :=
    (BinaryMaterializedField.referenceHom (t := t)).map_pow _ _
  constructor
  · intro h
    apply BinaryMaterializedField.reference_injective
    rw [hpow, ← BinaryWordMaterialization.toField_fieldPower, h,
      BinaryWordMaterialization.toField_one, BinaryMaterializedField.reference_one]
  · intro h
    apply BinaryWordMaterialization.toField_injective
    rw [BinaryWordMaterialization.toField_fieldPower, BinaryWordMaterialization.toField_one,
      ← hpow, h, BinaryMaterializedField.reference_one]

theorem word_eq_one_iff {t : ℕ} (ht : 0 < t) (i : Fin (2 ^ t)) :
    word t i = BinaryWordMaterialization.one t ↔ i.val = 1 := by
  rw [← value_encode_eq_one_iff ht, value_encode_word]

theorem element_word_eq_one_iff {t : ℕ} (ht : 0 < t) (i : Fin (2 ^ t)) :
    (⟨word t i⟩ : BinaryMaterializedField.Element t) = 1 ↔ i.val = 1 := by
  change BinaryMaterializedField.Element.mk (word t i) =
    BinaryMaterializedField.Element.mk (BinaryWordMaterialization.one t) ↔ _
  rw [BinaryMaterializedField.Element.mk.injEq, word_eq_one_iff ht]

end PCP.Lang.BinaryFieldWordCode
