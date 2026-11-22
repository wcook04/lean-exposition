import PCP.Complexity.BinaryFieldCodeLang

/-!
# Natural-code arithmetic agrees with the production binary field

The numeric interface is a concrete equivalence, with both round trips proved.
Its arithmetic results therefore denote the actual field sum, product, and
inverse, including zero inverse, rather than merely related coefficient words.
-/

namespace PCP.Lang.BinaryFieldCode

open PCP.Algebraic BinaryField BinaryFieldWordCode

/-- The natural-number code of a fixed-width stored coefficient word. -/
def code {t : ℕ} (v : BinaryWordMaterialization.Word t) : ℕ := WordCodec.value (encode v)

theorem code_lt {t : ℕ} (v : BinaryWordMaterialization.Word t) : code v < 2 ^ t := by
  simpa only [code, encode_length] using WordCodec.value_lt (encode_bits v)

@[simp] theorem code_word (t : ℕ) (i : Fin (2 ^ t)) : code (word t i) = i.val :=
  value_encode_word t i

@[simp] theorem word_code {t : ℕ} (v : BinaryWordMaterialization.Word t) :
    word t ⟨code v, code_lt v⟩ = v := by
  apply BinaryFieldInverse.encode_injective
  apply value_injective (encode_bits _) (encode_bits _) (by simp)
  exact value_encode_word t _

/-- Explicit finite field coordinates in increasing little-endian numeric order. -/
def fieldEquiv (t : ℕ) : BinaryMaterializedField.Element t ≃ Fin (2 ^ t) where
  toFun a := ⟨code a.coefficients, code_lt _⟩
  invFun i := ⟨word t i⟩
  left_inv a := by cases a; simp
  right_inv i := by apply Fin.ext; exact code_word t i

@[simp] theorem fieldEquiv_val {t : ℕ} (a : BinaryMaterializedField.Element t) :
    (fieldEquiv t a).val = code a.coefficients := rfl

@[simp] theorem fieldEquiv_symm (t : ℕ) (i : Fin (2 ^ t)) :
    (fieldEquiv t).symm i = ⟨word t i⟩ := rfl

/-- This codec is exactly the one used to order the production fields. -/
theorem fieldEquiv_production (k : ℕ) :
    fieldEquiv (4 * (k + 1)) = ThreeColorFields.fieldCode k := by
  have h : (fieldEquiv (4 * (k + 1))).symm = (ThreeColorFields.fieldCode k).symm := by
    ext i
    rfl
  exact congrArg Equiv.symm h

/-- Field semantics for each numeric binary operation. -/
def Op.fieldEval {t : ℕ} [NeZero t] : Op →
    BinaryMaterializedField.Element t → BinaryMaterializedField.Element t →
    BinaryMaterializedField.Element t
  | .add, a, b => a + b
  | .mul, a, b => a * b

@[simp] theorem eval_coefficients {t : ℕ} [NeZero t] (op : Op) (ht : 0 < t)
    (a b : BinaryMaterializedField.Element t) :
    op.eval ht a.coefficients b.coefficients = (op.fieldEval a b).coefficients := by
  cases op <;> rfl

/-- The complete binary program returns the numeric code of the actual field operation. -/
theorem binary_run_field {t : ℕ} [NeZero t] (op : Op) (st : State 36 11)
    (a b : BinaryMaterializedField.Element t) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = (fieldEquiv t a).val)
    (h25 : st.regs 25 = (fieldEquiv t b).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((binary op).run st).1.regs 26 = (fieldEquiv t (op.fieldEval a b)).val := by
  have h := binary_run op (Nat.pos_of_ne_zero (NeZero.ne t)) st
    (fieldEquiv t a) (fieldEquiv t b) h20 h24 h25 hm he
  change _ = WordCodec.value (encode (op.eval _
    (word t ⟨code a.coefficients, code_lt _⟩)
    (word t ⟨code b.coefficients, code_lt _⟩))) at h
  rw [word_code, word_code, eval_coefficients] at h
  exact h

/-- The complete inverse program returns the field inverse's code, including zero. -/
theorem inverse_run_field {t : ℕ} [NeZero t] (st : State 36 11)
    (a : BinaryMaterializedField.Element t) (h20 : st.regs 20 = t)
    (h24 : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    (inverse.run st).1.regs 26 = (fieldEquiv t a⁻¹).val := by
  have h := inverse_run st (fieldEquiv t a) h20 h24 hm he
  change _ = WordCodec.value (encode (BinaryWordMaterialization.inverse
    (word t ⟨code a.coefficients, code_lt _⟩))) at h
  rw [word_code] at h
  exact h

end PCP.Lang.BinaryFieldCode
