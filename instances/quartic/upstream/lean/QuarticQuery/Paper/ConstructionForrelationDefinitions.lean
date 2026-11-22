module

public import QuarticQuery.Forrelation.Circuit
public import QuarticQuery.Forrelation.Promise

/-!
# Section 2.1: exact Forrelation definitions

Compiled as part of the `QuarticQuery` library target.
These statements use the power-of-four domain fixed at the start of Section 2.
-/

public section

namespace QuarticQuery.Paper

open Finset Matrix QuarticQuery.Forrelation

/-- Ledger: def-walsh-sign. Verbatim normalization on `m = 4^t`.
This names the positive square root already used as `2^t` in the source. -/
theorem construction_forr_sqrt_mValue (t : ℕ) :
    Real.sqrt (mValue t : ℝ) = (2 : ℝ) ^ t := by
  rw [Forrelation.mValue_cast, ← pow_two]
  exact Real.sqrt_sq (by positivity)

/-- Ledger: def-walsh-sign. Verbatim joint definition of the bit signs,
Walsh entries, normalized matrix, uniform vector and diagonal matrices. -/
theorem construction_walsh_definitions (k t : ℕ)
    (z : BitInput (ForrelationCoord k t)) :
    (∀ b : Bool, bitSign b = (-1 : ℤ) ^ (if b then (1 : ℕ) else 0)) ∧
    (∀ i j : Fin (mValue t), walshSign t i j =
      (-1 : ℤ) ^ (∑ b ∈ range (2 * t),
        if i.val.testBit b && j.val.testBit b then (1 : ℕ) else 0)) ∧
    (∀ i j : Fin (mValue t), H t i j =
      (Real.sqrt (mValue t : ℝ))⁻¹ * (walshSign t i j : ℝ)) ∧
    (∀ i : Fin (mValue t), u t i = (Real.sqrt (mValue t : ℝ))⁻¹) ∧
    (∀ h : Fin k, signDiag z h = Matrix.diagonal fun i => (bitSign (z (h, i)) : ℝ)) := by
  refine ⟨?_, fun _ _ => rfl, ?_, ?_, fun _ => rfl⟩
  · intro b
    cases b <;> simp only [bitSign, Bool.false_eq_true, ↓reduceIte, pow_zero, pow_one]
  · intro i j
    rw [construction_forr_sqrt_mValue]
    rfl
  · intro i
    rw [construction_forr_sqrt_mValue]
    rfl

/-- Ledger: eq-3. Verbatim alternating product and threshold, in one statement.
The harmless extension to `k = 1` is supported by the existing product theorem. -/
theorem construction_equation_3 (k t : ℕ) (hk : 1 ≤ k)
    (z : BitInput (ForrelationCoord k t)) :
    Phi k t z = u t ⬝ᵥ
      (alternate (H t) (List.ofFn fun h : Fin k => signDiag z h) *ᵥ u t) ∧
    delta k = (2 : ℝ) ^ (-(5 * (k : ℤ))) :=
  ⟨Phi_eq_matrix_product k t hk z, rfl⟩

/-- Ledger: eq-4. Verbatim complete promise, including the undefined case,
disjointness, and the number of input bits. -/
theorem construction_equation_4 (k t : ℕ)
    (z : BitInput (ForrelationCoord k t)) :
    Fintype.card (ForrelationCoord k t) = k * mValue t ∧
    (P k t z = some true ↔ delta k ≤ Phi k t z) ∧
    (P k t z = some false ↔ |Phi k t z| ≤ delta k / 2) ∧
    (P k t z = none ↔ ¬ delta k ≤ Phi k t z ∧ ¬ |Phi k t z| ≤ delta k / 2) ∧
    ¬ (delta k ≤ Phi k t z ∧ |Phi k t z| ≤ delta k / 2) := by
  refine ⟨?_, P_eq_some_true_iff k t z, P_eq_some_false_iff k t z,
    P_eq_none_iff k t z, cases_disjoint k t z⟩
  simp only [ForrelationCoord, Fintype.card_prod, Fintype.card_fin]

/-- Ledger: eq-5. Verbatim definition of `L`; the complexity inequality is
separately stated as Lemma 2.1(i). -/
theorem construction_equation_5 (k t : ℕ) :
    Lvalue k t =
      ⌊Real.rpow (mValue t : ℝ) (1 - 1 / (k : ℝ)) /
        (Real.logb 2 (mValue t : ℝ)) ^ 2⌋₊ := rfl

/-- Ledger: claim-N-phi. Auxiliary scaling identity for the stated matrix word.
Every listed matrix contributes one occurrence of `A` to `tailProd`. -/
theorem construction_tailProd_smul {n : Type} [Fintype n] [DecidableEq n]
    (c : ℝ) (A : Matrix n n ℝ) (Ds : List (Matrix n n ℝ)) :
    tailProd (c • A) Ds = c ^ Ds.length • tailProd A Ds := by
  induction Ds with
  | nil => simp only [tailProd, List.length_nil, pow_zero, one_smul]
  | cons D Ds ih =>
    simp only [tailProd, List.length_cons, ih, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, pow_succ]

/-- Ledger: claim-N-phi. Auxiliary scaling identity with exactly `k-1`
Walsh factors, for the nonempty word in the paper. -/
theorem construction_alternate_smul {n : Type} [Fintype n] [DecidableEq n]
    (c : ℝ) (A : Matrix n n ℝ) (k : ℕ) (hk : 1 ≤ k)
    (D : Fin k → Matrix n n ℝ) :
    alternate (c • A) (List.ofFn D) = c ^ (k - 1) • alternate A (List.ofFn D) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  simp only [List.ofFn_succ, alternate, construction_tailProd_smul,
    Matrix.mul_smul, List.length_ofFn, Nat.add_sub_cancel]

/-- Ledger: claim-N-phi. Verbatim integer denominator and its positivity. -/
theorem construction_denominator (k t : ℕ) :
    0 < forrelationDenominator k t ∧
    (forrelationDenominator k t : ℝ) =
      (mValue t : ℝ) * (Real.sqrt (mValue t : ℝ)) ^ (k - 1) := by
  refine ⟨forrelationDenominator_pos k t, ?_⟩
  rw [construction_forr_sqrt_mValue]
  simp [forrelationDenominator, mValue]

/-- Ledger: claim-N-phi. Verbatim unnormalized product for the integer `N`.
The vector of ones on the left absorbs the first diagonal, giving `z₁ᵀ`. -/
theorem construction_numerator_matrix (k t : ℕ) (hk : 1 ≤ k)
    (z : BitInput (ForrelationCoord k t)) :
    (forrelationNumerator k t z : ℝ) =
      (fun _ : Fin (mValue t) => (1 : ℝ)) ⬝ᵥ
        (alternate (W t) (List.ofFn fun h : Fin k => signDiag z h) *ᵥ
          fun _ => (1 : ℝ)) := by
  have hr : (2 : ℝ) ^ t ≠ 0 := by positivity
  have hW : W t = (2 : ℝ) ^ t • H t := by
    rw [H, smul_smul, mul_inv_cancel₀ hr, one_smul]
  have hu : (fun _ : Fin (mValue t) => (1 : ℝ)) = (2 : ℝ) ^ t • u t := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, u, mul_inv_cancel₀ hr]
  have hM : (forrelationDenominator k t : ℝ) =
      ((2 : ℝ) ^ t * (2 : ℝ) ^ t) * ((2 : ℝ) ^ t) ^ (k - 1) := by
    rw [(construction_denominator k t).2, construction_forr_sqrt_mValue,
      Forrelation.mValue_cast]
  have hM0 : (forrelationDenominator k t : ℝ) ≠ 0 := by
    exact_mod_cast (forrelationDenominator_pos k t).ne'
  calc
    (forrelationNumerator k t z : ℝ) =
        (forrelationDenominator k t : ℝ) * Phi k t z := by
      rw [Phi]
      field_simp [hM0]
    _ = _ := by
      rw [hM, Phi_eq_matrix_product k t hk, hW,
        construction_alternate_smul _ _ k hk]
      simp only [hu, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      ring

/-- Ledger: claim-N-phi. Verbatim joint integer representation, normalization,
positive denominator, and the `±1` entries of `W`. -/
theorem construction_N_phi (k t : ℕ) (hk : 1 ≤ k)
    (z : BitInput (ForrelationCoord k t)) :
    (forrelationNumerator k t z : ℝ) =
      (fun _ : Fin (mValue t) => (1 : ℝ)) ⬝ᵥ
        (alternate (W t) (List.ofFn fun h : Fin k => signDiag z h) *ᵥ
          fun _ => (1 : ℝ)) ∧
    Phi k t z = (forrelationNumerator k t z : ℝ) / (forrelationDenominator k t : ℝ) ∧
    0 < forrelationDenominator k t ∧
    (forrelationDenominator k t : ℝ) =
      (mValue t : ℝ) * (Real.sqrt (mValue t : ℝ)) ^ (k - 1) ∧
    W t = Real.sqrt (mValue t : ℝ) • H t ∧
    (∀ i j : Fin (mValue t), W t i j = 1 ∨ W t i j = -1) := by
  refine ⟨construction_numerator_matrix k t hk z, rfl,
    (construction_denominator k t).1, (construction_denominator k t).2, ?_, ?_⟩
  · rw [construction_forr_sqrt_mValue, H, smul_smul,
      mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ t ≠ 0), one_smul]
  · intro i j
    rcases walshSign_eq_one_or t i j with h | h
    · left
      simp only [W, Matrix.map_apply, walshZ, Matrix.of_apply, h,
        Int.coe_castRingHom, Int.cast_one]
    · right
      simp only [W, Matrix.map_apply, walshZ, Matrix.of_apply, h,
        Int.coe_castRingHom, Int.cast_neg, Int.cast_one]

/-- Ledger: claim-integer-tests. Verbatim integer comparisons and Boolean
output rules, stated extensionally on every input. -/
theorem construction_integer_tests (k t : ℕ)
    (z : BitInput (ForrelationCoord k t)) :
    (delta k ≤ Phi k t z ↔
      (2 : ℤ) ^ (5 * k) * forrelationNumerator k t z ≥ forrelationDenominator k t) ∧
    (|Phi k t z| ≤ delta k / 2 ↔
      (2 : ℤ) ^ (5 * k + 1) * |forrelationNumerator k t z| ≤ forrelationDenominator k t) ∧
    (promised (P k t) z ↔
      ((2 : ℤ) ^ (5 * k) * forrelationNumerator k t z ≥ forrelationDenominator k t ∨
       (2 : ℤ) ^ (5 * k + 1) * |forrelationNumerator k t z| ≤ forrelationDenominator k t)) ∧
    (P k t z = some true ↔
      (2 : ℤ) ^ (5 * k) * forrelationNumerator k t z ≥ forrelationDenominator k t) := by
  refine ⟨delta_le_Phi_iff k t z, abs_Phi_le_iff k t z, ?_, ?_⟩
  · rw [promised_P_iff, delta_le_Phi_iff, abs_Phi_le_iff]
  · rw [P_eq_some_true_iff, delta_le_Phi_iff]

end QuarticQuery.Paper
