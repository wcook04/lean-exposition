/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorFullFieldSeeds
import PCP.Algebraic.FiniteSeedPadding
import PCP.Algebraic.ThreeColorVerifierCompleteness
import PCP.Algebraic.ThreeColorVerifierSoundness

/-!
# Whole-field sampling for the concrete three-color verifier

The four correction parameters are sampled from the whole field. A zero
parameter causes immediate acceptance and no oracle queries. Otherwise the
explicit seed decoder runs the existing seven-check verifier without changing
any other random coordinate. The rejection loss is exactly `((q-1)/q)^4`.
-/

namespace PCP.Algebraic.ThreeColorFullFieldSampling

open ThreeColorVerifier

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n m c t : ℕ}

/-- Accept unused zero-parameter seeds, otherwise run the actual verifier. -/
noncomputable def test (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (s : RawSample F n m c t) : Bool :=
  match decode s with
  | none => true
  | some a => ThreeColorVerifier.test ρ nodes ζ H G π a

/-- Unused seeds make no reads; valid seeds use exactly the original queries. -/
noncomputable def queries (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (s : RawSample F n m c t) : List (Query F n m c t) :=
  match decode s with
  | none => []
  | some a => ThreeColorVerifier.queries ρ nodes ζ H G a

@[simp] theorem test_pad (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (s : Sample F n m c t) :
    test ρ nodes ζ H G π (pad s) = ThreeColorVerifier.test ρ nodes ζ H G π s := by
  simp [test]

@[simp] theorem queries_pad (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (s : Sample F n m c t) :
    queries ρ nodes ζ H G (pad s) = ThreeColorVerifier.queries ρ nodes ζ H G s := by
  simp [queries]

theorem test_of_not_valid (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (s : RawSample F n m c t) (hs : ¬ Valid s) :
    test ρ nodes ζ H G π s = true := by
  simp [test, decode_of_not_valid s hs]

theorem queries_of_not_valid (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (s : RawSample F n m c t) (hs : ¬ Valid s) : queries ρ nodes ζ H G s = [] := by
  simp [queries, decode_of_not_valid s hs]

theorem queries_length_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (s : RawSample F n m c t) : (queries ρ nodes ζ H G s).length ≤ 20 * c + 107 := by
  cases h : decode s with
  | none => simp [queries, h]
  | some a =>
    simpa only [queries, h] using ThreeColorVerifier.queries_length_le ρ nodes ζ H G a

theorem test_congr (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π π' : Proof F n m c t) (s : RawSample F n m c t)
    (h : ∀ q ∈ queries ρ nodes ζ H G s, read π q = read π' q) :
    test ρ nodes ζ H G π s = test ρ nodes ζ H G π' s := by
  cases hs : decode s with
  | none => simp [test, hs]
  | some a =>
    simp only [test, hs]
    apply ThreeColorVerifier.test_congr ρ nodes ζ H G π π' a
    simpa only [queries, hs] using h

theorem test_complete (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) (hπ : ∀ a, ThreeColorVerifier.test ρ nodes ζ H G π a = true)
    (s : RawSample F n m c t) : test ρ nodes ζ H G π s = true := by
  cases hs : decode s <;> simp [test, hs, hπ]

section Completeness

variable [NeZero m] [CharP F 2]

/-- The same eight physical tables give perfect completeness on every raw seed. -/
theorem exists_proof_test_eq_true (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty) (G : SimpleGraph (Fin n → H)) (hG : G.Colorable 3)
    (hdegree : 5 * ((H.card - 1) * n) < m ^ c) :
    ∃ π : Proof F n m c t, ∀ s, test ρ nodes ζ H G π s = true := by
  obtain ⟨π, hπ⟩ := ThreeColorVerifier.exists_proof_test_eq_true
    ρ hnodes hζ hω H hH G hG hdegree
  exact ⟨π, test_complete ρ nodes ζ H G π hπ⟩

end Completeness

/-- Probability that all four whole-field correction parameters are nonzero. -/
def retention (q : ℕ) : ℚ := (((q : ℚ) - 1) / q) ^ 4

theorem retention_ge_sixteenth {q : ℕ} (hq : 2 ≤ q) : (1 : ℚ) / 16 ≤ retention q := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < q := by linarith
  have hh : (1 : ℚ) / 2 ≤ ((q : ℚ) - 1) / q := by
    apply (le_div_iff₀ hqpos).mpr
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1 / 2) hh 4
  norm_num [retention] at hp ⊢
  exact hp

section Finite

variable [Fintype F] [DecidableEq F]

/-- Rejection normalized by the actual enlarged finite seed space. -/
noncomputable def rejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) : ℚ :=
  relativeDistance (test ρ nodes ζ H G π) (fun _ => true)

theorem rejectionRate_eq_card_ratio (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    rejectionRate ρ nodes ζ H G π =
      ((Fintype.card (Sample F n m c t) : ℚ) / Fintype.card (RawSample F n m c t)) *
        ThreeColorVerifier.rejectionRate ρ nodes ζ H G π := by
  apply FiniteSeedPadding.rejectionRate_of_embedding embedding
  · exact test_pad ρ nodes ζ H G π
  · intro s hs
    exact test_of_not_valid ρ nodes ζ H G π s ((mem_range_embedding s).not.mp hs)

omit [Algebra (ZMod 2) F] in
theorem seed_card_ratio :
    (Fintype.card (Sample F n m c t) : ℚ) / Fintype.card (RawSample F n m c t) =
      retention (Fintype.card F) := by
  have hq : 1 ≤ Fintype.card F := Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hcross : (Fintype.card (Sample F n m c t) : ℚ) * (Fintype.card F : ℚ) ^ 4 =
      Fintype.card (RawSample F n m c t) * ((Fintype.card F : ℚ) - 1) ^ 4 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hq, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : ℚ))
        (card_sample_mul_card_pow (F := F) (n := n) (m := m) (c := c) (t := t))
  have hqne : (Fintype.card F : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsne : (Fintype.card (RawSample F n m c t) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold retention
  field_simp
  exact hcross

/-- The rejection loss is precisely the probability of four nonzero parameters. -/
theorem rejectionRate_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    rejectionRate ρ nodes ζ H G π = retention (Fintype.card F) *
      ThreeColorVerifier.rejectionRate ρ nodes ζ H G π := by
  rw [rejectionRate_eq_card_ratio, seed_card_ratio]

/-- Every finite field retains at least one sixteenth of the old rejection. -/
theorem rejectionRate_ge_sixteenth (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F) (H : Finset F) (G : SimpleGraph (Fin n → H))
    (π : Proof F n m c t) :
    ThreeColorVerifier.rejectionRate ρ nodes ζ H G π / 16 ≤
      rejectionRate ρ nodes ζ H G π := by
  rw [rejectionRate_eq]
  have h := mul_le_mul_of_nonneg_right
    (retention_ge_sixteenth (Fintype.one_lt_card : 1 < Fintype.card F))
    (ThreeColorVerifier.rejectionRate_nonneg ρ nodes ζ H G π)
  linarith

variable [NeZero m] [CharP F 2]

omit [DecidableEq F] in
open scoped Classical in
/-- Perfect completeness remains true after whole-field padding. -/
theorem exists_proof_rejectionRate_eq_zero (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : Function.Injective nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty) (G : SimpleGraph (Fin n → H)) (hG : G.Colorable 3)
    (hdegree : 5 * ((H.card - 1) * n) < m ^ c) :
    ∃ π : Proof F n m c t, rejectionRate ρ nodes ζ H G π = 0 := by
  classical
  obtain ⟨π, hπ⟩ := exists_proof_test_eq_true ρ hnodes hζ hω H hH G hG hdegree
  refine ⟨π, relativeDistance_eq_zero_iff.mpr ?_⟩
  funext s
  exact hπ s

omit [DecidableEq F] in
open scoped Classical in
/-- The concrete full-field test has a positive size-independent soundness gap. -/
theorem rejectionRate_ge_of_not_colorable
    (hc : 1 ≤ c)
    (hq : PointLineConstants.fieldFactor * (c * m ^ c) ^ 3 ≤ Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (H : Finset F) (hH : H.Nonempty)
    (hgrid : 100 * (c * m ^ c) * H.card ≤ Fintype.card F)
    (hdegree : (H.card - 1) * n ≤ c * m ^ c)
    (G : SimpleGraph (Fin n → H)) (hG : ¬ G.Colorable 3) (π : Proof F n m c t) :
    ThreeColorSoundnessBudget.gap c / 16 ≤ rejectionRate ρ nodes ζ H G π := by
  classical
  have h := ThreeColorVerifier.rejectionRate_ge_of_not_colorable
    hc hq ρ hnodes hζ hω H hH hgrid hdegree G hG π
  exact (div_le_div_of_nonneg_right h (by norm_num)).trans
    (rejectionRate_ge_sixteenth ρ nodes ζ H G π)

end Finite

end PCP.Algebraic.ThreeColorFullFieldSampling
