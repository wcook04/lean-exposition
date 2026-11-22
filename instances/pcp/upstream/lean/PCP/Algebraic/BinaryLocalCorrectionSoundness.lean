/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryLocalCorrection
import PCP.Algebraic.BinaryLocalRowDecoding
import PCP.Algebraic.HadamardHomogeneousDistance
import PCP.Algebraic.LineTableLocalCorrection

/-!
# Soundness of the weighted binary local corrector

All rejection and failure probabilities use the concrete `Sample` distribution.
The nearby inner polynomials are constructed from actual inner-test rejection.
The final failure event includes both explicit rejection and a wrong returned bit.
-/

namespace PCP.Algebraic.BinaryLocalCorrection

open Finset PolynomialLine BinaryPolynomialSpace Hadamard AffineLineSampling
open scoped BigOperators

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {m c t : ℕ}

/-- The sum of both local-correction losses and the two direct rejection losses. -/
def soundnessConstant (c : ℕ) : ℚ :=
  2 + 2 * (c + 1 : ℕ) * BinaryLocalRowDecoding.decodingConstant c

theorem soundnessConstant_nonneg (c : ℕ) : 0 ≤ soundnessConstant c := by
  unfold soundnessConstant
  positivity [BinaryLocalRowDecoding.decodingConstant_nonneg c]

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

/-- Actual rejection of the concrete procedure, including either failed check. -/
noncomputable def rejectionRate (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) : ℚ :=
  fraction (fun s : Sample F σ m c t => sample ρ nodes ζ f H a s = none)

theorem rejectionRate_nonneg (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) :
    0 ≤ rejectionRate ρ nodes ζ f H a := fraction_nonneg _

private theorem expect_pair {A B : Type*} [Fintype A] [Fintype B] (k : A × B → ℚ) :
    (𝔼 p, k p) = 𝔼 a, 𝔼 b, k (a, b) := by
  simpa only [univ_product_univ] using expect_product univ univ k

omit [Algebra (ZMod 2) F] in
private theorem expect_sample (k : Sample F σ m c t → ℚ) :
    (𝔼 s, k s) = 𝔼 b, 𝔼 z, 𝔼 vw, 𝔼 s, k (b, (z, (vw, s))) := by
  rw [expect_pair]
  apply expect_congr rfl
  intro b _
  rw [expect_pair]
  apply expect_congr rfl
  intro z _
  rw [expect_pair]

private theorem distance_expect {A B : Type*} [Fintype A] [DecidableEq B] (k l : A → B) :
    relativeDistance k l = 𝔼 a, if k a ≠ l a then (1 : ℚ) else 0 := by
  rw [← fraction_ne_eq_relativeDistance, fraction_eq_expect]

omit [Algebra (ZMod 2) F] in
private theorem distance_sample_comparison {A : Type*} [DecidableEq A]
    (k l : ((σ → F) × Fˣ) → (Fin t → ZMod 2) → A) :
    relativeDistance
      (fun s : Sample F σ m c t => k (s.1, s.2.1) s.2.2.1.2)
      (fun s => l (s.1, s.2.1) s.2.2.1.2) =
      relativeDistance (fun p : ((σ → F) × Fˣ) × (Fin t → ZMod 2) => k p.1 p.2)
        (fun p => l p.1 p.2) := by
  rw [distance_expect, expect_sample]
  conv_rhs => rw [distance_expect, expect_pair, expect_pair]
  apply expect_congr rfl
  intro b _
  apply expect_congr rfl
  intro z _
  change (𝔼 vw : InnerPoint F m c × (Fin t → ZMod 2),
    𝔼 _s : InnerSeed F m c t, if k (b, z) vw.2 ≠ l (b, z) vw.2 then (1 : ℚ) else 0) =
    𝔼 w, if k (b, z) w ≠ l (b, z) w then (1 : ℚ) else 0
  simp only [Fintype.expect_const]
  rw [expect_pair]
  dsimp only
  exact Fintype.expect_const (ι := InnerPoint F m c) (M := ℚ)
    (𝔼 w, if k (b, z) w ≠ l (b, z) w then (1 : ℚ) else 0)

omit [Algebra (ZMod 2) F] in
private theorem distance_sample_origin {A : Type*} [DecidableEq A]
    (k l : (σ → F) → (Fin t → ZMod 2) → A) :
    relativeDistance
      (fun s : Sample F σ m c t => k s.1 s.2.2.1.2)
      (fun s => l s.1 s.2.2.1.2) =
      relativeDistance (fun p : (σ → F) × (Fin t → ZMod 2) => k p.1 p.2)
        (fun p => l p.1 p.2) := by
  rw [distance_sample_comparison (m := m) (c := c)
    (fun bz w => k bz.1 w) (fun bz w => l bz.1 w)]
  simp only [distance_expect]
  rw [expect_pair, expect_pair, expect_pair]
  apply expect_congr rfl
  intro b _
  change (𝔼 _z : Fˣ, 𝔼 w, if k b w ≠ l b w then (1 : ℚ) else 0) = _
  exact Fintype.expect_const _

/-- Both uses of inner correction, distinguished by the selected parameter. -/
noncomputable def correctedAt (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (ζ : F) (H : (σ → F) → RowOracle F m c t)
    (parameter : Fˣ → F) (s : Sample F σ m c t) : ZMod 2 :=
  BinaryStandardLocalCorrection.correct c ζ ρ (H s.1)
    (SetMultilinear.evaluationPoint m c (parameter s.2.1)) s.2.2.1.1 s.2.2.1.2

/-- The corresponding true bit in a chosen decoded polynomial row. -/
noncomputable def decodedAt (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (Q : (σ → F) → MvPolynomial (SetMultilinear.Variables m c) F)
    (parameter : Fˣ → F) (s : Sample F σ m c t) : ZMod 2 :=
  linearEncode (ρ ((SetMultilinear.decode m c (Q s.1)).eval (parameter s.2.1))) s.2.2.1.2

/-- The only discrepancy from always returning the zero-parameter correction
is actual rejection, exactly rather than merely as an upper bound. -/
theorem distance_sample_to_corrected (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) :
    relativeDistance (sample ρ nodes ζ f H a)
      (fun s => some (correctedAt ρ ζ H (fun _ => 0) s)) =
      rejectionRate ρ nodes ζ f H a := by
  classical
  rw [← fraction_ne_eq_relativeDistance, rejectionRate]
  congr 1
  funext s
  apply propext
  simp only [sample, run, correctedAt]
  split_ifs <;> simp

/-- The independent inner test's average rejection is visible in actual rejection. -/
theorem average_inner_rejection_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) :
    (𝔼 b, BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H b)) ≤
      rejectionRate ρ nodes ζ f H a := by
  classical
  have hsub : fraction (fun s : Sample F σ m c t =>
      BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H s.1) s.2.2.2 ≠ true) ≤
      rejectionRate ρ nodes ζ f H a := by
    apply PointedLineSampling.fraction_mono
    intro s hs
    simp only [sample, run, hs, Bool.false_eq_true, ↓reduceIte]
  have he : fraction (fun s : Sample F σ m c t =>
      BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H s.1) s.2.2.2 ≠ true) =
      𝔼 b, BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H b) := by
    rw [fraction_eq_expect, expect_sample]
    apply expect_congr rfl
    intro b _
    change (𝔼 _z : Fˣ, 𝔼 _vw : InnerPoint F m c × (Fin t → ZMod 2),
      𝔼 s : InnerSeed F m c t,
        if BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H b) s ≠ true then (1 : ℚ) else 0) = _
    rw [Fintype.expect_const, Fintype.expect_const]
    exact (distance_expect _ _).symm
  rwa [he] at hsub

/-- A failed comparison also forces rejection, regardless of the inner test's outcome. -/
theorem comparison_error_le_rejection (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) :
    relativeDistance (correctedAt ρ ζ H (fun z => (z : F)))
      (fun s => f (point a s.1 s.2.1) (homogeneousIndex (le_refl 1) s.2.2.1.2)) ≤
      rejectionRate ρ nodes ζ f H a := by
  classical
  rw [← fraction_ne_eq_relativeDistance]
  apply PointedLineSampling.fraction_mono
  intro s hs
  change _ ≠ _ at hs
  simp only [sample, run, correctedAt] at hs ⊢
  split_ifs <;> simp_all

variable [CharP F 2]

/-- Both correction calls have the promised mean error even when they share
their sampled direction and homogeneous label. -/
theorem correction_error_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (H : (σ → F) → RowOracle F m c t)
    (Q : (σ → F) → MvPolynomial (SetMultilinear.Variables m c) F)
    (hQ : ∀ b, (Q b).totalDegree ≤ c) (parameter : Fˣ → F) :
    relativeDistance (correctedAt ρ ζ H parameter) (decodedAt ρ Q parameter) ≤
      (c + 1 : ℕ) * (𝔼 b, BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) (H b)
        (fun x => encode 1 (ρ (MvPolynomial.eval x (Q b))))) := by
  classical
  have hrow (b : σ → F) :
      relativeDistance
        (fun s : Fˣ × ((InnerPoint F m c × (Fin t → ZMod 2)) × InnerSeed F m c t) =>
          correctedAt ρ ζ H parameter (b, s))
        (fun s => decodedAt ρ Q parameter (b, s)) ≤
        (c + 1 : ℕ) * BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) (H b)
          (fun x => encode 1 (ρ (MvPolynomial.eval x (Q b)))) := by
    apply relativeDistance_prod_le
    intro z
    simp only [correctedAt, decodedAt, SetMultilinear.eval_decode]
    rw [relativeDistance_comp_fst
      (fun vw : InnerPoint F m c × (Fin t → ZMod 2) =>
        BinaryStandardLocalCorrection.correct c ζ ρ (H b)
          (SetMultilinear.evaluationPoint m c (parameter z)) vw.1 vw.2)
      (fun vw => linearEncode (ρ (MvPolynomial.eval
        (SetMultilinear.evaluationPoint m c (parameter z)) (Q b))) vw.2)]
    exact BinaryStandardLocalCorrection.failure_le ρ hζ (Q b) (hQ b) (H b) _
  rw [relativeDistance_prod, Fintype.expect_eq_sum_div_card]
  calc
    _ ≤ (∑ b, (c + 1 : ℕ) * BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) (H b)
        (fun x => encode 1 (ρ (MvPolynomial.eval x (Q b))))) / Fintype.card (σ → F) :=
      div_le_div_of_nonneg_right (sum_le_sum (fun b _ => hrow b)) (Nat.cast_nonneg _)
    _ = _ := by rw [← mul_sum, mul_div_assoc]

variable [NeZero m]

/-- Soundness against an honestly encoded outer polynomial. The distance on
the left counts both `none` and an incorrect returned bit as failures. The inner
polynomials are decoded from arbitrary received rows without a small-error premise. -/
theorem failure_le
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    {D : ℕ} (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) {δ : ℚ}
    (hnear : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) f
      (fun x => encode 1 (ρ (MvPolynomial.eval x P))) ≤ δ) (a : σ → F) :
    relativeDistance (sample ρ nodes ζ f H a)
      (fun s : Sample F σ m c t => some (linearEncode (ρ (MvPolynomial.eval a P)) s.2.2.1.2)) ≤
      soundnessConstant c * rejectionRate ρ nodes ζ f H a + δ +
        (D : ℚ) / (2 * (Fintype.card F - 1 : ℕ)) := by
  classical
  choose Q hQ _hfull hhom using fun b =>
    BinaryLocalRowDecoding.exists_polynomial_distance_le hq (le_refl 1) ρ nodes hnodes (H b)
  let R := rejectionRate ρ nodes ζ f H a
  let K := BinaryLocalRowDecoding.decodingConstant c
  have hK : 0 ≤ K := BinaryLocalRowDecoding.decodingConstant_nonneg c
  have hmean : (𝔼 b, BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) (H b)
      (fun x => encode 1 (ρ (MvPolynomial.eval x (Q b))))) ≤ K * R := by
    calc
      _ ≤ 𝔼 b, K * BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H b) :=
        expect_le_expect (s := univ) (fun b _ => hhom b)
      _ = K * (𝔼 b, BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H b)) :=
        (mul_expect ..).symm
      _ ≤ K * R := mul_le_mul_of_nonneg_left
        (average_inner_rejection_le ρ nodes ζ f H a) hK
  have hcorrect (parameter : Fˣ → F) :
      relativeDistance (correctedAt ρ ζ H parameter) (decodedAt ρ Q parameter) ≤
        (c + 1 : ℕ) * K * R := by
    exact (correction_error_le ρ hζ H Q hQ parameter).trans
      ((mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)).trans_eq (by ring))
  let readPoint : Sample F σ m c t → ZMod 2 := fun s =>
    f (point a s.1 s.2.1) (homogeneousIndex (le_refl 1) s.2.2.1.2)
  let truth : Sample F σ m c t → ZMod 2 := fun s =>
    linearEncode (ρ (MvPolynomial.eval a P)) s.2.2.1.2
  have hcompare : relativeDistance (decodedAt ρ Q (fun z => (z : F))) readPoint ≤
      (c + 1 : ℕ) * K * R + R := by
    have ht := relativeDistance_triangle (decodedAt ρ Q (fun z => (z : F)))
      (correctedAt ρ ζ H (fun z => (z : F))) readPoint
    rw [relativeDistance_comm (decodedAt ρ Q (fun z => (z : F)))
      (correctedAt ρ ζ H (fun z => (z : F)))] at ht
    have hcheck := comparison_error_le_rejection ρ nodes ζ f H a
    change relativeDistance (correctedAt ρ ζ H (fun z => (z : F))) readPoint ≤ R at hcheck
    linarith [hcorrect (fun z => (z : F))]
  have hT (b : σ → F) : (SetMultilinear.decode m c (Q b)).natDegree ≤ D :=
    (SetMultilinear.natDegree_decode_le_of_totalDegree_le m c (Q b) (hQ b)).trans hdecode
  have hbridge : relativeDistance (decodedAt ρ Q (fun _ => 0)) truth ≤
      relativeDistance (decodedAt ρ Q (fun z => (z : F))) readPoint +
        BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) f
          (fun x => encode 1 (ρ (MvPolynomial.eval x P))) +
        ((D : ℚ) / (Fintype.card F - 1 : ℕ)) / 2 := by
    change relativeDistance
      (fun s : Sample F σ m c t =>
        linearEncode (ρ ((SetMultilinear.decode m c (Q s.1)).eval 0)) s.2.2.1.2)
      (fun s => linearEncode (ρ (MvPolynomial.eval a P)) s.2.2.1.2) ≤ _
    rw [distance_sample_origin
      (fun b w => linearEncode (ρ ((SetMultilinear.decode m c (Q b)).eval 0)) w)
      (fun _ w => linearEncode (ρ (MvPolynomial.eval a P)) w)]
    change _ ≤ relativeDistance
      (fun s : Sample F σ m c t =>
        linearEncode (ρ ((SetMultilinear.decode m c (Q s.1)).eval (s.2.1 : F))) s.2.2.1.2)
      (fun s => f (point a s.1 s.2.1) (homogeneousIndex (le_refl 1) s.2.2.1.2)) +
        BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) f
          (fun x => encode 1 (ρ (MvPolynomial.eval x P))) +
        ((D : ℚ) / (Fintype.card F - 1 : ℕ)) / 2
    rw [distance_sample_comparison
      (fun bz w => linearEncode (ρ ((SetMultilinear.decode m c (Q bz.1)).eval (bz.2 : F))) w)
      (fun bz w => f (point a bz.1 bz.2) (homogeneousIndex (le_refl 1) w))]
    simpa only [BinaryLagrangeConstraint.homogeneousDistance, encode_homogeneousIndex] using
      LineTableLocalCorrection.binary_origin_error_le_comparison_add_oracle_distance
        ρ ρ.injective (fun b => SetMultilinear.decode m c (Q b)) hT P hP a
        (fun x w => f x (homogeneousIndex (le_refl 1) w))
  have hreturn := relativeDistance_triangle (sample ρ nodes ζ f H a)
    (fun s => some (correctedAt ρ ζ H (fun _ => 0) s)) (fun s => some (truth s))
  rw [distance_sample_to_corrected,
    relativeDistance_map some (Option.some_injective _)] at hreturn
  have hzero := relativeDistance_triangle (correctedAt ρ ζ H (fun _ => 0))
    (decodedAt ρ Q (fun _ => 0)) truth
  have hgap : ((D : ℚ) / (Fintype.card F - 1 : ℕ)) / 2 =
      (D : ℚ) / (2 * (Fintype.card F - 1 : ℕ)) := by ring
  change relativeDistance (sample ρ nodes ζ f H a) (fun s => some (truth s)) ≤ _
  change _ ≤ soundnessConstant c * R + δ + _
  rw [← hgap]
  dsimp only [soundnessConstant]
  change _ ≤ (2 + 2 * (c + 1 : ℕ) * K) * R + δ + _
  change relativeDistance (sample ρ nodes ζ f H a) (fun s => some (truth s)) ≤
    R + relativeDistance (correctedAt ρ ζ H (fun _ => 0)) truth at hreturn
  linarith [hcorrect (fun _ => 0)]

/-- The same bound stated using the received point oracle's exact homogeneous distance. -/
theorem failure_le_distance
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    {D : ℕ} (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) (a : σ → F) :
    relativeDistance (sample ρ nodes ζ f H a)
      (fun s : Sample F σ m c t => some (linearEncode (ρ (MvPolynomial.eval a P)) s.2.2.1.2)) ≤
      soundnessConstant c * rejectionRate ρ nodes ζ f H a +
        BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) f
          (fun x => encode 1 (ρ (MvPolynomial.eval x P))) +
        (D : ℚ) / (2 * (Fintype.card F - 1 : ℕ)) :=
  failure_le hq ρ hnodes hζ P hP hdecode f H le_rfl a

/-- Full coefficient-oracle proximity suffices, with the factor two for homogeneous labels. -/
theorem failure_le_full_distance
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    {D : ℕ} (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D)
    (f : (σ → F) → Coefficients t 1 → ZMod 2)
    (H : (σ → F) → RowOracle F m c t) {δ : ℚ}
    (hnear : relativeDistance
      (fun p : (σ → F) × Coefficients t 1 => f p.1 p.2)
      (encodeFunction 1 (fun x => ρ (MvPolynomial.eval x P))) ≤ δ)
    (a : σ → F) :
    relativeDistance (sample ρ nodes ζ f H a)
      (fun s : Sample F σ m c t => some (linearEncode (ρ (MvPolynomial.eval a P)) s.2.2.1.2)) ≤
      soundnessConstant c * rejectionRate ρ nodes ζ f H a + 2 * δ +
        (D : ℚ) / (2 * (Fintype.card F - 1 : ℕ)) := by
  have hhom : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) f
      (fun x => encode 1 (ρ (MvPolynomial.eval x P))) ≤ 2 * δ :=
    (relativeDistance_homogeneous_le_twice_full f
      (fun x => encode 1 (ρ (MvPolynomial.eval x P)))).trans
        (mul_le_mul_of_nonneg_left hnear (by norm_num))
  exact failure_le hq ρ hnodes hζ P hP hdecode f H hhom a

end PCP.Algebraic.BinaryLocalCorrection
