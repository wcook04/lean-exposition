/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PointLineSoundness
import PCP.Algebraic.EncodedLineLowDegreeTest
import PCP.Algebraic.BinaryLocalRowDecoding
import PCP.Algebraic.LineTableLocalCorrection

/-!
# Soundness of encoded-line low-degree testing

Every auxiliary received row is decoded to an actual inner polynomial, including
rows above the inner soundness threshold. Decoding the set-multilinear variables
then supplies actual degree-`c*m^c` line polynomials. The binary comparison bounds
their field point-versus-line rejection, to which the proved general point-line
theorem applies. No auxiliary proximity or soundness premise is assumed.

`exists_close` is Theorem 4.1. Its first conclusion bounds the distance over all
degree-`r` labels. Its second conclusion bounds the distance over the `2^t`
homogeneous degree-one labels only, whereas the paper bounds it over all
degree-at-most-one labels. The homogeneous form is what Claim 7.3 uses. Because
the outer parameter ranges over all of `F`, the general point-line theorem
applies directly, with factor `2` rather than the paper's `4`.
-/

namespace PCP.Algebraic.EncodedLineLowDegreeTest

open Finset PolynomialLine BinaryPolynomialSpace Hadamard BinaryLocalCorrection
open AffineLineSampling
open scoped BigOperators

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {m c t r : ℕ}
variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]

local instance : Fintype (InnerPoint F m c) := inferInstance
local instance : Fintype (InnerSeed F m c t) := inferInstance
local instance : Fintype (Hadamard.TestRandomness t r × InnerSeed F m c t) := inferInstance
local instance : Fintype (Sample F σ m c t r) := inferInstance
local instance : Nonempty (InnerSeed F m c t) := inferInstance
local instance : Nonempty (Hadamard.TestRandomness t r) := inferInstance
local instance : Nonempty (InnerPoint F m c) := inferInstance

/-- The virtual point-line rejection factor, after both binary decoding steps. -/
def lineErrorConstant (c : ℕ) : ℚ :=
  2 * ((c + 1 : ℕ) * BinaryLocalRowDecoding.decodingConstant c + 29)

/-- The final primary-oracle proximity factor. -/
def soundnessConstant (c : ℕ) : ℚ := 28 + lineErrorConstant c

theorem lineErrorConstant_nonneg (c : ℕ) : 0 ≤ lineErrorConstant c := by
  unfold lineErrorConstant
  positivity [BinaryLocalRowDecoding.decodingConstant_nonneg c]

theorem soundnessConstant_nonneg (c : ℕ) : 0 ≤ soundnessConstant c := by
  unfold soundnessConstant
  positivity [lineErrorConstant_nonneg c]

private theorem expect_pair {A B : Type*} [Fintype A] [Fintype B] (k : A × B → ℚ) :
    (𝔼 p, k p) = 𝔼 a, 𝔼 b, k (a, b) := by
  simpa only [univ_product_univ] using expect_product univ univ k

private theorem distance_expect {A B : Type*} [Fintype A] [DecidableEq B] (k l : A → B) :
    relativeDistance k l = 𝔼 a, if k a ≠ l a then (1 : ℚ) else 0 := by
  rw [← fraction_ne_eq_relativeDistance, fraction_eq_expect]

omit [Field F] [Algebra (ZMod 2) F] [DecidableEq F] in
private theorem expect_sample (k : Sample F σ m c t r → ℚ) :
    (𝔼 s, k s) = 𝔼 uv, 𝔼 z, 𝔼 vw, 𝔼 hi, k (uv, (z, (vw, hi))) := by
  rw [expect_pair]
  apply expect_congr rfl
  intro uv _
  rw [expect_pair]
  apply expect_congr rfl
  intro z _
  rw [expect_pair]

omit [DecidableEq F] in
/-- Primary Hadamard rejection is a marginal of the actual conjunction tester. -/
theorem primary_rejection_le (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t) :
    Hadamard.averageRejectionRate hr f ≤ rejectionRate hr ρ nodes ζ f H := by
  have hsub := relativeDistance_le_of_disagreement
    (fun s : Sample F σ m c t r => Hadamard.test hr (f s.1.1) s.2.2.2.1)
    (fun _ => true) (test hr ρ nodes ζ f H) (fun _ => true) (by
      intro s hs htest
      simp only [test, Bool.and_eq_true] at htest
      exact hs htest.1.1)
  have he : relativeDistance
      (fun s : Sample F σ m c t r => Hadamard.test hr (f s.1.1) s.2.2.2.1)
      (fun _ => true) = Hadamard.averageRejectionRate hr f := by
    rw [distance_expect, expect_sample]
    have hi (u : σ → F) :
        (𝔼 p : Hadamard.TestRandomness t r × InnerSeed F m c t,
          if Hadamard.test hr (f u) p.1 ≠ true then (1 : ℚ) else 0) =
          Hadamard.testRejectionRate hr (f u) := by
      rw [expect_pair]
      change (𝔼 h : Hadamard.TestRandomness t r, 𝔼 _i : InnerSeed F m c t,
        if Hadamard.test hr (f u) h ≠ true then (1 : ℚ) else 0) = _
      have hconst (h : Hadamard.TestRandomness t r) := Fintype.expect_const
        (ι := InnerSeed F m c t) (M := ℚ)
        (if Hadamard.test hr (f u) h ≠ true then (1 : ℚ) else 0)
      simp only [hconst]
      exact (distance_expect (Hadamard.test hr (f u)) (fun _ => true)).symm
    simp only [hi, Fintype.expect_const]
    rw [expect_pair]
    simp only [Fintype.expect_const]
    exact Fintype.expect_eq_sum_div_card _
  exact he ▸ hsub

omit [DecidableEq F] in
/-- Auxiliary inner rejection is another normalized marginal of actual rejection. -/
theorem inner_rejection_le (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t) :
    (𝔼 uv, BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H uv)) ≤
      rejectionRate hr ρ nodes ζ f H := by
  have hsub := relativeDistance_le_of_disagreement
    (fun s : Sample F σ m c t r =>
      BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H s.1) s.2.2.2.2)
    (fun _ => true) (test hr ρ nodes ζ f H) (fun _ => true) (by
      intro s hs htest
      simp only [test, Bool.and_eq_true] at htest
      exact hs htest.1.2)
  have he : relativeDistance
      (fun s : Sample F σ m c t r =>
        BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H s.1) s.2.2.2.2)
      (fun _ => true) = 𝔼 uv, BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H uv) := by
    rw [distance_expect, expect_sample]
    have hi (uv : Lines F σ) :
        (𝔼 p : Hadamard.TestRandomness t r × InnerSeed F m c t,
          if BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H uv) p.2 ≠ true
            then (1 : ℚ) else 0) =
          BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H uv) := by
      rw [expect_pair]
      exact (Fintype.expect_const (ι := Hadamard.TestRandomness t r) (M := ℚ)
        (𝔼 s : InnerSeed F m c t,
          if BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H uv) s ≠ true
            then (1 : ℚ) else 0)).trans
        (distance_expect (BinaryLowDegreeTest.test (le_refl 1) ρ nodes (H uv))
          (fun _ => true)).symm
    simp only [hi, Fintype.expect_const]
  exact he ▸ hsub

omit [DecidableEq F] in
/-- The bit comparison is tested even when either consistency check also fails. -/
theorem comparison_error_le (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (nodes : Fin (c + 1) → F) (ζ : F)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t) :
    relativeDistance (corrected ρ ζ H : Sample F σ m c t r → ZMod 2)
      (fun s => f (point s.1.1 s.1.2 s.2.1) (homogeneousIndex hr s.2.2.1.2)) ≤
      rejectionRate hr ρ nodes ζ f H := by
  apply relativeDistance_le_of_disagreement
  intro s hs htest
  simp only [test, Bool.and_eq_true] at htest
  exact hs (of_decide_eq_true htest.2)

omit [Algebra (ZMod 2) F] [DecidableEq F] in
private theorem distance_line_bits {A : Type*} [DecidableEq A]
    (k l : (Lines F σ × F) → (Fin t → ZMod 2) → A) :
    relativeDistance (fun s : Sample F σ m c t r => k (s.1, s.2.1) s.2.2.1.2)
      (fun s => l (s.1, s.2.1) s.2.2.1.2) =
      relativeDistance (fun p : (Lines F σ × F) × (Fin t → ZMod 2) => k p.1 p.2)
        (fun p => l p.1 p.2) := by
  rw [distance_expect, expect_sample]
  conv_rhs => rw [distance_expect, expect_pair, expect_pair]
  apply expect_congr rfl
  intro uv _
  apply expect_congr rfl
  intro z _
  change (𝔼 vw : InnerPoint F m c × (Fin t → ZMod 2),
    𝔼 _hi : Hadamard.TestRandomness t r × InnerSeed F m c t,
      if k (uv, z) vw.2 ≠ l (uv, z) vw.2 then (1 : ℚ) else 0) = _
  simp only [Fintype.expect_const]
  rw [expect_pair]
  dsimp only
  exact Fintype.expect_const (ι := InnerPoint F m c) (M := ℚ)
    (𝔼 w, if k (uv, z) w ≠ l (uv, z) w then (1 : ℚ) else 0)

omit [Algebra (ZMod 2) F] [DecidableEq F] in
private theorem distance_point_bits {A : Type*} [DecidableEq A]
    (k l : (σ → F) → (Fin t → ZMod 2) → A) :
    relativeDistance
      (fun s : Sample F σ m c t r => k (point s.1.1 s.1.2 s.2.1) s.2.2.1.2)
      (fun s => l (point s.1.1 s.1.2 s.2.1) s.2.2.1.2) =
      relativeDistance (fun p : (σ → F) × (Fin t → ZMod 2) => k p.1 p.2)
        (fun p => l p.1 p.2) := by
  rw [distance_line_bits
    (fun p w => k (point p.1.1 p.1.2 p.2) w)
    (fun p w => l (point p.1.1 p.1.2 p.2) w)]
  simp only [distance_expect]
  rw [expect_pair, expect_pair, expect_comm]
  conv_rhs => rw [expect_pair]
  have hp (z : F) :
      (𝔼 uv : Lines F σ, 𝔼 w, if k (point uv.1 uv.2 z) w ≠
        l (point uv.1 uv.2 z) w then (1 : ℚ) else 0) =
      𝔼 x, 𝔼 w, if k x w ≠ l x w then (1 : ℚ) else 0 :=
    expect_point (fun x => 𝔼 w, if k x w ≠ l x w then (1 : ℚ) else 0) z
  simp only [hp, Fintype.expect_const]

variable [CharP F 2]

omit [DecidableEq F] in
/-- Actual correction error averaged over every seed, for an arbitrary chosen inner table. -/
theorem correction_error_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Auxiliary F σ m c t)
    (Q : Lines F σ → MvPolynomial (SetMultilinear.Variables m c) F)
    (hQ : ∀ uv, (Q uv).totalDegree ≤ c) :
    relativeDistance (corrected ρ ζ H : Sample F σ m c t r → ZMod 2)
      (fun s => linearEncode (ρ ((SetMultilinear.decode m c (Q s.1)).eval s.2.1))
        s.2.2.1.2) ≤
      (c + 1 : ℕ) * (𝔼 uv, BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) (H uv)
        (fun x => encode 1 (ρ (MvPolynomial.eval x (Q uv))))) := by
  rw [distance_expect, expect_sample, mul_expect]
  apply expect_le_expect
  intro uv _
  apply le_trans _ (le_refl _)
  have he (z : F) :
      (𝔼 vw : InnerPoint F m c × (Fin t → ZMod 2),
        𝔼 _hi : Hadamard.TestRandomness t r × InnerSeed F m c t,
          if BinaryStandardLocalCorrection.correct c ζ ρ (H uv)
              (SetMultilinear.evaluationPoint m c z) vw.1 vw.2 ≠
            linearEncode (ρ ((SetMultilinear.decode m c (Q uv)).eval z)) vw.2
          then (1 : ℚ) else 0) ≤
        (c + 1 : ℕ) * BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) (H uv)
          (fun x => encode 1 (ρ (MvPolynomial.eval x (Q uv)))) := by
    simp only [Fintype.expect_const]
    rw [← distance_expect, SetMultilinear.eval_decode]
    exact BinaryStandardLocalCorrection.failure_le ρ hζ (Q uv) (hQ uv) (H uv) _
  exact (expect_le_expect (s := univ) (fun z _ => he z)).trans_eq (Fintype.expect_const _)

variable [NeZero m]

/-- The actual formal line table extracted from decoded inner polynomials. -/
noncomputable def decodedTable
    (Q : Lines F σ → MvPolynomial (SetMultilinear.Variables m c) F)
    (hQ : ∀ uv, (Q uv).totalDegree ≤ c) : PointLineTest.LineTable F σ (c * m ^ c) :=
  fun uv => ⟨SetMultilinear.decode m c (Q uv),
    SetMultilinear.natDegree_decode_le_of_totalDegree_le m c (Q uv) (hQ uv)⟩

/-- The tester constructs a nearby field function and an actual formal line table,
with point-line rejection controlled by its own rejection. No smallness is needed here. -/
theorem exists_decoded_table
    (hq : 2 * c < Fintype.card F)
    (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t) :
    ∃ (g : (σ → F) → F) (T : PointLineTest.LineTable F σ (c * m ^ c)),
      relativeDistance (fun p : (σ → F) × Coefficients t r => f p.1 p.2)
        (encodeFunction r (fun x => ρ (g x))) ≤ 28 * rejectionRate hr ρ nodes ζ f H ∧
      BinaryLagrangeConstraint.homogeneousDistance hr f (fun x => encode r (ρ (g x))) ≤
        28 * rejectionRate hr ρ nodes ζ f H ∧
      PointLineTest.rejectionRate g T ≤
        lineErrorConstant c * rejectionRate hr ρ nodes ζ f H := by
  classical
  let κ := rejectionRate hr ρ nodes ζ f H
  let K := BinaryLocalRowDecoding.decodingConstant c
  have hK : 0 ≤ K := BinaryLocalRowDecoding.decodingConstant_nonneg c
  obtain ⟨g, hfull, hhom⟩ := Hadamard.exists_field_function_of_average_rejectionRate hr ρ f
  have hprimary := primary_rejection_le hr ρ nodes ζ f H
  have hfull' : relativeDistance (fun p : (σ → F) × Coefficients t r => f p.1 p.2)
      (encodeFunction r (fun x => ρ (g x))) ≤ 28 * κ := by dsimp [κ]; linarith
  have hhom' : BinaryLagrangeConstraint.homogeneousDistance hr f
      (fun x => encode r (ρ (g x))) ≤ 28 * κ := by dsimp [κ]; linarith
  choose Q hQ _hQfull hQhom using fun uv =>
    BinaryLocalRowDecoding.exists_polynomial_distance_le hq (le_refl 1) ρ nodes hnodes (H uv)
  let T := decodedTable Q hQ
  refine ⟨g, T, hfull', hhom', ?_⟩
  have hmean : (𝔼 uv, BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) (H uv)
      (fun x => encode 1 (ρ (MvPolynomial.eval x (Q uv))))) ≤ K * κ := by
    calc
      _ ≤ 𝔼 uv, K * BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H uv) :=
        expect_le_expect (s := univ) (fun uv _ => hQhom uv)
      _ = K * (𝔼 uv, BinaryLowDegreeTest.rejectionRate (le_refl 1) ρ nodes (H uv)) :=
        (mul_expect ..).symm
      _ ≤ K * κ := mul_le_mul_of_nonneg_left (inner_rejection_le hr ρ nodes ζ f H) hK
  let decoded : Sample F σ m c t r → ZMod 2 := fun s =>
    linearEncode (ρ ((T s.1).val.eval s.2.1)) s.2.2.1.2
  let received : Sample F σ m c t r → ZMod 2 := fun s =>
    f (point s.1.1 s.1.2 s.2.1) (homogeneousIndex hr s.2.2.1.2)
  let field : Sample F σ m c t r → ZMod 2 := fun s =>
    linearEncode (ρ (g (point s.1.1 s.1.2 s.2.1))) s.2.2.1.2
  have hc : relativeDistance (corrected ρ ζ H) decoded ≤ (c + 1 : ℕ) * K * κ :=
    (correction_error_le ρ hζ H Q hQ).trans
      ((mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)).trans_eq (by ring))
  have hp : relativeDistance received field ≤ 28 * κ := by
    change relativeDistance
      (fun s : Sample F σ m c t r =>
        f (point s.1.1 s.1.2 s.2.1) (homogeneousIndex hr s.2.2.1.2))
      (fun s => linearEncode (ρ (g (point s.1.1 s.1.2 s.2.1))) s.2.2.1.2) ≤ _
    rw [distance_point_bits (fun x w => f x (homogeneousIndex hr w))
      (fun x w => linearEncode (ρ (g x)) w)]
    simpa only [BinaryLagrangeConstraint.homogeneousDistance, encode_homogeneousIndex] using hhom'
  have hhalf : relativeDistance decoded field = (1 : ℚ) / 2 *
      PointLineTest.rejectionRate g T := by
    change relativeDistance
      (fun s : Sample F σ m c t r =>
        linearEncode (ρ ((T s.1).val.eval s.2.1)) s.2.2.1.2)
      (fun s => linearEncode (ρ (g (point s.1.1 s.1.2 s.2.1))) s.2.2.1.2) = _
    rw [distance_line_bits
      (fun p w => linearEncode (ρ ((T p.1).val.eval p.2)) w)
      (fun p w => linearEncode (ρ (g (point p.1.1 p.1.2 p.2))) w),
      LineTableLocalCorrection.homogeneous_distance_eq_half ρ ρ.injective
        (fun p : Lines F σ × F => (T p.1).val.eval p.2)
        (fun p => g (point p.1.1 p.1.2 p.2)),
      PointLineTest.rejectionRate_eq_relativeDistance, relativeDistance_comm]
  have hcompare := comparison_error_le hr ρ nodes ζ f H
  change relativeDistance (corrected ρ ζ H) received ≤ κ at hcompare
  have h₁ := relativeDistance_triangle decoded (corrected ρ ζ H) received
  rw [relativeDistance_comm decoded (corrected ρ ζ H)] at h₁
  have h₂ := relativeDistance_triangle decoded received field
  rw [hhalf] at h₂
  change PointLineTest.rejectionRate g T ≤ lineErrorConstant c * κ
  dsimp only [lineErrorConstant]
  change PointLineTest.rejectionRate g T ≤ 2 * ((c + 1 : ℕ) * K + 29) * κ
  nlinarith

omit [DecidableEq F] in
/-- Theorem 4.1 at inflated outer degree `c*m^c`, for the actual tester and arbitrary
auxiliary answers. The only rejection restriction is the explicit final threshold.
The second distance is over homogeneous degree-one labels, not all affine ones. -/
theorem exists_close
    (hq : PointLineConstants.fieldFactor * (c * m ^ c) ^ 3 ≤ Fintype.card F)
    (hr : 1 ≤ r) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (f : (σ → F) → Coefficients t r → ZMod 2) (H : Auxiliary F σ m c t)
    (hsmall : lineErrorConstant c * rejectionRate hr ρ nodes ζ f H ≤
      PointLineConstants.smallError) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ c * m ^ c ∧
      relativeDistance (fun p : (σ → F) × Coefficients t r => f p.1 p.2)
        (encodeFunction r (fun x => ρ (MvPolynomial.eval x P))) ≤
          soundnessConstant c * rejectionRate hr ρ nodes ζ f H ∧
      BinaryLagrangeConstraint.homogeneousDistance hr f
        (fun x => encode r (ρ (MvPolynomial.eval x P))) ≤
          soundnessConstant c * rejectionRate hr ρ nodes ζ f H := by
  classical
  have hdegree : c ≤ c * m ^ c := Nat.le_mul_of_pos_right c (pow_pos (NeZero.pos m) c)
  have hinner := (Nat.mul_le_mul_left 2 hdegree).trans_lt
    (PointLineConstants.field_bound_linear (Fintype.one_lt_card (α := F)) hq)
  obtain ⟨g, T, hfull, hhom, hline⟩ := exists_decoded_table hinner hr ρ hnodes hζ f H
  obtain ⟨P, hP, hclose⟩ := PointLineTest.exists_close_of_small_rejection hq g T
    (hline.trans hsmall)
  refine ⟨P, hP, ?_, ?_⟩
  · have ht := relativeDistance_triangle
      (fun p : (σ → F) × Coefficients t r => f p.1 p.2)
      (encodeFunction r (fun x => ρ (g x)))
      (encodeFunction r (fun x => ρ (MvPolynomial.eval x P)))
    rw [relativeDistance_encodeFunction_map ρ ρ.injective hr] at ht
    unfold soundnessConstant
    linarith
  · have ht := BinaryLagrangeConstraint.homogeneousDistance_triangle hr f
      (fun x => encode r (ρ (g x))) (fun x => encode r (ρ (MvPolynomial.eval x P)))
    rw [BinaryLagrangeConstraint.homogeneousDistance_encode] at ht
    unfold soundnessConstant
    linarith

end PCP.Algebraic.EncodedLineLowDegreeTest
