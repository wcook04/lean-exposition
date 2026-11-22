/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryZeroOnGridCorrection
import PCP.Algebraic.BinaryLocalCorrectionSoundness
import PCP.Algebraic.PointedLineSampling
import PCP.Algebraic.HadamardHomogeneousDistance

/-!
# Averaged soundness of the corrected grid check

The two certificate targets can have different rejection probabilities. Each
pointwise correction guarantee is averaged at its actual target, and every
correction abort forces the grid checker to reject. Thus the final coefficient
charges the actual grid rejection, without asserting a pointwise bound by that
global average.
-/

namespace PCP.Algebraic.BinaryZeroOnGridCorrection

open Finset MvPolynomial BinaryPolynomialSpace Hadamard BinaryZeroOnGrid
open AffineLineSampling PointedLineSampling
open scoped BigOperators

section Sampling

variable {X W S A : Type*} [Fintype X] [Fintype W] [Fintype S] [Nonempty S]

private theorem expect_pair {U V : Type*} [Fintype U] [Fintype V] (f : U × V → ℚ) :
    (𝔼 uv, f uv) = 𝔼 u, 𝔼 v, f (u, v) := by
  simpa only [univ_product_univ] using expect_product univ univ f

private theorem expect_shared_fst (f : W × S → ℚ) :
    (𝔼 s : W × (S × S), f (s.1, s.2.1)) = 𝔼 s, f s := by
  simp only [expect_pair, Fintype.expect_const]

private theorem expect_shared_snd (f : W × S → ℚ) :
    (𝔼 s : W × (S × S), f (s.1, s.2.2)) = 𝔼 s, f s := by
  simp only [expect_pair, Fintype.expect_const]

private theorem fraction_prod (E : X × W → Prop) :
    fraction E = 𝔼 x, fraction (fun w => E (x, w)) := by
  classical
  simp only [fraction_eq_expect, expect_pair]

private theorem fraction_shared_fst (E : W × S → Prop) :
    fraction (fun s : W × (S × S) => E (s.1, s.2.1)) = fraction E := by
  classical
  simpa only [fraction_eq_expect] using
    expect_shared_fst (fun s => if E s then (1 : ℚ) else 0)

private theorem fraction_shared_snd (E : W × S → Prop) :
    fraction (fun s : W × (S × S) => E (s.1, s.2.2)) = fraction E := by
  classical
  simpa only [fraction_eq_expect] using
    expect_shared_snd (fun s => if E s then (1 : ℚ) else 0)

variable [DecidableEq A]

private theorem distance_shared_fst (f g : W × S → A) :
    relativeDistance (fun s : W × (S × S) => f (s.1, s.2.1))
      (fun s => g (s.1, s.2.1)) = relativeDistance f g := by
  simpa only [fraction_ne_eq_relativeDistance] using
    fraction_shared_fst (fun s => f s ≠ g s)

private theorem distance_shared_snd (f g : W × S → A) :
    relativeDistance (fun s : W × (S × S) => f (s.1, s.2.2))
      (fun s => g (s.1, s.2.2)) = relativeDistance f g := by
  simpa only [fraction_ne_eq_relativeDistance] using
    fraction_shared_snd (fun s => f s ≠ g s)

/-- The common label keeps its uniform marginal when the two independent call seeds are added. -/
theorem distance_lift_labels (f g : X × W → A) :
    relativeDistance (fun s : X × (W × (S × S)) => f (s.1, s.2.1))
      (fun s => g (s.1, s.2.1)) = relativeDistance f g := by
  have he := relativeDistance_comp_equiv (Equiv.prodAssoc X W (S × S))
    (fun s : X × (W × (S × S)) => f (s.1, s.2.1))
    (fun s => g (s.1, s.2.1))
  simp only [Equiv.prodAssoc_apply] at he
  rw [relativeDistance_comp_fst (κ := S × S) f g] at he
  exact he.symm

end Sampling

section Generic

variable {X W S : Type*} [Fintype X] [Nonempty X] [Fintype W]
variable [Fintype S] [Nonempty S]

/-- One direct bit and two independently seeded optional bits, with a shared label. -/
def twoCallCheck (p : X → W → ZMod 2) (a b : X → W → S → Option (ZMod 2))
    (s : X × (W × (S × S))) : Option (ZMod 2 × ZMod 2) :=
  optionCheck (some (p s.1 s.2.1)) (a s.1 s.2.1 s.2.2.1) (b s.1 s.2.1 s.2.2.2)

/-- An averaged rejection guarantee follows from genuine per-target corrector bounds. -/
theorem two_corrector_rejection_bound
    (p P A B : X → W → ZMod 2) (a b : X → W → S → Option (ZMod 2))
    {K ν ε : ℚ} (hK : 0 ≤ K)
    (ha : ∀ x, relativeDistance (fun ws : W × S => a x ws.1 ws.2)
      (fun ws => some (A x ws.1)) ≤
        K * fraction (fun ws : W × S => a x ws.1 ws.2 = none) + ν)
    (hb : ∀ x, relativeDistance (fun ws : W × S => b x ws.1 ws.2)
      (fun ws => some (B x ws.1)) ≤
        K * fraction (fun ws : W × S => b x ws.1 ws.2 = none) + ν)
    (hp : relativeDistance (fun xw : X × W => p xw.1 xw.2)
      (fun xw => P xw.1 xw.2) ≤ ε) :
    relativeDistance (fun xw : X × W => checkBits (P xw.1 xw.2) (A xw.1 xw.2)
      (B xw.1 xw.2)) (fun _ => (0, 0)) ≤
        (1 + 2 * K) * relativeDistance (twoCallCheck p a b) (fun _ => some (0, 0)) + ε +
          2 * ν := by
  have habort (s : X × (W × (S × S)))
      (h : a s.1 s.2.1 s.2.2.1 = none ∨ b s.1 s.2.1 s.2.2.2 = none) :
      twoCallCheck p a b s ≠ some (0, 0) := by
    rcases h with h | h
    · simp [twoCallCheck, optionCheck, h]
    · simp only [twoCallCheck, h]
      cases a s.1 s.2.1 s.2.2.1 <;> simp [optionCheck]
  have haabort : (𝔼 x, fraction (fun ws : W × S => a x ws.1 ws.2 = none)) ≤
      relativeDistance (twoCallCheck p a b) (fun _ => some (0, 0)) := by
    have he : fraction (fun s : X × (W × (S × S)) => a s.1 s.2.1 s.2.2.1 = none) =
        𝔼 x, fraction (fun ws : W × S => a x ws.1 ws.2 = none) := by
      rw [fraction_prod]
      apply expect_congr rfl
      intro x _
      exact fraction_shared_fst (fun ws : W × S => a x ws.1 ws.2 = none)
    rw [← he, ← fraction_ne_eq_relativeDistance]
    exact fraction_mono _ _ (fun s hs => habort s (Or.inl hs))
  have habortb : (𝔼 x, fraction (fun ws : W × S => b x ws.1 ws.2 = none)) ≤
      relativeDistance (twoCallCheck p a b) (fun _ => some (0, 0)) := by
    have he : fraction (fun s : X × (W × (S × S)) => b s.1 s.2.1 s.2.2.2 = none) =
        𝔼 x, fraction (fun ws : W × S => b x ws.1 ws.2 = none) := by
      rw [fraction_prod]
      apply expect_congr rfl
      intro x _
      exact fraction_shared_snd (fun ws : W × S => b x ws.1 ws.2 = none)
    rw [← he, ← fraction_ne_eq_relativeDistance]
    exact fraction_mono _ _ (fun s hs => habort s (Or.inr hs))
  have hfa : relativeDistance
      (fun s : X × (W × (S × S)) => a s.1 s.2.1 s.2.2.1)
      (fun s => some (A s.1 s.2.1)) ≤
        K * relativeDistance (twoCallCheck p a b) (fun _ => some (0, 0)) + ν := by
    have he : relativeDistance
        (fun s : X × (W × (S × S)) => a s.1 s.2.1 s.2.2.1)
        (fun s => some (A s.1 s.2.1)) =
          𝔼 x, relativeDistance (fun ws : W × S => a x ws.1 ws.2)
            (fun ws => some (A x ws.1)) := by
      rw [relativeDistance_prod, Fintype.expect_eq_sum_div_card]
      congr 1
      apply sum_congr rfl
      intro x _
      exact distance_shared_fst (fun ws : W × S => a x ws.1 ws.2)
        (fun ws => some (A x ws.1))
    rw [he]
    have hm := expect_le_expect (s := univ) (fun x _ => ha x)
    rw [expect_add_distrib, ← mul_expect, Fintype.expect_const] at hm
    exact hm.trans (add_le_add (mul_le_mul_of_nonneg_left haabort hK) le_rfl)
  have hfb : relativeDistance
      (fun s : X × (W × (S × S)) => b s.1 s.2.1 s.2.2.2)
      (fun s => some (B s.1 s.2.1)) ≤
        K * relativeDistance (twoCallCheck p a b) (fun _ => some (0, 0)) + ν := by
    have he : relativeDistance
        (fun s : X × (W × (S × S)) => b s.1 s.2.1 s.2.2.2)
        (fun s => some (B s.1 s.2.1)) =
          𝔼 x, relativeDistance (fun ws : W × S => b x ws.1 ws.2)
            (fun ws => some (B x ws.1)) := by
      rw [relativeDistance_prod, Fintype.expect_eq_sum_div_card]
      congr 1
      apply sum_congr rfl
      intro x _
      exact distance_shared_snd (fun ws : W × S => b x ws.1 ws.2)
        (fun ws => some (B x ws.1))
    rw [he]
    have hm := expect_le_expect (s := univ) (fun x _ => hb x)
    rw [expect_add_distrib, ← mul_expect, Fintype.expect_const] at hm
    exact hm.trans (add_le_add (mul_le_mul_of_nonneg_left habortb hK) le_rfl)
  have hfp : relativeDistance
      (fun s : X × (W × (S × S)) => some (p s.1 s.2.1))
      (fun s => some (P s.1 s.2.1)) ≤ ε := by
    rw [relativeDistance_map Option.some (Option.some_injective _)]
    rw [distance_lift_labels (S := S) (fun xw : X × W => p xw.1 xw.2)
      (fun xw => P xw.1 xw.2)]
    exact hp
  have hi := ideal_rejection_le_option_rejection_add_errors
    (fun s : X × (W × (S × S)) => P s.1 s.2.1)
    (fun s => A s.1 s.2.1) (fun s => B s.1 s.2.1)
    (fun s => some (p s.1 s.2.1))
    (fun s => a s.1 s.2.1 s.2.2.1) (fun s => b s.1 s.2.1 s.2.2.2)
  rw [distance_lift_labels (S := S)
    (fun xw : X × W => checkBits (P xw.1 xw.2) (A xw.1 xw.2) (B xw.1 xw.2))
    (fun _ => ((0, 0) : ZMod 2 × ZMod 2))] at hi
  change _ ≤ relativeDistance (twoCallCheck p a b) (fun _ => some (0, 0)) + _ + _ + _ at hi
  nlinarith

end Generic

section Concrete

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype F] [DecidableEq F]
variable [CharP F 2] {n m c t D : ℕ} [NeZero m]

local instance : Fintype (BinaryLocalCorrection.InnerPoint F m c) := inferInstance
local instance : Fintype (BinaryLocalCorrection.InnerSeed F m c t) := inferInstance
local instance : Fintype (CallSeed F (Fin n ⊕ Fin n) m c t) := inferInstance
local instance : Fintype (BinaryLocalCorrection.Sample F (Fin n ⊕ Fin n) m c t) :=
  inferInstance

/-- Reindexing the actual full corrector sample separates its uniform requested label. -/
theorem call_failure_le
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (M : MvPolynomial (Fin n ⊕ Fin n) F) (hM : M.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D)
    (M' : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A : CertificatePoint F n → BinaryLocalCorrection.RowOracle F m c t) {δ : ℚ}
    (hnear : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) M'
      (fun x => encode 1 (ρ (eval x M))) ≤ δ) (a : CertificatePoint F n) :
    relativeDistance
      (fun ws : (Fin t → ZMod 2) × CallSeed F (Fin n ⊕ Fin n) m c t =>
        call ρ nodes ζ M' A a ws.1 ws.2)
      (fun ws => some (linearEncode (ρ (eval a M)) ws.1)) ≤
      BinaryLocalCorrection.soundnessConstant c *
        fraction (fun ws : (Fin t → ZMod 2) × CallSeed F (Fin n ⊕ Fin n) m c t =>
          call ρ nodes ζ M' A a ws.1 ws.2 = none) + δ +
        (D : ℚ) / (2 * (Fintype.card F - 1 : ℕ)) := by
  have hd := relativeDistance_comp_equiv
    (callSampleEquiv (F := F) (σ := Fin n ⊕ Fin n) (m := m) (c := c) (t := t))
    (BinaryLocalCorrection.sample ρ nodes ζ M' A a)
    (fun s : BinaryLocalCorrection.Sample F (Fin n ⊕ Fin n) m c t =>
      some (linearEncode (ρ (eval a M)) s.2.2.1.2))
  have ha : fraction
      (fun ws : (Fin t → ZMod 2) × CallSeed F (Fin n ⊕ Fin n) m c t =>
        call ρ nodes ζ M' A a ws.1 ws.2 = none) =
      BinaryLocalCorrection.rejectionRate ρ nodes ζ M' A a := by
    unfold BinaryLocalCorrection.rejectionRate fraction
    exact Fintype.expect_equiv
      (callSampleEquiv (F := F) (σ := Fin n ⊕ Fin n) (m := m) (c := c) (t := t))
      _ _ (fun _ => rfl)
  rw [ha]
  simpa only [callSampleEquiv, Equiv.coe_fn_mk, call, BinaryLocalCorrection.sample] using
    hd.trans_le (BinaryLocalCorrection.failure_le hq ρ hnodes hζ M hM hdecode M' A hnear a)

/-- Soundness of the actual two-corrector grid verifier against nearby polynomial encodings.
Both proximity hypotheses are global homogeneous-query distances.
The auxiliary proof is arbitrary. -/
theorem rejectionRate_lower_bound
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F) (hH : H.Nonempty)
    (P : MvPolynomial (Fin n) F) (M : MvPolynomial (Fin n ⊕ Fin n) F)
    (hP : P.totalDegree ≤ D) (hM : M.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D) (hnot : ¬ GridVanishing.VanishesOn H P)
    (p' : (Fin n → F) → Coefficients t 1 → ZMod 2)
    (M' : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A : Auxiliary F n m c t) {δP δM : ℚ}
    (hp : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) p'
      (fun x => encode 1 (ρ (eval x P))) ≤ δP)
    (hm : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) M'
      (fun x => encode 1 (ρ (eval x M))) ≤ δM) :
    (1 - ((D * H.card : ℕ) : ℚ) / Fintype.card F) / 2 ≤
      (1 + 2 * BinaryLocalCorrection.soundnessConstant c) *
        rejectionRate ρ nodes ζ H p' M' A + δP + 2 * δM +
          (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have hf (a : CertificatePoint F n) :=
    call_failure_le hq ρ hnodes hζ M hM hdecode M' (A a) hm a
  have hgeneric := two_corrector_rejection_bound
    (fun x w => p' x (homogeneousIndex (le_refl 1) w))
    (fun x w => linearEncode (ρ (eval x P)) w)
    (fun x w => linearEncode (ρ (eval (zeroPoint x) M)) w)
    (fun x w => linearEncode (ρ (eval (recoveryPoint H x) M)) w)
    (fun x w s => call ρ nodes ζ M' (A (zeroPoint x)) (zeroPoint x) w s)
    (fun x w s => call ρ nodes ζ M' (A (recoveryPoint H x)) (recoveryPoint H x) w s)
    (ν := δM + (D : ℚ) / (2 * (Fintype.card F - 1 : ℕ)))
    (BinaryLocalCorrection.soundnessConstant_nonneg c)
    (fun x => by simpa only [add_assoc] using hf (zeroPoint x))
    (fun x => by simpa only [add_assoc] using hf (recoveryPoint H x))
    (by simpa only [BinaryLagrangeConstraint.homogeneousDistance, encode_homogeneousIndex] using hp)
  have hi := BinaryZeroOnGrid.rejectionRate_encode_ge_of_not_vanishesOn (r := 1)
    (le_refl 1) ρ H hH P M hP hM hnot
  have hid : relativeDistance
      (fun xw : (Fin n → F) × (Fin t → ZMod 2) =>
        checkBits (linearEncode (ρ (eval xw.1 P)) xw.2)
          (linearEncode (ρ (eval (zeroPoint xw.1) M)) xw.2)
          (linearEncode (ρ (eval (recoveryPoint H xw.1) M)) xw.2)) (fun _ => (0, 0)) =
      BinaryZeroOnGrid.rejectionRate (le_refl 1) H (fun x => encode 1 (ρ (eval x P)))
        (fun x => encode 1 (ρ (eval x M))) := by
    simp only [BinaryZeroOnGrid.rejectionRate, BinaryZeroOnGrid.check, encode_homogeneousIndex]
  rw [hid] at hgeneric
  change _ ≤ (1 + 2 * BinaryLocalCorrection.soundnessConstant c) *
    rejectionRate ρ nodes ζ H p' M' A + δP +
      2 * (δM + (D : ℚ) / (2 * (Fintype.card F - 1 : ℕ))) at hgeneric
  have hterm : 2 * ((D : ℚ) / (2 * (Fintype.card F - 1 : ℕ))) =
      (D : ℚ) / (Fintype.card F - 1 : ℕ) := by ring
  linarith

/-- An explicit rejection lower bound, with a provably positive denominator. -/
theorem rejectionRate_ge
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F) (hH : H.Nonempty)
    (P : MvPolynomial (Fin n) F) (M : MvPolynomial (Fin n ⊕ Fin n) F)
    (hP : P.totalDegree ≤ D) (hM : M.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D) (hnot : ¬ GridVanishing.VanishesOn H P)
    (p' : (Fin n → F) → Coefficients t 1 → ZMod 2)
    (M' : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A : Auxiliary F n m c t) {δP δM : ℚ}
    (hp : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) p'
      (fun x => encode 1 (ρ (eval x P))) ≤ δP)
    (hm : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) M'
      (fun x => encode 1 (ρ (eval x M))) ≤ δM) :
    ((1 - ((D * H.card : ℕ) : ℚ) / Fintype.card F) / 2 - δP - 2 * δM -
      (D : ℚ) / (Fintype.card F - 1 : ℕ)) /
        (1 + 2 * BinaryLocalCorrection.soundnessConstant c) ≤
          rejectionRate ρ nodes ζ H p' M' A := by
  have hden : 0 < 1 + 2 * BinaryLocalCorrection.soundnessConstant c := by
    have h := BinaryLocalCorrection.soundnessConstant_nonneg c
    linarith
  apply (div_le_iff₀ hden).mpr
  have h := rejectionRate_lower_bound hq ρ hnodes hζ H hH P M hP hM hdecode hnot p' M' A hp hm
  nlinarith

/-- Source-style full coefficient-space proximity costs at most a factor two per oracle. -/
theorem rejectionRate_lower_bound_of_full_distance
    (hq : 2 * c < Fintype.card F)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    {nodes : Fin (c + 1) → F} (hnodes : GeneratorLowDegreeTest.IsGeneratorNodes nodes)
    {ζ : F} (hζ : StandardLocalCorrection.GoodNodes c ζ) (H : Finset F) (hH : H.Nonempty)
    (P : MvPolynomial (Fin n) F) (M : MvPolynomial (Fin n ⊕ Fin n) F)
    (hP : P.totalDegree ≤ D) (hM : M.totalDegree ≤ D)
    (hdecode : c * m ^ c ≤ D) (hnot : ¬ GridVanishing.VanishesOn H P)
    (p' : (Fin n → F) → Coefficients t 1 → ZMod 2)
    (M' : CertificatePoint F n → Coefficients t 1 → ZMod 2)
    (A : Auxiliary F n m c t) {δP δM : ℚ}
    (hp : relativeDistance (fun s : (Fin n → F) × Coefficients t 1 => p' s.1 s.2)
      (fun s => encode 1 (ρ (eval s.1 P)) s.2) ≤ δP)
    (hm : relativeDistance (fun s : CertificatePoint F n × Coefficients t 1 => M' s.1 s.2)
      (fun s => encode 1 (ρ (eval s.1 M)) s.2) ≤ δM) :
    (1 - ((D * H.card : ℕ) : ℚ) / Fintype.card F) / 2 ≤
      (1 + 2 * BinaryLocalCorrection.soundnessConstant c) *
        rejectionRate ρ nodes ζ H p' M' A + 2 * δP + 4 * δM +
          (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have hp' : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) p'
      (fun x => encode 1 (ρ (eval x P))) ≤ 2 * δP :=
    (relativeDistance_homogeneous_le_twice_full p' (fun x => encode 1 (ρ (eval x P)))).trans
      (mul_le_mul_of_nonneg_left hp (by norm_num))
  have hm' : BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) M'
      (fun x => encode 1 (ρ (eval x M))) ≤ 2 * δM :=
    (relativeDistance_homogeneous_le_twice_full M' (fun x => encode 1 (ρ (eval x M)))).trans
      (mul_le_mul_of_nonneg_left hm (by norm_num))
  have h := rejectionRate_lower_bound hq ρ hnodes hζ H hH P M hP hM hdecode hnot p' M' A hp' hm'
  linarith

end Concrete
end PCP.Algebraic.BinaryZeroOnGridCorrection
