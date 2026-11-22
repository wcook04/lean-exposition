/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Hadamard
import PCP.Algebraic.PolynomialLine
import PCP.Algebraic.AffineSampling
import PCP.Algebraic.PointedLineSampling
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Polynomial.Roots

/-!
# Local correction from arbitrary polynomial line tables

At a fixed point `a`, sample every direction uniformly, including zero, and
sample a nonzero parameter uniformly as an element of `Fˣ`. A table row whose
value at zero is wrong differs formally from the honest restriction. The root
bound therefore limits agreement to `D` of the `|F|-1` sampled parameters.

All claims are normalized rational probabilities for the actual finite samples.
The table is arbitrary except for its ordinary univariate degree bound; neither
coherence between rows nor low-degree-test soundness is assumed.
-/

namespace PCP.Algebraic.LineTableLocalCorrection

open Finset PolynomialLine AffineLineSampling
open scoped BigOperators

section Units

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {D : ℕ}

/-- Distinct bounded-degree polynomials agree on at most `D` nonzero parameters. -/
theorem agreement_on_units_le (p q : Polynomial F) (hp : p.natDegree ≤ D)
    (hq : q.natDegree ≤ D) (hne : p ≠ q) :
    relativeAgreement (fun l : Fˣ => p.eval (l : F)) (fun l => q.eval (l : F)) ≤
      (D : ℚ) / Fintype.card Fˣ := by
  classical
  have hcount : (univ.filter (fun l : Fˣ => p.eval (l : F) = q.eval (l : F))).card ≤ D := by
    by_contra hbad
    let S := univ.filter (fun l : Fˣ => p.eval (l : F) = q.eval (l : F))
    have hlarge : D < S.card := Nat.lt_of_not_ge hbad
    apply hne
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q
      (f := fun l : S => (l.val : F)) (Units.val_injective.comp Subtype.val_injective)
    · intro l
      exact (mem_filter.mp l.property).2
    · simpa only [Fintype.card_coe] using (max_le hp hq).trans_lt hlarge
  unfold relativeAgreement
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hcount) (Nat.cast_nonneg _)

/-- Nonzero-parameter disagreement has the usual polynomial-distance lower bound. -/
theorem distance_on_units_ge (p q : Polynomial F) (hp : p.natDegree ≤ D)
    (hq : q.natDegree ≤ D) (hne : p ≠ q) :
    1 - (D : ℚ) / Fintype.card Fˣ ≤
      relativeDistance (fun l : Fˣ => p.eval (l : F)) (fun l => q.eval (l : F)) := by
  have h := agreement_on_units_le p q hp hq hne
  rw [relativeAgreement_eq_one_sub_relativeDistance] at h
  linarith

end Units

section LineTable

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype σ] [DecidableEq σ] {D : ℕ}

omit [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ] in
/-- Wrong origin values imply a formal discrepancy with the honest restricted polynomial. -/
theorem table_ne_restrict_of_origin_ne (T : (σ → F) → Polynomial F)
    (P : MvPolynomial σ F) (a b : σ → F)
    (hne : (T b).eval 0 ≠ MvPolynomial.eval a P) : T b ≠ restrict a b P := by
  intro heq
  apply hne
  rw [heq, eval_restrict, point_zero]

/-- The multiplicative correction bound, valid even when `D ≥ |F|-1`.
The parameter and direction are sampled independently, and zero directions remain included. -/
theorem origin_error_mul_le (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) :
    (1 - (D : ℚ) / (Fintype.card F - 1 : ℕ)) *
      relativeDistance (fun b => (T b).eval 0) (fun _ => MvPolynomial.eval a P) ≤
    relativeDistance (fun s : (σ → F) × Fˣ => (T s.1).eval (s.2 : F))
      (fun s => MvPolynomial.eval (point a s.1 s.2) P) := by
  classical
  have hpoint (b : σ → F) :
      (1 - (D : ℚ) / Fintype.card Fˣ) *
        (if (T b).eval 0 ≠ MvPolynomial.eval a P then (1 : ℚ) else 0) ≤
      relativeDistance (fun l : Fˣ => (T b).eval (l : F))
        (fun l => MvPolynomial.eval (point a b l) P) := by
    split_ifs with hb
    · simp only [mul_one]
      simpa only [eval_restrict] using distance_on_units_ge (T b) (restrict a b P) (hT b)
        (natDegree_restrict_le_of_totalDegree_le a b P hP)
        (table_ne_restrict_of_origin_ne T P a b hb)
    · simp only [mul_zero]
      exact relativeDistance_nonneg _ _
  have h := expect_le_expect (s := univ) (fun b _ => hpoint b)
  rw [← mul_expect, ← fraction_eq_expect, fraction_ne_eq_relativeDistance,
    Fintype.expect_eq_sum_div_card] at h
  rw [relativeDistance_prod]
  simpa only [Fintype.card_units] using h

/-- Origin errors are bounded by sampled line-comparison errors plus `D/(|F|-1)`. -/
theorem origin_error_le (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) :
    relativeDistance (fun b => (T b).eval 0) (fun _ => MvPolynomial.eval a P) ≤
      relativeDistance (fun s : (σ → F) × Fˣ => (T s.1).eval (s.2 : F))
        (fun s => MvPolynomial.eval (point a s.1 s.2) P) +
      (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have h := origin_error_mul_le T hT P hP a
  have he := relativeDistance_le_one (fun b => (T b).eval 0) (fun _ => MvPolynomial.eval a P)
  have hτ : 0 ≤ (D : ℚ) / (Fintype.card F - 1 : ℕ) := by positivity
  nlinarith

/-- Every nonzero parameter sends a uniform direction to a uniform field point. -/
theorem affine_units_distance (a : σ → F) (f g : (σ → F) → F) :
    relativeDistance (fun s : (σ → F) × Fˣ => f (point a s.1 s.2))
      (fun s => g (point a s.1 s.2)) = relativeDistance f g := by
  rw [← relativeDistance_comp_equiv (Equiv.prodComm Fˣ (σ → F)), relativeDistance_prod]
  have hrow (l : Fˣ) :
      relativeDistance (fun b : σ → F => f (point a b l))
        (fun b => g (point a b l)) = relativeDistance f g :=
    relativeDistance_affineSampling a (l : F) l.ne_zero f g
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  simp only [hrow, sum_const, card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Comparing line rows with an imperfect oracle adds exactly its global error. -/
theorem origin_error_le_comparison_add_distance (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) (f : (σ → F) → F) :
    relativeDistance (fun b => (T b).eval 0) (fun _ => MvPolynomial.eval a P) ≤
      relativeDistance (fun s : (σ → F) × Fˣ => (T s.1).eval (s.2 : F))
        (fun s => f (point a s.1 s.2)) +
      relativeDistance f (fun x => MvPolynomial.eval x P) +
      (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have h := origin_error_le T hT P hP a
  have ht := relativeDistance_triangle (fun s : (σ → F) × Fˣ => (T s.1).eval (s.2 : F))
    (fun s => f (point a s.1 s.2)) (fun s => MvPolynomial.eval (point a s.1 s.2) P)
  rw [affine_units_distance a f (fun x => MvPolynomial.eval x P)] at ht
  linarith

/-- A wrong origin value can pass comparison with the honest polynomial on
at most `D/(|F|-1)` of the actual direction/parameter samples. -/
theorem accepted_wrong_honest_le (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) :
    fraction (fun s : (σ → F) × Fˣ =>
      (T s.1).eval (s.2 : F) = MvPolynomial.eval (point a s.1 s.2) P ∧
        (T s.1).eval 0 ≠ MvPolynomial.eval a P) ≤
      (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  classical
  rw [← Fintype.card_units, fraction_eq_expect, ← univ_product_univ, expect_product]
  apply expect_le univ_nonempty
  intro b _
  change (𝔼 l : Fˣ, if (T b).eval (l : F) = MvPolynomial.eval (point a b l) P ∧
    (T b).eval 0 ≠ MvPolynomial.eval a P then (1 : ℚ) else 0) ≤ _
  by_cases hb : (T b).eval 0 ≠ MvPolynomial.eval a P
  · simp_rw [and_iff_left hb]
    have h := agreement_on_units_le (T b) (restrict a b P) (hT b)
      (natDegree_restrict_le_of_totalDegree_le a b P hP)
      (table_ne_restrict_of_origin_ne T P a b hb)
    simpa only [hb, and_true, Fintype.expect_eq_sum_div_card, relativeAgreement,
      ← natCast_card_filter, eval_restrict] using h
  · simp only [hb, and_false, ↓reduceIte, Fintype.expect_const]
    positivity

end LineTable

section EventUnion

variable {I : Type*} [Fintype I]

/-- A two-event union bound for normalized finite fractions. -/
theorem fraction_le_add_of_imp_or (E B C : I → Prop)
    (h : ∀ i, E i → B i ∨ C i) : fraction E ≤ fraction B + fraction C := by
  classical
  simp only [fraction_eq_expect]
  rw [← expect_add_distrib]
  apply expect_le_expect
  intro i _
  by_cases he : E i
  · rcases h i he with hb | hc
    · simp only [he, hb, ↓reduceIte]
      split_ifs <;> norm_num
    · simp only [he, hc, ↓reduceIte]
      split_ifs <;> norm_num
  · simp only [he, ↓reduceIte]
    split_ifs <;> norm_num

end EventUnion

section NoisyComparison

variable {F σ : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype σ] [DecidableEq σ] {D : ℕ}

/-- The lines-table corrector accepts a wrong origin value with probability at
most the comparator's global error plus `D/(|F|-1)`. No small-error premise is needed. -/
theorem accepted_wrong_le (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) (f : (σ → F) → F) :
    fraction (fun s : (σ → F) × Fˣ =>
      (T s.1).eval (s.2 : F) = f (point a s.1 s.2) ∧
        (T s.1).eval 0 ≠ MvPolynomial.eval a P) ≤
      relativeDistance f (fun x => MvPolynomial.eval x P) +
        (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have h := fraction_le_add_of_imp_or
    (fun s : (σ → F) × Fˣ => (T s.1).eval (s.2 : F) = f (point a s.1 s.2) ∧
      (T s.1).eval 0 ≠ MvPolynomial.eval a P)
    (fun s : (σ → F) × Fˣ => f (point a s.1 s.2) ≠
      MvPolynomial.eval (point a s.1 s.2) P)
    (fun s : (σ → F) × Fˣ => (T s.1).eval (s.2 : F) =
      MvPolynomial.eval (point a s.1 s.2) P ∧ (T s.1).eval 0 ≠ MvPolynomial.eval a P) ?_
  · rw [fraction_ne_eq_relativeDistance,
      affine_units_distance a f (fun x => MvPolynomial.eval x P)] at h
    exact h.trans (add_le_add le_rfl (accepted_wrong_honest_le T hT P hP a))
  · intro s hs
    by_cases he : f (point a s.1 s.2) = MvPolynomial.eval (point a s.1 s.2) P
    · exact Or.inr ⟨hs.1.trans he, hs.2⟩
    · exact Or.inl he

end NoisyComparison

section Procedure

variable {F σ : Type*} [Field F]

/-- Compare one nonzero line sample, returning its proposed origin value on acceptance. -/
noncomputable def correct (T : (σ → F) → Polynomial F) (f : (σ → F) → F)
    (a b : σ → F) (z : Fˣ) : Option F := by
  classical
  exact if (T b).eval (z : F) = f (point a b z) then some ((T b).eval 0) else none

/-- The honest restricted table returns the requested value on every sample. -/
theorem correct_eval (P : MvPolynomial σ F) (a b : σ → F) (z : Fˣ) :
    correct (fun b => restrict a b P) (fun x => MvPolynomial.eval x P) a b z =
      some (MvPolynomial.eval a P) := by
  simp [correct, eval_restrict]

variable [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ] {D : ℕ}

/-- The actual field-valued procedure has the same accepted-wrong guarantee. -/
theorem correct_wrong_le (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) (f : (σ → F) → F) :
    fraction (fun s : (σ → F) × Fˣ => correct T f a s.1 s.2 ≠ none ∧
      correct T f a s.1 s.2 ≠ some (MvPolynomial.eval a P)) ≤
      relativeDistance f (fun x => MvPolynomial.eval x P) +
        (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have he (s : (σ → F) × Fˣ) :
      (correct T f a s.1 s.2 ≠ none ∧
        correct T f a s.1 s.2 ≠ some (MvPolynomial.eval a P)) ↔
      (T s.1).eval (s.2 : F) = f (point a s.1 s.2) ∧
        (T s.1).eval 0 ≠ MvPolynomial.eval a P := by
    by_cases h : (T s.1).eval (s.2 : F) = f (point a s.1 s.2)
    · simp [correct, h]
    · simp [correct, h]
  simp_rw [he]
  exact accepted_wrong_le T hT P hP a f

end Procedure

section LabeledSampling

variable {F σ W : Type*} [Field F]

/-- Preserve an independently sampled label while reindexing a nonzero affine sample. -/
def affineUnitsLabelEquiv (a : σ → F) :
    (((σ → F) × Fˣ) × W) ≃ (((σ → F) × W) × Fˣ) where
  toFun s := ((affineSamplingEquiv a (s.1.2 : F) s.1.2.ne_zero s.1.1, s.2), s.1.2)
  invFun s := (((affineSamplingEquiv a (s.2 : F) s.2.ne_zero).symm s.1.1, s.2), s.1.2)
  left_inv s := by simp
  right_inv s := by simp

/-- A label may be shared by both compared answers: affine sampling preserves
the complete point-and-label distance exactly. -/
theorem affine_units_label_distance [Fintype F] [DecidableEq F] [Fintype σ] [DecidableEq σ]
    [Fintype W] {K : Type*} [DecidableEq K]
    (a : σ → F) (f g : (σ → F) → W → K) :
    relativeDistance
        (fun s : ((σ → F) × Fˣ) × W => f (point a s.1.1 s.1.2) s.2)
        (fun s => g (point a s.1.1 s.1.2) s.2) =
      relativeDistance (fun s : (σ → F) × W => f s.1 s.2) (fun s => g s.1 s.2) := by
  calc
    _ = relativeDistance
        (fun s : ((σ → F) × W) × Fˣ => f s.1.1 s.1.2)
        (fun s => g s.1.1 s.1.2) :=
      relativeDistance_comp_equiv (affineUnitsLabelEquiv a) _ _
    _ = _ := relativeDistance_comp_fst (κ := Fˣ)
      (fun s : (σ → F) × W => f s.1 s.2) (fun s => g s.1 s.2)

end LabeledSampling

section BinaryProjection

open Hadamard

variable {F I : Type*} [DecidableEq F] [Fintype I] {t : ℕ}

/-- An injective binary representation and a uniform homogeneous label detect
exactly half of the field disagreements. -/
theorem homogeneous_distance_eq_half (ρ : F → Fin t → ZMod 2)
    (hρ : Function.Injective ρ) (f g : I → F) :
    relativeDistance (fun s : I × (Fin t → ZMod 2) => linearEncode (ρ (f s.1)) s.2)
      (fun s => linearEncode (ρ (g s.1)) s.2) = (1 : ℚ) / 2 * relativeDistance f g := by
  have h := relativeDistance_homogeneous_queries (r := 1) (le_refl 1)
    (fun i => ρ (f i)) (fun i => ρ (g i))
  simpa only [encode_homogeneousIndex, relativeDistance_map ρ hρ] using h

variable {σ : Type*} [Field F] [Fintype F] [Fintype σ] [DecidableEq σ] {D : ℕ}

/-- Binary line comparison controls field-valued origin error via the exact half-distance. -/
theorem origin_error_le_twice_binary_comparison (ρ : F → Fin t → ZMod 2)
    (hρ : Function.Injective ρ) (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) :
    relativeDistance (fun b => (T b).eval 0) (fun _ => MvPolynomial.eval a P) ≤
      2 * relativeDistance
        (fun s : ((σ → F) × Fˣ) × (Fin t → ZMod 2) =>
          linearEncode (ρ ((T s.1.1).eval (s.1.2 : F))) s.2)
        (fun s => linearEncode (ρ (MvPolynomial.eval (point a s.1.1 s.1.2) P)) s.2) +
      (D : ℚ) / (Fintype.card F - 1 : ℕ) := by
  have hhalf := homogeneous_distance_eq_half ρ hρ
    (fun s : (σ → F) × Fˣ => (T s.1).eval (s.2 : F))
    (fun s => MvPolynomial.eval (point a s.1 s.2) P)
  have h := origin_error_le T hT P hP a
  linarith

/-- With a homogeneous output label, binary origin error is bounded by binary
line-comparison error plus half the polynomial root-bound loss. -/
theorem binary_origin_error_le_binary_comparison (ρ : F → Fin t → ZMod 2)
    (hρ : Function.Injective ρ) (T : (σ → F) → Polynomial F)
    (hT : ∀ b, (T b).natDegree ≤ D) (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D)
    (a : σ → F) :
    relativeDistance
        (fun s : (σ → F) × (Fin t → ZMod 2) => linearEncode (ρ ((T s.1).eval 0)) s.2)
        (fun s => linearEncode (ρ (MvPolynomial.eval a P)) s.2) ≤
      relativeDistance
        (fun s : ((σ → F) × Fˣ) × (Fin t → ZMod 2) =>
          linearEncode (ρ ((T s.1.1).eval (s.1.2 : F))) s.2)
        (fun s => linearEncode (ρ (MvPolynomial.eval (point a s.1.1 s.1.2) P)) s.2) +
      ((D : ℚ) / (Fintype.card F - 1 : ℕ)) / 2 := by
  have hhalf := homogeneous_distance_eq_half ρ hρ
    (fun b : σ → F => (T b).eval 0) (fun _ => MvPolynomial.eval a P)
  have h := origin_error_le_twice_binary_comparison ρ hρ T hT P hP a
  linarith

/-- Arbitrary received homogeneous-bit answers can be used as the comparator.
Their actual global point-and-label error is added without an independence assumption. -/
theorem binary_origin_error_le_comparison_add_oracle_distance
    (ρ : F → Fin t → ZMod 2) (hρ : Function.Injective ρ)
    (T : (σ → F) → Polynomial F) (hT : ∀ b, (T b).natDegree ≤ D)
    (P : MvPolynomial σ F) (hP : P.totalDegree ≤ D) (a : σ → F)
    (H : (σ → F) → (Fin t → ZMod 2) → ZMod 2) :
    relativeDistance
        (fun s : (σ → F) × (Fin t → ZMod 2) => linearEncode (ρ ((T s.1).eval 0)) s.2)
        (fun s => linearEncode (ρ (MvPolynomial.eval a P)) s.2) ≤
      relativeDistance
        (fun s : ((σ → F) × Fˣ) × (Fin t → ZMod 2) =>
          linearEncode (ρ ((T s.1.1).eval (s.1.2 : F))) s.2)
        (fun s => H (point a s.1.1 s.1.2) s.2) +
      relativeDistance (fun s : (σ → F) × (Fin t → ZMod 2) => H s.1 s.2)
        (fun s => linearEncode (ρ (MvPolynomial.eval s.1 P)) s.2) +
      ((D : ℚ) / (Fintype.card F - 1 : ℕ)) / 2 := by
  have h := binary_origin_error_le_binary_comparison ρ hρ T hT P hP a
  have ht := relativeDistance_triangle
    (fun s : ((σ → F) × Fˣ) × (Fin t → ZMod 2) =>
      linearEncode (ρ ((T s.1.1).eval (s.1.2 : F))) s.2)
    (fun s => H (point a s.1.1 s.1.2) s.2)
    (fun s => linearEncode (ρ (MvPolynomial.eval (point a s.1.1 s.1.2) P)) s.2)
  rw [affine_units_label_distance a H (fun x w => linearEncode (ρ (MvPolynomial.eval x P)) w)] at ht
  linarith

end BinaryProjection

end PCP.Algebraic.LineTableLocalCorrection
