/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Hadamard
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Binary linearity testing

Finite rational Walsh analysis for the sharp Blum–Luby–Rubinfeld linearity
bound (Theorem B.1). All averages are uniform finite averages.
-/

namespace PCP.Algebraic.BLR

open Finset

/-- The real-valued sign of a binary value, kept in `ℚ`. -/
def sign (b : ZMod 2) : ℚ := if b = 0 then 1 else -1

private theorem binary_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  obtain rfl | rfl := binary_cases a <;> obtain rfl | rfl := binary_cases b
  · simp
  · simp
  · simp
  · change sign 0 = (-1 : ℚ) * -1
    norm_num

@[simp] theorem sign_sq (a : ZMod 2) : sign a ^ 2 = 1 := by
  obtain rfl | rfl := binary_cases a <;> norm_num

theorem sign_mul_sign (a b : ZMod 2) :
    sign a * sign b = if a = b then 1 else -1 := by
  obtain rfl | rfl := binary_cases a <;> obtain rfl | rfl := binary_cases b <;> norm_num

/-- A uniform finite average; the empty-domain average is zero. -/
def average {α : Type*} [Fintype α] (f : α → ℚ) : ℚ :=
  (∑ x, f x) / Fintype.card α

theorem average_add {α : Type*} [Fintype α] (f g : α → ℚ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, sum_add_distrib, add_div]

theorem average_mul_left {α : Type*} [Fintype α] (c : ℚ) (f : α → ℚ) :
    average (fun x => c * f x) = c * average f := by
  unfold average
  rw [← mul_sum, mul_div_assoc]

theorem average_mul_right {α : Type*} [Fintype α] (c : ℚ) (f : α → ℚ) :
    average (fun x => f x * c) = average f * c := by
  simpa [mul_comm] using average_mul_left c f

theorem average_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℚ) :
    average (fun x => ∑ y, f x y) = ∑ y, average (fun x => f x y) := by
  simp only [average, sum_div]
  exact sum_comm

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℚ) :
    average (fun x => average (f x)) = average (fun y => average (fun x => f x y)) := by
  simp only [average, ← sum_div, div_div]
  rw [sum_comm, mul_comm (Fintype.card β : ℚ)]

theorem average_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℚ) :
    average (fun x => average (fun y => f (x, y))) = average f := by
  simp only [average, ← sum_div, div_div, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type]
  rw [mul_comm (Fintype.card β : ℚ)]

theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℚ) : average (fun x => f (e x)) = average f := by
  simp only [average, Fintype.card_congr e, Equiv.sum_comp e]

@[simp] theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℚ) :
    average (fun _ : α => c) = c := by
  simp [average, Fintype.card_ne_zero]

theorem average_sign_mul {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → ZMod 2) :
    average (fun x => sign (f x) * sign (g x)) = 1 - 2 * relativeDistance f g := by
  classical
  simp only [sign_mul_sign, average, relativeDistance, hammingDist]
  have hsum : (∑ x : α, if f x = g x then (1 : ℚ) else -1) =
      Fintype.card α - 2 * #{x | f x ≠ g x} := by
    calc
      _ = ∑ x : α, (1 - 2 * if f x ≠ g x then (1 : ℚ) else 0) := by
        apply sum_congr rfl
        intro x _
        by_cases h : f x = g x <;> norm_num [h]
      _ = _ := by
        rw [sum_sub_distrib, ← mul_sum]
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, natCast_card_filter]
  rw [hsum]
  have hn : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Rejection probability of the binary three-query linearity test. -/
def rejectionProbability {V : Type*} [Fintype V] [Add V] (H : V → ZMod 2) : ℚ :=
  relativeDistance (fun p : V × V => H (p.1 + p.2)) (fun p => H p.1 + H p.2)

@[simp] theorem rejectionProbability_addHom {V : Type*} [Fintype V] [AddZeroClass V]
    (L : V →+ ZMod 2) : rejectionProbability L = 0 := by
  simp [rejectionProbability]

theorem rejection_bias {V : Type*} [Fintype V] [Nonempty V] [Add V]
    (H : V → ZMod 2) :
    average (fun x => average (fun y => sign (H x) * sign (H y) * sign (H (x + y)))) =
      1 - 2 * rejectionProbability H := by
  rw [average_prod (fun p : V × V => sign (H p.1) * sign (H p.2) * sign (H (p.1 + p.2)))]
  have h := average_sign_mul (fun p : V × V => H (p.1 + p.2))
    (fun p => H p.1 + H p.2)
  simpa only [sign_add, mul_comm _ (sign (H (_ + _))), rejectionProbability] using h

section Walsh

variable {ι : Type*} [Fintype ι]

/-- A homogeneous binary linear form indexed by its coefficients. -/
noncomputable def linearForm (a : ι → ZMod 2) : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i, a i • LinearMap.proj i

theorem linearForm_apply (a x : ι → ZMod 2) : linearForm a x = ∑ i, a i * x i := by
  simp [linearForm, smul_eq_mul]

theorem linearForm_comm (a x : ι → ZMod 2) : linearForm a x = linearForm x a := by
  simp only [linearForm_apply, mul_comm]

@[simp] theorem linearForm_single [DecidableEq ι] (a : ι → ZMod 2) (i : ι) :
    linearForm a (Pi.single i 1) = a i := by
  simp [linearForm_apply, Pi.single_apply]

/-- The rational Walsh character indexed by `a`. -/
noncomputable def character (a x : ι → ZMod 2) : ℚ := sign (linearForm a x)

theorem character_comm (a x : ι → ZMod 2) : character a x = character x a := by
  rw [character, character, linearForm_comm]

@[simp] theorem character_zero (a : ι → ZMod 2) : character a 0 = 1 := by
  simp [character]

theorem character_add (a x y : ι → ZMod 2) :
    character a (x + y) = character a x * character a y := by
  simp [character, sign_add]

@[simp] theorem character_sq (a x : ι → ZMod 2) : character a x ^ 2 = 1 := by
  exact sign_sq _

variable [DecidableEq ι]

theorem average_character (a : ι → ZMod 2) :
    average (character a) = if a = 0 then 1 else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    change average (fun x => sign (linearForm 0 x)) = if (0 : ι → ZMod 2) = 0 then 1 else 0
    simp [linearForm_apply]
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have hc := Hadamard.relativeDistance_addHom_zero (linearForm a).toAddMonoidHom
      (Pi.single i 1) (by simpa using hi)
    change relativeDistance (linearForm a) 0 = (1 : ℚ) / 2 at hc
    have hs := average_sign_mul (linearForm a) (0 : (ι → ZMod 2) → ZMod 2)
    change average (fun x => sign (linearForm a x)) = 0
    simpa [hc] using hs

theorem average_character_mul (x y : ι → ZMod 2) :
    average (fun a => character a x * character a y) = if x = y then 1 else 0 := by
  have hz : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      have hchar : y i + y i = 0 := by
        obtain h | h := binary_cases (y i) <;> rw [h] <;> rfl
      exact add_right_cancel (hi.trans hchar.symm)
    · rintro rfl
      funext i
      obtain h | h := binary_cases (x i) <;> rw [Pi.add_apply, Pi.zero_apply, h] <;> rfl
  simp_rw [← character_add, character_comm _ (x + y)]
  simpa only [hz] using average_character (x + y)

/-- Normalized rational Walsh coefficient. -/
noncomputable def fourier (f : (ι → ZMod 2) → ℚ) (a : ι → ZMod 2) : ℚ :=
  average (fun x => f x * character a x)

theorem inversion (f : (ι → ZMod 2) → ℚ) (x : ι → ZMod 2) :
    (∑ a, fourier f a * character a x) = f x := by
  classical
  simp only [fourier, average, div_mul_eq_mul_div, ← sum_div]
  simp_rw [sum_mul]
  rw [sum_comm]
  simp_rw [mul_assoc, ← mul_sum]
  have horth (y : ι → ZMod 2) :
      (∑ a, character a y * character a x) =
        (Fintype.card (ι → ZMod 2) : ℚ) * if y = x then 1 else 0 := by
    have h := average_character_mul y x
    unfold average at h
    exact (div_eq_iff (by exact_mod_cast Fintype.card_ne_zero)).mp h |>.trans (mul_comm _ _)
  simp_rw [horth]
  simp [mul_ite]

/-- The Walsh basis is orthonormal for the uniform average. -/
theorem pairing (f g : (ι → ZMod 2) → ℚ) :
    (∑ a, fourier f a * fourier g a) = average (fun x => f x * g x) := by
  calc
    _ = ∑ a, average (fun x => fourier f a * (g x * character a x)) := by
      simp only [average_mul_left, fourier]
    _ = average (fun x => ∑ a, fourier f a * (g x * character a x)) :=
      (average_sum _).symm
    _ = average (fun x => (∑ a, fourier f a * character a x) * g x) := by
      congr 1
      funext x
      simp only [sum_mul]
      apply sum_congr rfl
      intro a _
      ring
    _ = _ := by simp only [inversion]

/-- Parseval's identity, with normalized coefficients and an unnormalized dual sum. -/
theorem parseval (f : (ι → ZMod 2) → ℚ) :
    (∑ a, fourier f a ^ 2) = average (fun x => f x ^ 2) := by
  simpa only [pow_two] using pairing f f

theorem fourier_translate (f : (ι → ZMod 2) → ℚ) (x a : ι → ZMod 2) :
    fourier (fun y => f (x + y)) a = fourier f a * character a x := by
  calc
    _ = average (fun y => (f (x + y) * character a (x + y)) * character a x) := by
      unfold fourier
      congr 1
      funext y
      rw [character_add]
      calc
        _ = (f (x + y) * character a y) * character a x ^ 2 := by rw [character_sq, mul_one]
        _ = _ := by ring
    _ = average (fun y => f (x + y) * character a (x + y)) * character a x :=
      average_mul_right _ _
    _ = _ := by
      congr 1
      exact average_equiv (Equiv.addLeft x) (fun y => f y * character a y)

theorem autocorrelation (f : (ι → ZMod 2) → ℚ) (x : ι → ZMod 2) :
    average (fun y => f y * f (x + y)) =
      ∑ a, fourier f a ^ 2 * character a x := by
  rw [← pairing]
  simp only [fourier_translate]
  apply sum_congr rfl
  intro a _
  ring

/-- The acceptance bias of the three-query test is the third Fourier moment. -/
theorem cubic_identity (f : (ι → ZMod 2) → ℚ) :
    average (fun x => average (fun y => f x * f y * f (x + y))) =
      ∑ a, fourier f a ^ 3 := by
  calc
    _ = average (fun x => f x * average (fun y => f y * f (x + y))) := by
      simp only [mul_assoc, average_mul_left]
    _ = average (fun x => f x * ∑ a, fourier f a ^ 2 * character a x) := by
      simp only [autocorrelation]
    _ = ∑ a, average (fun x => fourier f a ^ 2 * (f x * character a x)) := by
      rw [← average_sum]
      congr 1
      funext x
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ = ∑ a, fourier f a ^ 2 * fourier f a := by
      simp only [average_mul_left, fourier]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      ring

/-- Some Walsh coefficient bounds the third moment whenever the energy is one. -/
theorem exists_coefficient_ge_cubic (f : (ι → ZMod 2) → ℚ)
    (hf : average (fun x => f x ^ 2) = 1) :
    ∃ a, (∑ b, fourier f b ^ 3) ≤ fourier f a := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image univ (fourier f) (by simp)
  refine ⟨a, ?_⟩
  calc
    _ ≤ ∑ b, fourier f a * fourier f b ^ 2 := by
      apply sum_le_sum
      intro b hb
      have h := mul_le_mul_of_nonneg_right (ha b hb) (sq_nonneg (fourier f b))
      nlinarith
    _ = fourier f a * ∑ b, fourier f b ^ 2 := (mul_sum _ _ _).symm
    _ = fourier f a := by rw [parseval, hf, mul_one]

/-- Correlation with a Walsh character is precisely the agreement bias. -/
theorem fourier_sign_distance (H : (ι → ZMod 2) → ZMod 2) (a : ι → ZMod 2) :
    fourier (fun x => sign (H x)) a = 1 - 2 * relativeDistance H (linearForm a) :=
  average_sign_mul H (linearForm a)

/-- Sharp BLR soundness: rejection probability bounds distance to a linear form. -/
theorem exists_linearForm_distance_le (H : (ι → ZMod 2) → ZMod 2) :
    ∃ a, relativeDistance H (linearForm a) ≤ rejectionProbability H := by
  obtain ⟨a, ha⟩ := exists_coefficient_ge_cubic (fun x => sign (H x)) (by simp)
  refine ⟨a, ?_⟩
  rw [← cubic_identity, rejection_bias, fourier_sign_distance] at ha
  linarith

/-- Theorem B.1, with the witness bundled as an actual binary linear map. -/
theorem exists_linearMap_distance_le (H : (ι → ZMod 2) → ZMod 2) :
    ∃ L : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      relativeDistance H L ≤ rejectionProbability H := by
  obtain ⟨a, ha⟩ := exists_linearForm_distance_le H
  exact ⟨linearForm a, ha⟩

/-- Soundness with an explicit upper bound on the rejection probability. -/
theorem exists_linearMap_distance_le_of_rejection_le (H : (ι → ZMod 2) → ZMod 2)
    {ε : ℚ} (hε : rejectionProbability H ≤ ε) :
    ∃ L : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2, relativeDistance H L ≤ ε := by
  obtain ⟨L, hL⟩ := exists_linearMap_distance_le H
  exact ⟨L, hL.trans hε⟩

end Walsh

end PCP.Algebraic.BLR
