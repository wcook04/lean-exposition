/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryPolynomialSpace

/-!
# Low-degree Hadamard encoding

A Definitions 3.5–3.6 and Observation 3.8. A Boolean vector is encoded by its
evaluations on all reduced polynomials of degree at most `r`, using the finite
coefficient coordinates of `BinaryPolynomialSpace`. Distinct vectors have distance
exactly one half when `r ≥ 1`. The field-element version composes with an injective
coordinate map; the paper fixes such a map using an `𝔽₂`-linear equivalence.
-/

namespace PCP.Algebraic.Hadamard

open Finset BinaryPolynomialSpace

variable {t r : ℕ}

/-- Definition 3.5, in Boolean coordinates. -/
noncomputable def encode (r : ℕ) (x : Fin t → ZMod 2) : Coefficients t r →ₗ[ZMod 2] ZMod 2 :=
  evaluate x

theorem encode_apply (x : Fin t → ZMod 2) (c : Coefficients t r) :
    encode r x c = MvPolynomial.eval x (polynomial t r c) := rfl

@[simp] theorem encode_variableCoeff (x : Fin t → ZMod 2) (hr : 1 ≤ r) (i : Fin t) :
    encode r x (variableCoeff hr i) = x i := evaluate_variableCoeff x hr i

@[simp] theorem encode_constant (x : Fin t → ZMod 2) (a : ZMod 2) :
    encode r x (constant (t := t) (r := r) a) = a := evaluate_constant x a

theorem encode_injective (hr : 1 ≤ r) : Function.Injective (encode (t := t) r) := by
  intro x y h
  funext i
  simpa using LinearMap.congr_fun h (variableCoeff hr i)

/-- Degree-zero queries see only constants, so they cannot distinguish messages. -/
theorem encode_degree_zero_eq (x y : Fin t → ZMod 2) : encode 0 x = encode 0 y := by
  apply LinearMap.ext
  intro c
  have hp := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    (Nat.eq_zero_of_le_zero (totalDegree_polynomial_le c))
  simp only [encode_apply]
  rw [hp, MvPolynomial.eval_C, MvPolynomial.eval_C]

private theorem add_nonzero_eq_zero_iff (a b : ZMod 2) (hb : b ≠ 0) :
    a + b = 0 ↔ a ≠ 0 := by
  have hcases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain rfl | rfl := hcases b
  · exact (hb rfl).elim
  · obtain rfl | rfl := hcases a
    · simp
    · exact iff_of_true rfl one_ne_zero

/-- Translation by a vector with nonzero image exchanges the two fibers of a binary homomorphism. -/
theorem two_mul_nonzero_count {V : Type*} [AddCommGroup V] [Fintype V]
    (L : V →+ ZMod 2) (e : V) (he : L e ≠ 0) :
    2 * #{v | L v ≠ 0} = Fintype.card V := by
  classical
  have hc : #{v | L v ≠ 0} = #{v | L v = 0} := by
    apply card_equiv (Equiv.addRight e)
    intro v
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, map_add]
    exact (add_nonzero_eq_zero_iff (L v) (L e) he).symm
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun v => L v = 0)
  rw [← hc] at hsum
  simpa [two_mul] using hsum

/-- A nonzero binary additive functional is one on exactly half the domain. -/
theorem relativeDistance_addHom_zero {V : Type*} [AddCommGroup V] [Fintype V]
    (L : V →+ ZMod 2) (e : V) (he : L e ≠ 0) : relativeDistance L 0 = (1 : ℚ) / 2 := by
  have hc : (2 : ℚ) * #{v | L v ≠ 0} = Fintype.card V := by
    exact_mod_cast two_mul_nonzero_count L e he
  have hpos : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [relativeDistance, hammingDist, Pi.zero_apply]
  apply (div_eq_iff hpos).mpr
  linarith

/-- Distinct messages have exactly one-half relative distance. -/
theorem relativeDistance_encode (hr : 1 ≤ r) (x y : Fin t → ZMod 2) (hxy : x ≠ y) :
    relativeDistance (encode r x) (encode r y) = (1 : ℚ) / 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  let L : Coefficients t r →+ ZMod 2 := (encode r x - encode r y).toAddMonoidHom
  have he : L (variableCoeff hr i) ≠ 0 := by
    simpa [L, sub_eq_zero] using hi
  have h := relativeDistance_addHom_zero L (variableCoeff hr i) he
  change relativeDistance (fun c => encode r x c - encode r y c) 0 = (1 : ℚ) / 2 at h
  simpa only [relativeDistance, hammingDist, Pi.zero_apply, sub_ne_zero] using h

/-- Equal messages give distance zero; distinct ones give distance one half. -/
theorem relativeDistance_encode_eq (hr : 1 ≤ r) (x y : Fin t → ZMod 2) :
    relativeDistance (encode r x) (encode r y) = if x = y then 0 else (1 : ℚ) / 2 := by
  classical
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy, relativeDistance_encode hr x y hxy]

/-- Definition 3.6: concatenate the encodings of a function's values. -/
noncomputable def encodeFunction {ι : Type*} (r : ℕ) (f : ι → Fin t → ZMod 2) :
    ι × Coefficients t r → ZMod 2 := fun p => encode r (f p.1) p.2

/-- Observation 3.8: concatenation halves the relative distance of two functions. -/
theorem relativeDistance_encodeFunction {ι : Type*} [Fintype ι] (hr : 1 ≤ r)
    (f g : ι → Fin t → ZMod 2) :
    relativeDistance (encodeFunction r f) (encodeFunction r g) =
      (1 : ℚ) / 2 * relativeDistance f g :=
  relativeDistance_concatenate (fun x => encode r x) ((1 : ℚ) / 2)
    (relativeDistance_encode_eq hr) f g

/-- The field-coordinate version, using only injectivity of the paper's coordinate map. -/
theorem relativeDistance_encodeFunction_map {ι α : Type*} [Fintype ι] [DecidableEq α]
    (ρ : α → Fin t → ZMod 2) (hρ : Function.Injective ρ) (hr : 1 ≤ r) (f g : ι → α) :
    relativeDistance (encodeFunction r (fun i => ρ (f i)))
      (encodeFunction r (fun i => ρ (g i))) = (1 : ℚ) / 2 * relativeDistance f g := by
  rw [relativeDistance_encodeFunction hr, relativeDistance_map ρ hρ]

/-- A received word cannot be within distance less than one quarter of two messages. -/
theorem eq_of_close (hr : 1 ≤ r) (x y : Fin t → ZMod 2)
    (w : Coefficients t r → ZMod 2) {ε : ℚ} (hε : ε < (1 : ℚ) / 4)
    (hx : relativeDistance w (encode r x) ≤ ε)
    (hy : relativeDistance w (encode r y) ≤ ε) : x = y := by
  by_contra hxy
  have hd := relativeDistance_encode hr x y hxy
  have ht := relativeDistance_triangle (encode r x) w (encode r y)
  rw [relativeDistance_comm (encode r x) w] at ht
  linarith

/-- Homogeneous linear forms, parametrized by their `t` binary coefficients. -/
noncomputable def linearEncode (x : Fin t → ZMod 2) :
    (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i, x i • LinearMap.proj i

theorem linearEncode_apply (x w : Fin t → ZMod 2) :
    linearEncode x w = ∑ i, x i * w i := by
  simp [linearEncode, smul_eq_mul]

@[simp] theorem linearEncode_single (x : Fin t → ZMod 2) (i : Fin t) :
    linearEncode x (Pi.single i 1) = x i := by
  simp [linearEncode_apply, Pi.single_apply]

/-- Embed a homogeneous linear query into the degree-`r` query space. -/
noncomputable def homogeneousIndex (hr : 1 ≤ r) :
    (Fin t → ZMod 2) →ₗ[ZMod 2] Coefficients t r :=
  ∑ i, (LinearMap.proj i).smulRight (variableCoeff hr i)

theorem polynomial_homogeneousIndex (hr : 1 ≤ r) (w : Fin t → ZMod 2) :
    polynomial t r (homogeneousIndex hr w) =
      ∑ i, MvPolynomial.C (w i) * MvPolynomial.X i := by
  simp [homogeneousIndex, MvPolynomial.smul_eq_C_mul]

@[simp] theorem encode_homogeneousIndex (hr : 1 ≤ r) (x w : Fin t → ZMod 2) :
    encode r x (homogeneousIndex hr w) = linearEncode x w := by
  simp [encode_apply, polynomial_homogeneousIndex, linearEncode_apply, mul_comm]

theorem homogeneousIndex_injective (hr : 1 ≤ r) :
    Function.Injective (homogeneousIndex (t := t) hr) := by
  intro w v h
  funext i
  have he := congrArg (encode r (Pi.single i 1)) h
  simp only [encode_homogeneousIndex, linearEncode_apply] at he
  simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
    ite_true] using he

/-- The homogeneous-linear variant of the element distance identity. -/
theorem relativeDistance_linearEncode (x y : Fin t → ZMod 2) (hxy : x ≠ y) :
    relativeDistance (linearEncode x) (linearEncode y) = (1 : ℚ) / 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  let L := (linearEncode x - linearEncode y).toAddMonoidHom
  have he : L (Pi.single i 1) ≠ 0 := by simpa [L, sub_eq_zero] using hi
  have h := relativeDistance_addHom_zero L (Pi.single i 1) he
  change relativeDistance (fun c => linearEncode x c - linearEncode y c) 0 = (1 : ℚ) / 2 at h
  simpa only [relativeDistance, hammingDist, Pi.zero_apply, sub_ne_zero] using h

/-- Observation 3.8's second identity, sampling homogeneous linear queries. -/
theorem relativeDistance_homogeneous_queries {ι : Type*} [Fintype ι] (hr : 1 ≤ r)
    (f g : ι → Fin t → ZMod 2) :
    relativeDistance
      (fun p : ι × (Fin t → ZMod 2) => encode r (f p.1) (homogeneousIndex hr p.2))
      (fun p => encode r (g p.1) (homogeneousIndex hr p.2)) =
      (1 : ℚ) / 2 * relativeDistance f g := by
  simp only [encode_homogeneousIndex]
  refine relativeDistance_concatenate (fun x => linearEncode x) ((1 : ℚ) / 2) ?_ f g
  intro x y
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy, relativeDistance_linearEncode x y hxy]

end PCP.Algebraic.Hadamard
