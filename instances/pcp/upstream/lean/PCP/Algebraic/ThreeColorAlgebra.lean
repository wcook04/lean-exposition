/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.CharP.Two
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Three colors as cubic roots of unity

The algebra in Observations 7.1 and 7.2. In characteristic two, the difference
of two distinct cubic roots of unity is another cubic root of unity. Consequently
the vertex and edge cubic equations together characterize proper three-coloring.
The vertex equations are essential, and not only for isolated vertices. If `F`
contains `GF(4)`, color `K₄` by its four elements. Each difference of distinct
elements is a nonzero element of `GF(4)`, hence a cube root of unity, so every
edge equation holds; yet `K₄` has no proper three-coloring.
-/

namespace PCP.Algebraic.ThreeColorAlgebra

variable {F V : Type*} [Field F]

/-- The three field elements representing the ordinary finite color set. -/
def colorValue (ω : F) (i : Fin 3) : F := ω ^ i.val

theorem colorValue_injective {ω : F} (hω : IsPrimitiveRoot ω 3) :
    Function.Injective (colorValue ω) := by
  intro i j hij
  exact Fin.ext (hω.pow_inj i.isLt j.isLt hij)

theorem colorValue_cube {ω : F} (hω : IsPrimitiveRoot ω 3) (i : Fin 3) :
    colorValue ω i ^ 3 = 1 := by
  rw [colorValue, ← pow_mul, Nat.mul_comm, pow_mul, hω.pow_eq_one, one_pow]

/-- The three chosen colors exhaust the solutions of the vertex equation. -/
theorem cube_eq_one_iff {ω : F} (hω : IsPrimitiveRoot ω 3) (x : F) :
    x ^ 3 = 1 ↔ ∃ i : Fin 3, colorValue ω i = x := by
  constructor
  · intro hx
    obtain ⟨i, hi, he⟩ := hω.eq_pow_of_pow_eq_one hx
    exact ⟨⟨i, hi⟩, he⟩
  · rintro ⟨i, rfl⟩
    exact colorValue_cube hω i

variable [CharP F 2]

/-- Frobenius fixes the difference of two cubic roots. -/
theorem sub_fourth_eq_self {a b : F} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a - b) ^ 4 = a - b := by
  have h := sub_pow_char_pow a b 2
  norm_num only at h
  rw [h, show (4 : ℕ) = 3 + 1 from rfl, pow_succ a 3, pow_succ b 3,
    ha, hb, one_mul, one_mul]

/-- For valid colors, the edge cubic equation is exactly inequality. -/
theorem sub_cube_eq_one_iff_ne {a b : F} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a - b) ^ 3 = 1 ↔ a ≠ b := by
  constructor
  · intro h he
    simp [he] at h
  · intro hne
    apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
    calc
      (a - b) * (a - b) ^ 3 = (a - b) ^ 4 := by ring
      _ = a - b := sub_fourth_eq_self ha hb
      _ = (a - b) * 1 := (mul_one _).symm

/-- Both algebraic constraints, with edge constraints imposed only on actual edges. -/
def Satisfies (G : SimpleGraph V) (f : V → F) : Prop :=
  (∀ v, f v ^ 3 - 1 = 0) ∧ ∀ v w, G.Adj v w → (f v - f w) ^ 3 - 1 = 0

theorem satisfies_iff (G : SimpleGraph V) (f : V → F) :
    Satisfies G f ↔ (∀ v, f v ^ 3 = 1) ∧ ∀ v w, G.Adj v w → f v ≠ f w := by
  simp only [Satisfies, sub_eq_zero]
  constructor
  · rintro ⟨hv, he⟩
    exact ⟨hv, fun v w h => (sub_cube_eq_one_iff_ne (hv v) (hv w)).mp (he v w h)⟩
  · rintro ⟨hv, he⟩
    exact ⟨hv, fun v w h => (sub_cube_eq_one_iff_ne (hv v) (hv w)).mpr (he v w h)⟩

/-- A usual proper three-coloring supplies the required field assignment. -/
theorem satisfies_colorValue {ω : F} (hω : IsPrimitiveRoot ω 3)
    (G : SimpleGraph V) (C : G.Coloring (Fin 3)) :
    Satisfies G (fun v => colorValue ω (C v)) := by
  apply (satisfies_iff G _).mpr
  exact ⟨fun v => colorValue_cube hω (C v), fun _ _ he h =>
    C.valid he (colorValue_injective hω h)⟩

/-- The two cubic constraint families characterize standard graph three-colorability. -/
theorem colorable_iff_exists_satisfies {ω : F} (hω : IsPrimitiveRoot ω 3)
    (G : SimpleGraph V) : G.Colorable 3 ↔ ∃ f : V → F, Satisfies G f := by
  constructor
  · rintro ⟨C⟩
    exact ⟨fun v => colorValue ω (C v), satisfies_colorValue hω G C⟩
  · rintro ⟨f, hf⟩
    obtain ⟨hv, he⟩ := (satisfies_iff G f).mp hf
    choose C hC using fun v => (cube_eq_one_iff hω (f v)).mp (hv v)
    refine ⟨SimpleGraph.Coloring.mk C ?_⟩
    intro v w hvw hc
    apply he v w hvw
    rw [← hC v, ← hC w, hc]

end PCP.Algebraic.ThreeColorAlgebra
