/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Hadamard
import PCP.Algebraic.BinaryPolynomialEmbedding
import PCP.Algebraic.FiniteDistance
import Mathlib.Data.Fintype.EquivFin

/-!
# Affine and homogeneous Hadamard query sampling

Every degree-one query has a unique constant bit and homogeneous coefficient
vector. Uniform affine sampling therefore assigns half its mass to homogeneous
queries. Restricting arbitrary received answers to the latter can at most double
their normalized disagreement. This includes zero variables and places no
linearity or correctness assumptions on the received answers.
-/

namespace PCP.Algebraic.Hadamard

open Finset BinaryPolynomialSpace

variable {t r : ℕ}

/-- Changing the degree bound preserves the homogeneous query indexed by `w`. -/
@[simp] theorem embed_homogeneousIndex (hr : 1 ≤ r) (w : Fin t → ZMod 2) :
    embed hr (homogeneousIndex (le_refl 1) w) = homogeneousIndex hr w := by
  apply polynomial_injective
  simp only [polynomial_embed, polynomial_homogeneousIndex]

private theorem affineQuery_injective : Function.Injective
    (fun p : ZMod 2 × (Fin t → ZMod 2) =>
      constant (r := 1) p.1 + homogeneousIndex (le_refl 1) p.2) := by
  rintro ⟨b, w⟩ ⟨d, v⟩ h
  have hbd := congrArg (encode 1 (0 : Fin t → ZMod 2)) h
  simp only [map_add, encode_constant, encode_homogeneousIndex, linearEncode_apply,
    Pi.zero_apply, zero_mul, sum_const_zero, add_zero] at hbd
  apply Prod.ext hbd
  apply homogeneousIndex_injective (le_refl 1)
  exact add_left_cancel (by simpa only [hbd] using h)

/-- Affine queries are parametrized by a constant bit and a homogeneous label. -/
noncomputable def affineQueryEquiv (t : ℕ) :
    (ZMod 2 × (Fin t → ZMod 2)) ≃ Coefficients t 1 :=
  Equiv.ofBijective
    (fun p => constant p.1 + homogeneousIndex (le_refl 1) p.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨affineQuery_injective, by
      simp [card_monomials, sum_range_succ, pow_add]⟩)

@[simp] theorem affineQueryEquiv_apply (b : ZMod 2) (w : Fin t → ZMod 2) :
    affineQueryEquiv t (b, w) = constant b + homogeneousIndex (le_refl 1) w := rfl

@[simp] theorem embed_affineQueryEquiv (hr : 1 ≤ r)
    (b : ZMod 2) (w : Fin t → ZMod 2) :
    embed hr (affineQueryEquiv t (b, w)) = constant b + homogeneousIndex hr w := by
  simp only [affineQueryEquiv_apply, map_add, embed_constant, embed_homogeneousIndex]

/-- A homogeneous slice has at most twice the error fraction of the affine space. -/
theorem homogeneousDistance_le_twice_affine (hr : 1 ≤ r)
    (H G : Coefficients t r → ZMod 2) :
    relativeDistance (H ∘ homogeneousIndex hr) (G ∘ homogeneousIndex hr) ≤
      2 * relativeDistance (H ∘ embed hr) (G ∘ embed hr) := by
  have hdist := relativeDistance_comp_equiv (affineQueryEquiv t)
    (H ∘ embed hr) (G ∘ embed hr)
  rw [← hdist, relativeDistance_prod]
  change relativeDistance (fun w => H (homogeneousIndex hr w))
    (fun w => G (homogeneousIndex hr w)) ≤ _
  have hslice := single_le_sum
    (fun b (_ : b ∈ (univ : Finset (ZMod 2))) =>
      relativeDistance_nonneg
        (fun w => (H ∘ embed hr) (affineQueryEquiv t (b, w)))
        (fun w => (G ∘ embed hr) (affineQueryEquiv t (b, w))))
    (mem_univ (0 : ZMod 2))
  simp only [Function.comp_apply, embed_affineQueryEquiv, constant, Pi.single_zero,
    zero_add] at hslice ⊢
  norm_num only [ZMod.card, Nat.cast_ofNat] at *
  linarith

end PCP.Algebraic.Hadamard
