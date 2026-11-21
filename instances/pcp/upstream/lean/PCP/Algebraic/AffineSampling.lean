/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.FiniteDistance
import Mathlib.Algebra.Module.Basic

/-!
# Uniform affine sampling and error bounds for sums

At a fixed center, any nonzero scalar multiple of a uniform direction is again
uniform. A sum of oracle answers can be wrong only if at least one answer is
wrong. Consequently, `n` affine samples have sum error at most `n` times the
oracle's relative distance. All samples may share the same direction; independence
between their error events is neither required nor assumed.
-/

namespace PCP.Algebraic

section Sum

variable {I Ω W : Type*} [Fintype Ω] [AddCommMonoid W] [DecidableEq W]

/-- A union bound for the error in a finite sum, even when summands are correlated. -/
theorem relativeDistance_finset_sum_le (s : Finset I) (f g : I → Ω → W) :
    relativeDistance (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, g i x) ≤
      ∑ i ∈ s, relativeDistance (f i) (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (relativeDistance_zipWith_le (fun a b : W => a + b)
      (f i) (g i) (fun x => ∑ j ∈ s, f j x) (fun x => ∑ j ∈ s, g j x)).trans
      (add_le_add le_rfl ih)

/-- The full finite-index version of the union bound for sums. -/
theorem relativeDistance_sum_le [Fintype I] (f g : I → Ω → W) :
    relativeDistance (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) ≤
      ∑ i, relativeDistance (f i) (g i) :=
  relativeDistance_finset_sum_le Finset.univ f g

end Sum

section Affine

variable {𝔽 V W : Type*} [DivisionRing 𝔽] [AddCommGroup V] [Module 𝔽 V]

/-- A nonzero affine scaling permutes all directions. -/
def affineSamplingEquiv (u : V) (a : 𝔽) (ha : a ≠ 0) : V ≃ V where
  toFun v := u + a • v
  invFun w := a⁻¹ • (w - u)
  left_inv v := by simp [smul_smul, ha]
  right_inv w := by simp [smul_smul, ha]

@[simp] theorem affineSamplingEquiv_apply (u : V) (a : 𝔽) (ha : a ≠ 0) (v : V) :
    affineSamplingEquiv u a ha v = u + a • v := rfl

@[simp] theorem affineSamplingEquiv_symm_apply (u : V) (a : 𝔽) (ha : a ≠ 0) (w : V) :
    (affineSamplingEquiv u a ha).symm w = a⁻¹ • (w - u) := rfl

/-- Each nonzero affine sample has exactly the original normalized error fraction. -/
theorem relativeDistance_affineSampling [Fintype V] [DecidableEq W]
    (u : V) (a : 𝔽) (ha : a ≠ 0) (f g : V → W) :
    relativeDistance (fun v => f (u + a • v)) (fun v => g (u + a • v)) =
      relativeDistance f g :=
  relativeDistance_comp_equiv (affineSamplingEquiv u a ha) f g

/-- A shared random direction is sufficient for the sum-error bound used in Lemma 3.4. -/
theorem relativeDistance_affine_sum_le [Fintype V] [AddCommMonoid W] [DecidableEq W]
    {I : Type*} [Fintype I] (u : V) (a : I → 𝔽) (ha : ∀ i, a i ≠ 0) (f g : V → W) :
    relativeDistance (fun v => ∑ i, f (u + a i • v))
      (fun v => ∑ i, g (u + a i • v)) ≤
        Fintype.card I * relativeDistance f g := by
  calc
    _ ≤ ∑ i, relativeDistance (fun v => f (u + a i • v))
        (fun v => g (u + a i • v)) :=
      relativeDistance_sum_le (fun i v => f (u + a i • v))
        (fun i v => g (u + a i • v))
    _ = ∑ _i : I, relativeDistance f g :=
      Finset.sum_congr rfl (fun i _ => relativeDistance_affineSampling u (a i) (ha i) f g)
    _ = _ := by simp

end Affine

end PCP.Algebraic
