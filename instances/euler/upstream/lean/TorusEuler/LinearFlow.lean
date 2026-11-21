/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

Adapted from `CCPoint/Framework/ODE/LinearODE.lean` in
`sources/ccpoint-lean`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.ODE.ExistUnique

open Set
open scoped NNReal

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two solutions of a continuous linear ODE on an interval agree everywhere
if they agree at any time in the interval. -/
theorem linearODE_unique_of_mem {A : ℝ → E →L[ℝ] E} {J : Set ℝ}
    (hJ : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hA : ContinuousOn A J)
    {x y : ℝ → E} (hx : ∀ t ∈ J, HasDerivWithinAt x (A t (x t)) J t)
    (hy : ∀ t ∈ J, HasDerivWithinAt y (A t (y t)) J t) (h₀ : x t₀ = y t₀) :
    EqOn x y J := by
  intro t ht
  have hsub : uIcc t₀ t ⊆ J := hJ.uIcc_subset ht₀ ht
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn (hA.mono hsub)
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hLip : ∀ r ∈ uIcc t₀ t, LipschitzOnWith K (A r) univ := by
    intro r hr
    refine (LipschitzWith.of_dist_le_mul fun p q => ?_).lipschitzOnWith
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((A r).le_opNorm (p - q)).trans
      (mul_le_mul_of_nonneg_right ((hC r hr).trans (le_max_left _ _)) (norm_nonneg _))
  rcases le_total t₀ t with hle | hle
  · rw [uIcc_of_le hle] at hsub hLip
    exact ODE_solution_unique_of_mem_Icc_right (v := fun r z => A r z)
      (fun r hr => hLip r (Ico_subset_Icc_self hr))
      (fun r hr => ((hx r (hsub hr)).mono hsub).continuousWithinAt)
      (fun r hr => ((hx r (hsub (Ico_subset_Icc_self hr))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hr))
      (fun _ _ => mem_univ _)
      (fun r hr => ((hy r (hsub hr)).mono hsub).continuousWithinAt)
      (fun r hr => ((hy r (hsub (Ico_subset_Icc_self hr))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hr))
      (fun _ _ => mem_univ _) h₀ ⟨hle, le_rfl⟩
  · rw [uIcc_of_ge hle] at hsub hLip
    exact ODE_solution_unique_of_mem_Icc_left (v := fun r z => A r z)
      (fun r hr => hLip r (Ioc_subset_Icc_self hr))
      (fun r hr => ((hx r (hsub hr)).mono hsub).continuousWithinAt)
      (fun r hr => ((hx r (hsub (Ioc_subset_Icc_self hr))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem hr))
      (fun _ _ => mem_univ _)
      (fun r hr => ((hy r (hsub hr)).mono hsub).continuousWithinAt)
      (fun r hr => ((hy r (hsub (Ioc_subset_Icc_self hr))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem hr))
      (fun _ _ => mem_univ _) h₀ ⟨le_rfl, hle⟩

/-- A solution of a homogeneous linear ODE that is nonzero at one time is
nonzero throughout its interval of definition. -/
theorem linearODE_ne_zero_of_mem {A : ℝ → E →L[ℝ] E} {J : Set ℝ}
    (hJ : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hA : ContinuousOn A J)
    {x : ℝ → E} (hx : ∀ t ∈ J, HasDerivWithinAt x (A t (x t)) J t)
    (h₀ : x t₀ ≠ 0) : ∀ t ∈ J, x t ≠ 0 := by
  intro t ht hxt
  have hzero : ∀ r ∈ J, HasDerivWithinAt (fun _ => (0 : E)) (A r 0) J r := by
    intro r _
    simpa only [map_zero] using hasDerivWithinAt_const r J (0 : E)
  exact h₀ (linearODE_unique_of_mem hJ ht hA hx hzero hxt ht₀)

/-- A normalized solution of the inverse equation is a left inverse of a
normalized fundamental solution at every time in the interval. -/
theorem linearODE_inv_comp_fundamental {A : ℝ → E →L[ℝ] E} {J : Set ℝ}
    (hJ : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J) {Φ Ψ : ℝ → E →L[ℝ] E}
    (hΦ : ∀ t ∈ J, HasDerivWithinAt Φ ((A t).comp (Φ t)) J t)
    (hΨ : ∀ t ∈ J, HasDerivWithinAt Ψ (-((Ψ t).comp (A t))) J t)
    (hΦ₀ : Φ t₀ = ContinuousLinearMap.id ℝ E) (hΨ₀ : Ψ t₀ = ContinuousLinearMap.id ℝ E) :
    ∀ t ∈ J, (Ψ t).comp (Φ t) = ContinuousLinearMap.id ℝ E := by
  have hd : ∀ t ∈ J, HasDerivWithinAt (fun r => (Ψ r).comp (Φ r)) (0 : E →L[ℝ] E) J t := by
    intro t ht
    refine ((hΨ t ht).clm_comp (hΦ t ht)).congr_deriv ?_
    rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc, neg_add_cancel]
  exact linearODE_unique_of_mem (A := fun _ => 0) hJ ht₀ continuousOn_const
    (by simpa only [zero_apply] using hd)
    (fun t _ => by simpa only [zero_apply] using
      hasDerivWithinAt_const t J (ContinuousLinearMap.id ℝ E)) (by simp [hΦ₀, hΨ₀])

/-- A normalized fundamental solution is a left inverse of a normalized
solution of the inverse equation at every time in the interval. -/
theorem linearODE_fundamental_comp_inv {A : ℝ → E →L[ℝ] E} {J : Set ℝ}
    (hJ : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hA : ContinuousOn A J)
    {Φ Ψ : ℝ → E →L[ℝ] E}
    (hΦ : ∀ t ∈ J, HasDerivWithinAt Φ ((A t).comp (Φ t)) J t)
    (hΨ : ∀ t ∈ J, HasDerivWithinAt Ψ (-((Ψ t).comp (A t))) J t)
    (hΦ₀ : Φ t₀ = ContinuousLinearMap.id ℝ E) (hΨ₀ : Ψ t₀ = ContinuousLinearMap.id ℝ E) :
    ∀ t ∈ J, (Φ t).comp (Ψ t) = ContinuousLinearMap.id ℝ E := by
  let M (t : ℝ) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    ContinuousLinearMap.compL ℝ E E E (A t) - (ContinuousLinearMap.compL ℝ E E E).flip (A t)
  have hM_apply (t : ℝ) (B : E →L[ℝ] E) : M t B = (A t).comp B - B.comp (A t) := by
    simp only [M, sub_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply]
  have hM : ContinuousOn M J :=
    ((ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA).sub
      ((ContinuousLinearMap.compL ℝ E E E).flip.continuous.comp_continuousOn hA)
  have hd : ∀ t ∈ J, HasDerivWithinAt (fun r => (Φ r).comp (Ψ r)) (M t ((Φ t).comp (Ψ t))) J t := by
    intro t ht
    refine ((hΦ t ht).clm_comp (hΨ t ht)).congr_deriv ?_
    rw [hM_apply, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc, sub_eq_add_neg]
  have hId : ∀ t ∈ J, HasDerivWithinAt (fun _ => ContinuousLinearMap.id ℝ E)
      (M t (ContinuousLinearMap.id ℝ E)) J t := by
    intro t _
    simpa [hM_apply] using hasDerivWithinAt_const t J (ContinuousLinearMap.id ℝ E)
  exact linearODE_unique_of_mem hJ ht₀ hM hd hId (by simp [hΦ₀, hΨ₀])

end TorusEuler
