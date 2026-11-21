import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Abel

open Set
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Cauchy–Green operator (K=F^*F) of (4.1). -/
noncomputable def kineticForm (F : E →L[ℝ] E) : E →L[ℝ] E :=
  F.adjoint.comp F

/-- The pulled-back skew coefficient (Omega=F^*(M^*-M)F) of (4.1). -/
noncomputable def vorticityForm (F M : E →L[ℝ] E) : E →L[ℝ] E :=
  F.adjoint.comp ((M.adjoint - M).comp F)

theorem kineticForm_identity : kineticForm (ContinuousLinearMap.id ℝ E) =
    ContinuousLinearMap.id ℝ E := by
  simp only [kineticForm, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.comp_id]

theorem isSelfAdjoint_kineticForm (F : E →L[ℝ] E) : IsSelfAdjoint (kineticForm F) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [kineticForm]

theorem inner_kineticForm_self (F : E →L[ℝ] E) (v : E) :
    ⟪kineticForm F v, v⟫_ℝ = ‖F v‖ ^ 2 := by
  rw [kineticForm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]

theorem norm_kineticForm (F : E →L[ℝ] E) : ‖kineticForm F‖ = ‖F‖ ^ 2 := by
  rw [kineticForm, ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

/-- If (G=F^{-1}), then (GG^*) is an explicit two-sided inverse of (K). -/
theorem kineticForm_inverse {F G : E →L[ℝ] E}
    (hGF : G.comp F = ContinuousLinearMap.id ℝ E)
    (hFG : F.comp G = ContinuousLinearMap.id ℝ E) :
    (G.comp G.adjoint).comp (kineticForm F) = ContinuousLinearMap.id ℝ E ∧
      (kineticForm F).comp (G.comp G.adjoint) = ContinuousLinearMap.id ℝ E := by
  constructor
  · calc
      (G.comp G.adjoint).comp (kineticForm F) =
          G.comp ((G.adjoint.comp F.adjoint).comp F) := by
        simp only [kineticForm, ContinuousLinearMap.comp_assoc]
      _ = ContinuousLinearMap.id ℝ E := by
        rw [← ContinuousLinearMap.adjoint_comp, hFG, ContinuousLinearMap.adjoint_id,
          ContinuousLinearMap.id_comp, hGF]
  · calc
      (kineticForm F).comp (G.comp G.adjoint) =
          F.adjoint.comp ((F.comp G).comp G.adjoint) := by
        simp only [kineticForm, ContinuousLinearMap.comp_assoc]
      _ = ContinuousLinearMap.id ℝ E := by
        rw [hFG, ContinuousLinearMap.id_comp, ← ContinuousLinearMap.adjoint_comp, hGF,
          ContinuousLinearMap.adjoint_id]

theorem norm_kineticForm_inverse (G : E →L[ℝ] E) : ‖G.comp G.adjoint‖ = ‖G‖ ^ 2 := by
  simpa only [kineticForm, ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] using
    norm_kineticForm G.adjoint

/-- The pointwise ellipticity (D_-^{-2}), from the bound on the inverse deformation. -/
theorem kineticForm_elliptic {F G : E →L[ℝ] E} {D : ℝ} (hD : 0 < D)
    (hGF : G.comp F = ContinuousLinearMap.id ℝ E) (hG : ‖G‖ ≤ D) (v : E) :
    (D ^ 2)⁻¹ * ‖v‖ ^ 2 ≤ ⟪kineticForm F v, v⟫_ℝ := by
  have hv : G (F v) = v := DFunLike.congr_fun hGF v
  have hnorm : ‖v‖ ≤ D * ‖F v‖ := calc
    ‖v‖ = ‖G (F v)‖ := congrArg norm hv.symm
    _ ≤ ‖G‖ * ‖F v‖ := G.le_opNorm (F v)
    _ ≤ D * ‖F v‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  rw [inner_kineticForm_self, ← div_eq_inv_mul, div_le_iff₀ (pow_pos hD 2), mul_comm,
    ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem kineticForm_quadratic_upper (F : E →L[ℝ] E) (v : E) :
    ⟪kineticForm F v, v⟫_ℝ ≤ ‖F‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_kineticForm_self, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (F.le_opNorm v) 2

theorem adjoint_vorticityForm (F M : E →L[ℝ] E) :
    (vorticityForm F M).adjoint = -vorticityForm F M := by
  simp only [vorticityForm, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    map_sub, ← neg_sub (M.adjoint), ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.comp_assoc]

/-- The time derivative of (K) with the vorticity term as in (4.2). -/
theorem hasDerivWithinAt_kineticForm {F : ℝ → E →L[ℝ] E} {M : E →L[ℝ] E}
    {s : Set ℝ} {t : ℝ} (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt (fun r => kineticForm (F r))
      (vorticityForm (F t) M + (2 : ℝ) • (F t).adjoint.comp (M.comp (F t))) s t := by
  let A : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toLinearIsometry.toContinuousLinearMap
  have hA : HasDerivWithinAt (fun r => (F r).adjoint) (M.comp (F t)).adjoint s t :=
    A.hasFDerivAt.comp_hasDerivWithinAt t hF
  refine (hA.clm_comp hF).congr_deriv ?_
  simp only [vorticityForm, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, two_smul]
  abel

/-- The identity (K_t-Omega=2F^*F_t) from (4.2). -/
theorem derivWithin_kineticForm_sub_vorticity {F : ℝ → E →L[ℝ] E} {M : E →L[ℝ] E}
    {s : Set ℝ} {t : ℝ} (hs : UniqueDiffWithinAt ℝ s t)
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    derivWithin (fun r => kineticForm (F r)) s t - vorticityForm (F t) M =
      (2 : ℝ) • (F t).adjoint.comp (derivWithin F s t) := by
  rw [(hasDerivWithinAt_kineticForm hF).derivWithin hs, hF.derivWithin hs]
  abel

end TorusEuler
