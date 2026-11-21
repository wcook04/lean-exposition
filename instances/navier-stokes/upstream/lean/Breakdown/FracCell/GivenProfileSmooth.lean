import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.GivenProfileSmoothField

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem profile_fun_eq {k : ℕ} (D : ProfileData k) (p : Fin k → ℝ) :
    D.profile p = fun y => ∑ μ ∈ D.index, ProfileData.monomialOf p μ • fieldOf D.chart (D.part μ) (D.phase p) y :=
  rfl

private theorem profile_contDiff {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (p : Fin k → ℝ) :
    ContDiff ℝ 1 (D.profile p) := by
  rw [profile_fun_eq]
  exact ContDiff.sum fun μ hμ =>
    (FracInternal.fieldOf_contDiff hD.chart (hD.parts μ hμ) (D.phase p)).const_smul (ProfileData.monomialOf p μ)

private theorem parts_differentiable {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (p : Fin k → ℝ) :
    ∀ μ ∈ D.index, Differentiable ℝ (fieldOf D.chart (D.part μ) (D.phase p)) := fun μ hμ =>
  (FracInternal.fieldOf_contDiff hD.chart (hD.parts μ hμ) _).differentiable (by norm_num)

theorem profile_smooth_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ∀ p ∈ box d.radius, ContDiff ℝ 1 (d.profile p) := by
  intro p _
  rw [hd.profile_eq]
  exact profile_contDiff D hD p

theorem profile_second_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ∀ p ∈ box d.radius, IsWeakSecondDerivOf (d.gradProfile p) (d.profileSecond p) ∧
      AEStronglyMeasurable (d.profileSecond p) volume := by
  intro p _
  have hG : d.gradProfile p = fderiv ℝ (D.profile p) := by
    funext y
    simp only [FracCertData.gradProfile, hd.profile_eq]
  have hH : d.profileSecond p = fderiv ℝ (fderiv ℝ (D.profile p)) := by
    rw [hd.second_eq]
    rfl
  rw [hG, hH]
  apply FracInternal.weakSecond_of_slopeOn
  rw [profile_fun_eq, FracInternal.fderiv_finset_sum_smul _ _ _ (parts_differentiable D hD p)]
  exact FracInternal.slopeOn_finset_sum _ _ _ fun μ hμ =>
    FracInternal.fieldOf_fderiv_slopeOn hD.chart (hD.parts μ hμ) _

theorem profile_divergence_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ∀ p ∈ box d.radius, ∀ y, divergenceAt (d.profile p) y = 0 := by
  intro p _ y
  rw [hd.profile_eq, profile_fun_eq, FracInternal.divergenceAt_finset_sum _ _ _ (parts_differentiable D hD p)]
  exact Finset.sum_eq_zero fun μ hμ => by
    rw [FracInternal.fieldOf_divergence hD.chart (hD.parts μ hμ) _ y, mul_zero]

theorem profile_class_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ∀ p ∈ box d.radius, IsClassField d.order (d.profile p) := by
  intro p _
  rw [hd.profile_eq, hd.order_eq, profile_fun_eq]
  exact FracInternal.classField_finset_sum _ _ _ _ fun μ hμ =>
    ⟨FracInternal.fieldOf_turn hD.chart (hD.parts μ hμ) _, FracInternal.fieldOf_mirror hD.chart (hD.parts μ hμ) _⟩

end GivenFields

end CellCert

end Breakdown
