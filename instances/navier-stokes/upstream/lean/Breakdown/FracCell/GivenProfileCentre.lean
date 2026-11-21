import Breakdown.FracCell.GivenProfileSmooth
import Breakdown.FracCell.GivenProfileBounds

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace GivenProfileCentreInternal

def instanceOf {k N : ℕ} (D : ProfileData k) (c : FracCellData k N) : FracCertData k N :=
  { c.toFracCertData with
    order := D.chart.m
    radius := D.radius
    rotationRate := D.rate
    multiplier := D.multiplier
    profile := D.profile
    profileSecond := D.second
    profilePower := D.powerField }

theorem instanceOf_isInstance {k N : ℕ} (D : ProfileData k) (c : FracCellData k N) :
    IsProfileInstance D (instanceOf D c) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zero_mem_box {k N : ℕ} (D : ProfileData k) (c : FracCellData k N) (hD : IsProfileData D) :
    (0 : Fin k → ℝ) ∈ box (instanceOf D c).radius := fun i => by
  simpa [instanceOf] using hD.radius_nonneg i

theorem second_symm_of_differentiable {f : Space → Space} (hf : Differentiable ℝ f) (y u w : Space) :
    fderiv ℝ (fderiv ℝ f) y u w = fderiv ℝ (fderiv ℝ f) y w u := by
  by_cases h : DifferentiableAt ℝ (fderiv ℝ f) y
  · exact second_derivative_symmetric_of_eventually
      (Filter.Eventually.of_forall fun z => (hf z).hasFDerivAt) h.hasFDerivAt u w
  · simp [fderiv_zero_of_not_differentiableAt h]

end GivenProfileCentreInternal

open GivenProfileCentreInternal

theorem centre_smooth_of {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (hD : IsProfileData D) (hc : IsCentreInstance D c) : ContDiff ℝ 1 c.centre := by
  rw [hc.centre_eq]
  exact profile_smooth_of D (instanceOf D c) hD (instanceOf_isInstance D c) 0 (zero_mem_box D c hD)

theorem centre_second_of {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (hD : IsProfileData D) (hc : IsCentreInstance D c) :
    IsWeakSecondDerivOf c.centreGrad c.centreSecond ∧ AEStronglyMeasurable c.centreSecond volume := by
  have h := profile_second_of D (instanceOf D c) hD (instanceOf_isInstance D c) 0 (zero_mem_box D c hD)
  have hg : c.centreGrad = (instanceOf D c).gradProfile 0 := by
    funext y
    simp only [FracCellData.centreGrad, FracCertData.gradProfile, hc.centre_eq]
    rfl
  rw [hg, hc.centreSecond_eq]
  exact h

theorem centre_divergence_of {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (hD : IsProfileData D) (hc : IsCentreInstance D c) : ∀ y, divergenceAt c.centre y = 0 := by
  rw [hc.centre_eq]
  exact profile_divergence_of D (instanceOf D c) hD (instanceOf_isInstance D c) 0 (zero_mem_box D c hD)

theorem centre_class_of {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (hD : IsProfileData D) (hc : IsCentreInstance D c) : IsClassField c.order c.centre := by
  rw [hc.centre_eq, hc.order_eq]
  exact profile_class_of D (instanceOf D c) hD (instanceOf_isInstance D c) 0 (zero_mem_box D c hD)

theorem centre_bounds_of {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (hD : IsProfileData D) (hc : IsCentreInstance D c) :
    ∃ C : ℝ, ∀ y, ‖c.centre y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
      ‖c.centreGrad y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧ ‖c.centreSecond y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  obtain ⟨C, hC⟩ := FracCellInternal.profile_bounds_everywhere D hD D.radius
  refine ⟨C, fun y => ?_⟩
  have h0 : (0 : Fin k → ℝ) ∈ box D.radius := zero_mem_box D c hD
  simp only [FracCellData.centreGrad, hc.centre_eq, hc.centreSecond_eq]
  exact hC 0 h0 y

theorem centreSecond_symm_of {k N : ℕ} (D : ProfileData k) (c : FracCellData k N)
    (hD : IsProfileData D) (hc : IsCentreInstance D c) :
    ∀ y (u w : Space), c.centreSecond y u w = c.centreSecond y w u := by
  intro y u w
  have hs := centre_smooth_of D c hD hc
  rw [hc.centre_eq] at hs
  rw [hc.centreSecond_eq]
  exact second_symm_of_differentiable (hs.differentiable one_ne_zero) y u w

end GivenFields

end CellCert

end Breakdown
