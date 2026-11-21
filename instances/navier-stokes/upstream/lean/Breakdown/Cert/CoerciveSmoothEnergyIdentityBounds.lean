import Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

namespace Bounds

theorem slice_of_joint (f : ℝ → Space → ℝ) (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (h0 : ∀ σ y, 0 ≤ f σ y) (hfin : periodLIntegral f < ⊤) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), Integrable (fun y => f σ y) := by
  have hm : Measurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  have hmeas : Measurable (fun σ => ∫⁻ y, ENNReal.ofReal (f σ y)) := hm.lintegral_prod_right'
  have hne : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y)) ≠ ⊤ := hfin.ne
  have hae := ae_lt_top hmeas hne
  filter_upwards [hae] with σ hσ
  have hc : Continuous (fun y => f σ y) := hf.comp (continuous_const.prodMk continuous_id)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun y => h0 σ y))]
  exact hσ

theorem joint_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → Space → E)
    (hF : ContDiff ℝ ∞ (fun z : ℝ × Space => F z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) :=
  joint_partial F hF (by simp) (by simp)

theorem joint_time (v : ℝ → Space → Space) (hv : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) := by
  have hd : Differentiable ℝ (fun z : ℝ × Space => v z.1 z.2) := hv.differentiable (by simp)
  have e : (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) =
      fun z => fderiv ℝ (fun z : ℝ × Space => v z.1 z.2) z (1, 0) := by
    funext z
    exact time_deriv_eq v hd z.1 z.2
  rw [e]
  exact (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem joint_transport (P : ℝ) (v : ℝ → Space → Space)
    (hv : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => transportPart P v z.1 z.2) := by
  have h1 := joint_time v hv
  have h2 := joint_fderiv v hv
  have e : (fun z : ℝ × Space => transportPart P v z.1 z.2) = fun z =>
      ((1 / P) • deriv (fun s => v s z.2) z.1 + (1 / 2 : ℝ) • v z.1 z.2)
        + (1 / 2 : ℝ) • fderiv ℝ (v z.1) z.2 z.2 := rfl
  rw [e]
  have h3 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 z.2) :=
    h2.clm_apply contDiff_snd
  have h4 : ContDiff ℝ ∞ (fun z : ℝ × Space => (1 / P) • deriv (fun s => v s z.2) z.1) :=
    h1.const_smul _
  have h5 : ContDiff ℝ ∞ (fun z : ℝ × Space => (1 / 2 : ℝ) • v z.1 z.2) := hv.const_smul _
  have h6 : ContDiff ℝ ∞ (fun z : ℝ × Space => (1 / 2 : ℝ) • fderiv ℝ (v z.1) z.2 z.2) :=
    h3.const_smul _
  exact (h4.add h5).add h6

end Bounds

open Bounds in
theorem slice_bounds_ae (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), SliceBounds P v σ := by
  have hs := hv.smooth
  have c0 : Continuous (fun z : ℝ × Space => v z.1 z.2) := hs.continuous
  have c1 := (joint_fderiv v hs).continuous
  have c2 := (joint_fderiv (fun σ x => fderiv ℝ (v σ) x) (joint_fderiv v hs)).continuous
  have cT := (joint_transport P v hs).continuous
  have cT1 := (joint_fderiv (transportPart P v) (joint_transport P v hs)).continuous
  have cS1 := (joint_fderiv (fun σ x => deriv (fun s => v s x) σ) (joint_time v hs)).continuous
  have cw : Continuous (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) := by
    refine (c0.norm.pow 2).div ((continuous_const.add continuous_snd.norm).pow 2) (fun z => ?_)
    positivity
  have a0 := slice_of_joint (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) cw
    (fun σ y => by positivity) hv.weighted_finite
  have e1 : ∀ σ y, ‖iteratedFDeriv ℝ 1 (v σ) y‖ ^ 2 = ‖fderiv ℝ (v σ) y‖ ^ 2 := fun σ y => by
    rw [norm_iteratedFDeriv_one]
  have e2 : ∀ σ y, ‖iteratedFDeriv ℝ 2 (v σ) y‖ ^ 2 =
      ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2 := fun σ y => by
    have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := v σ) (x := y)
    rw [norm_iteratedFDeriv_one] at h
    rw [show ‖iteratedFDeriv ℝ 2 (v σ) y‖ = ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ from h.symm]
  have eT0 : ∀ σ y, ‖iteratedFDeriv ℝ 0 (transportPart P v σ) y‖ ^ 2 = ‖transportPart P v σ y‖ ^ 2 :=
    fun σ y => by rw [norm_iteratedFDeriv_zero]
  have eT1 : ∀ σ y, ‖iteratedFDeriv ℝ 1 (transportPart P v σ) y‖ ^ 2 =
      ‖fderiv ℝ (transportPart P v σ) y‖ ^ 2 := fun σ y => by rw [norm_iteratedFDeriv_one]
  have eS1 : ∀ σ y, ‖iteratedFDeriv ℝ 1 (fun x => deriv (fun s => v s x) σ) y‖ ^ 2 =
      ‖fderiv ℝ (fun x => deriv (fun s => v s x) σ) y‖ ^ 2 := fun σ y => by rw [norm_iteratedFDeriv_one]
  have f1 := hv.derivatives_finite 1 le_rfl
  have f2 := hv.derivatives_finite 2 (by norm_num)
  have fT0 := hv.transport_finite 0
  have fT1 := hv.transport_finite 1
  have fS1 := hv.time_derivatives_finite 1 le_rfl
  simp only [e1] at f1
  simp only [e2] at f2
  simp only [eT0] at fT0
  simp only [eT1] at fT1
  simp only [eS1] at fS1
  have a1 := slice_of_joint (fun σ y => ‖fderiv ℝ (v σ) y‖ ^ 2) (c1.norm.pow 2)
    (fun σ y => by positivity) f1
  have a2 := slice_of_joint (fun σ y => ‖fderiv ℝ (fun x => fderiv ℝ (v σ) x) y‖ ^ 2) (c2.norm.pow 2)
    (fun σ y => by positivity) f2
  have aT0 := slice_of_joint (fun σ y => ‖transportPart P v σ y‖ ^ 2) (cT.norm.pow 2)
    (fun σ y => by positivity) fT0
  have aT1 := slice_of_joint (fun σ y => ‖fderiv ℝ (transportPart P v σ) y‖ ^ 2) (cT1.norm.pow 2)
    (fun σ y => by positivity) fT1
  have aS1 := slice_of_joint (fun σ y => ‖fderiv ℝ (fun x => deriv (fun s => v s x) σ) y‖ ^ 2)
    (cS1.norm.pow 2) (fun σ y => by positivity) fS1
  filter_upwards [a0, a1, a2, aT0, aT1, aS1] with σ h0 h1 h2 h3 h4 h5
  exact ⟨h0, h1, h2, h3, h4, h5⟩

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown
