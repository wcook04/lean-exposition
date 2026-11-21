import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.PressureMollifyAux
import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal

namespace TimeIdentity

open Breakdown.Internal

private theorem differentiable_of {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

private theorem contDiff_fderiv_apply_of {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) (a : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y a) :=
  (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

private theorem sum_coord (y : Space) : ∑ i, y i • unitVector i = y := by
  ext j
  simp [unitVector, Pi.single_apply]

private theorem integrable_of_vanish {F : Space → ℝ} (hF : Continuous F) {Φ : Space → Space}
    (hc : HasCompactSupport Φ) (h : ∀ x, x ∉ tsupport Φ → F x = 0) : Integrable F :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hc h)

private theorem integral_fderiv_eq_zero {h : Space → ℝ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (a : Space) : ∫ x, fderiv ℝ h x a = 0 := by
  have := PressureMollify.integral_mul_fderiv (f := fun _ => (1 : ℝ)) contDiff_const hh hc a
  simpa using this

private theorem integral_sum_fderiv_eq_zero {h : Fin 3 → Space → ℝ}
    (hh : ∀ i, ContDiff ℝ ∞ (h i)) (hc : ∀ i, HasCompactSupport (h i)) :
    ∫ x, ∑ i, fderiv ℝ (h i) x (unitVector i) = 0 := by
  rw [integral_finsetSum _ fun i _ => ((PressureMollify.contDiff_fderiv_apply (hh i) _).continuous
    ).integrable_of_hasCompactSupport (PressureMollify.hasCompactSupport_fderiv_apply (hc i) _)]
  simp [integral_fderiv_eq_zero (hh _) (hc _)]

private theorem vanish_off {Φ : Space → Space} {x : Space} (hx : x ∉ tsupport Φ) :
    Φ x = 0 ∧ fderiv ℝ Φ x = 0 :=
  ⟨image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx⟩

private theorem advection_identity {w Φ : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x, divergenceAt w x = 0) (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    ∫ x, inner ℝ (advectionAt w x) (Φ x) =
      -∫ x, ∑ i, ∑ j, w x i * w x j * fderiv ℝ Φ x (unitVector i) j := by
  set h : Fin 3 → Space → ℝ := fun i y => w y i * inner ℝ (w y) (Φ y) with hh
  have hhs : ∀ i, ContDiff ℝ ∞ (h i) := fun i =>
    (PressureMollify.contDiff_component hw i).mul (hw.inner ℝ hΦ)
  have hhc : ∀ i, HasCompactSupport (h i) := fun i => HasCompactSupport.intro hc fun x hx => by
    simp [hh, (vanish_off hx).1]
  have hadv : ∀ x, inner ℝ (advectionAt w x) (Φ x) =
      ∑ i, w x i * inner ℝ (fderiv ℝ w x (unitVector i)) (Φ x) := by
    intro x
    have e : advectionAt w x = ∑ i, w x i • fderiv ℝ w x (unitVector i) := by
      unfold advectionAt
      conv_lhs => rw [← sum_coord (w x)]
      simp [map_sum, map_smul]
    rw [e, sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  have hpt : ∀ x, inner ℝ (advectionAt w x) (Φ x) +
      ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i)) =
      ∑ i, fderiv ℝ (h i) x (unitVector i) := by
    intro x
    have hd : ∀ i, fderiv ℝ (h i) x (unitVector i) =
        w x i * (inner ℝ (w x) (fderiv ℝ Φ x (unitVector i)) +
          inner ℝ (fderiv ℝ w x (unitVector i)) (Φ x)) +
        inner ℝ (w x) (Φ x) * fderiv ℝ w x (unitVector i) i := by
      intro i
      have e : h i = fun y => w y i * inner ℝ (w y) (Φ y) := rfl
      rw [e, fderiv_fun_mul ((differentiable_of (PressureMollify.contDiff_component hw i)) x)
        (((differentiable_of hw) x).inner ℝ ((differentiable_of hΦ) x))]
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [fderiv_inner_apply ℝ ((differentiable_of hw) x) ((differentiable_of hΦ) x),
        PressureMollify.fderiv_component hw i x]
    simp only [hd]
    have hdv := hdiv x
    unfold divergenceAt at hdv
    rw [hadv]
    have e2 : ∑ i, inner ℝ (w x) (Φ x) * fderiv ℝ w x (unitVector i) i = 0 := by
      rw [← Finset.mul_sum, hdv, mul_zero]
    rw [Finset.sum_add_distrib, e2, add_zero]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  have hadvc : Continuous (advectionAt w) :=
    ((contDiff_infty_iff_fderiv.1 hw).2.continuous).clm_apply hw.continuous
  have hI1 : Integrable (fun x => inner ℝ (advectionAt w x) (Φ x)) :=
    integrable_of_vanish (hadvc.inner hΦ.continuous) hc fun x hx => by simp [(vanish_off hx).1]
  have hI2 : Integrable (fun x => ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) :=
    integrable_of_vanish (continuous_finsetSum _ fun i _ =>
      (PressureMollify.continuous_component hw.continuous i).mul
        (hw.continuous.inner (contDiff_fderiv_apply_of hΦ _).continuous)) hc fun x hx => by
      simp [(vanish_off hx).2]
  have h1 : ∫ x, (inner ℝ (advectionAt w x) (Φ x) +
      ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) = 0 := by
    rw [show (fun x => inner ℝ (advectionAt w x) (Φ x) +
      ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) =
      fun x => ∑ i, fderiv ℝ (h i) x (unitVector i) from funext hpt]
    exact integral_sum_fderiv_eq_zero hhs hhc
  rw [integral_add hI1 hI2] at h1
  have e3 : (fun x => ∑ i, w x i * inner ℝ (w x) (fderiv ℝ Φ x (unitVector i))) =
      fun x => ∑ i, ∑ j, w x i * w x j * fderiv ℝ Φ x (unitVector i) j := by
    funext x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.inner_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [e3] at h1
  linarith

theorem time_identity {T : ℝ} {v : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    {F : ℝ → Space → Space} (hv : IsForcedSolutionOn T v q F) {t : ℝ} (ht : t ∈ Ioo 0 T)
    {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    (∫ x, inner ℝ (deriv (fun τ => v τ x) t) (Φ x)) + pressureDefect v q t Φ =
      -(∫ x, inner ℝ (F t x) (Φ x)) +
        (∫ x, ∑ i, ∑ j, v t x i * v t x j * fderiv ℝ Φ x (unitVector i) j) -
        stressPairing (v t) (v t) (FundSol.potential (divergenceAt Φ)) := by
  have hvt : ContDiff ℝ ∞ (v t) :=
    CutoffEnergy.contDiff_slice hv.smooth_velocity (Ioo_subset_Icc_self ht)
  have hqt : ContDiff ℝ ∞ (q t) :=
    CutoffEnergy.contDiff_slice hv.smooth_pressure (Ioo_subset_Icc_self ht)
  have hFt : ContDiff ℝ ∞ (F t) := hv.force_smooth t ht
  have hmom : ∀ x, deriv (fun τ => v τ x) t =
      -gradientAt (q t) x - advectionAt (v t) x - F t x := by
    intro x
    have h := hv.momentum t ht x
    rw [← h]
    abel
  have hdiv : ∀ x, divergenceAt (v t) x = 0 := hv.incompressible t (Ioo_subset_Icc_self ht)
  have hA := advection_identity hvt hdiv hΦ hc
  have hgc : Continuous (gradientAt (q t)) := by
    show Continuous (fun x => ∑ i : Fin 3, fderiv ℝ (q t) x (unitVector i) • unitVector i)
    exact continuous_finsetSum _ fun i _ =>
      (contDiff_fderiv_apply_of hqt _).continuous.smul continuous_const
  have hadvc : Continuous (advectionAt (v t)) :=
    ((contDiff_infty_iff_fderiv.1 hvt).2.continuous).clm_apply hvt.continuous
  have hI1 : Integrable (fun x => inner ℝ (gradientAt (q t) x) (Φ x)) :=
    integrable_of_vanish (hgc.inner hΦ.continuous) hc fun x hx => by simp [(vanish_off hx).1]
  have hI2 : Integrable (fun x => inner ℝ (advectionAt (v t) x) (Φ x)) :=
    integrable_of_vanish (hadvc.inner hΦ.continuous) hc fun x hx => by simp [(vanish_off hx).1]
  have hI3 : Integrable (fun x => inner ℝ (F t x) (Φ x)) :=
    integrable_of_vanish (hFt.continuous.inner hΦ.continuous) hc fun x hx => by
      simp [(vanish_off hx).1]
  have hD : (∫ x, inner ℝ (deriv (fun τ => v τ x) t) (Φ x)) =
      -(∫ x, inner ℝ (gradientAt (q t) x) (Φ x)) - (∫ x, inner ℝ (advectionAt (v t) x) (Φ x)) -
        ∫ x, inner ℝ (F t x) (Φ x) := by
    simp only [hmom, inner_sub_left, inner_neg_left]
    have hI1n : Integrable (fun x => -inner ℝ (gradientAt (q t) x) (Φ x)) := hI1.neg
    have hI12 : Integrable (fun x => -inner ℝ (gradientAt (q t) x) (Φ x) -
        inner ℝ (advectionAt (v t) x) (Φ x)) := hI1n.sub hI2
    rw [integral_sub hI12 hI3, integral_sub hI1n hI2, integral_neg]
  unfold pressureDefect
  rw [hD, hA]
  ring

end TimeIdentity

end FracInternal

theorem forcedTimeIdentity : ForcedTimeIdentityStatement := by
  intro T v q F hv t ht Φ hΦ hc
  exact FracInternal.TimeIdentity.time_identity hv ht hΦ hc

end Breakdown
