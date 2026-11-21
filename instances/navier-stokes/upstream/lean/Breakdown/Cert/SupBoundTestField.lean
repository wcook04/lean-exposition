import Breakdown.FreqTr.EmbedNegSsp
import Breakdown.Cert.SupBoundReal
import Breakdown.Cert.SupBoundRadial

open MeasureTheory Real
open scoped ContDiff

noncomputable section

namespace Breakdown

open LineDeriv FourierTransform SchwartzMap

namespace Internal.SupBoundTestField

open Breakdown.Freq Breakdown.Freq.Internal.EmbedNegSsp

theorem norm_complexifyVec (v : Space) : ‖complexifyVec v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [complexifyVec]

def toRapid {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : 𝓢(Space, CSpace) :=
  HasCompactSupport.toSchwartzMap (f := fun x => complexifyVec (u x))
    (hc.comp_left (map_zero complexifyVec)) (complexifyVec.contDiff.comp hu)

theorem coe_toRapid {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ⇑(toRapid hu hc) = fun x => complexifyVec (u x) := rfl

theorem norm_le_integral (S : 𝓢(Space, CSpace)) (x : Space) : ‖S x‖ ≤ ∫ ξ, ‖𝓕 S ξ‖ := by
  have h : S x = 𝓕⁻ (𝓕 S) x := by rw [fourierInv_fourier_eq]
  rw [h, fourierInv_coe, fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

theorem sum_sq_coord (ξ : Space) : ∑ k : Fin 3, (ξ k) ^ 2 = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_sq_transform_partialDeriv (S : 𝓢(Space, CSpace)) (k : Fin 3) (ξ : Space) :
    ‖𝓕 (∂_{unitVector k} S) ξ‖ ^ 2 = 4 * π ^ 2 * (ξ k) ^ 2 * ‖𝓕 S ξ‖ ^ 2 := by
  rw [freqTr_pd_apply, norm_smul, mul_pow]
  congr 1
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [mul_one, mul_pow, mul_pow, sq_abs]
  ring

theorem sum_norm_sq_transform_partialDeriv (S : 𝓢(Space, CSpace)) (ξ : Space) :
    ∑ k : Fin 3, ‖𝓕 (∂_{unitVector k} S) ξ‖ ^ 2 = 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 S ξ‖ ^ 2 := by
  simp_rw [norm_sq_transform_partialDeriv]
  rw [← sum_sq_coord, Finset.mul_sum, Finset.sum_mul]

def sspS (S : 𝓢(Space, CSpace)) : 𝓢(Space, CSpace) :=
  ∑ k : Fin 3, ∂_{unitVector k} (∂_{unitVector k} S)

theorem coord_sq_complex (ξ : Space) (k : Fin 3) :
    (2 * π * Complex.I * ((ξ k : ℝ) : ℂ)) * (2 * π * Complex.I * ((ξ k : ℝ) : ℂ)) =
      ((-(4 * π ^ 2 * (ξ k) ^ 2) : ℝ) : ℂ) := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem transform_sspS (S : 𝓢(Space, CSpace)) (ξ : Space) :
    𝓕 (sspS S) ξ = ((-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) • 𝓕 S ξ := by
  rw [sspS, fourier_sum, sum_apply]
  simp_rw [freqTr_pd_apply, smul_smul, coord_sq_complex]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, ← sum_sq_coord, Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem norm_sq_transform_sspS (S : 𝓢(Space, CSpace)) (ξ : Space) :
    ‖𝓕 (sspS S) ξ‖ ^ 2 = 16 * π ^ 4 * ‖ξ‖ ^ 4 * ‖𝓕 S ξ‖ ^ 2 := by
  rw [transform_sspS, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity)]
  ring

theorem integrable_norm_sq (S : 𝓢(Space, CSpace)) : Integrable (fun x => ‖S x‖ ^ 2) := by
  have h : MemLp S ((2 : ℕ) : ENNReal) volume := by simpa using S.memLp 2
  exact h.integrable_norm_pow two_ne_zero

theorem coe_pd_toRapid {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (k : Fin 3) :
    ⇑(∂_{unitVector k} (toRapid hu hc) : 𝓢(Space, CSpace)) = fun x => complexifyVec (pd u k x) :=
  coe_lineDeriv_eq (differentiable_of_smooth hu) (coe_toRapid hu hc) k

theorem coe_sspS_toRapid {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ⇑(sspS (toRapid hu hc)) = fun x => complexifyVec (sumSecondPartialsAt u x) := by
  funext x
  rw [sspS, sum_apply, sumSecondPartialsAt_eq hu, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coe_lineDeriv_eq (differentiable_of_smooth (contDiff_pd hu k)) (coe_pd_toRapid hu hc k) k]

theorem integral_grad_eq {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∫ y, ∑ i : Fin 3, ‖fderiv ℝ u y (unitVector i)‖ ^ 2 =
      ∫ ξ, ∑ k : Fin 3, ‖𝓕 (∂_{unitVector k} (toRapid hu hc)) ξ‖ ^ 2 := by
  have e : ∀ y, ∑ i : Fin 3, ‖fderiv ℝ u y (unitVector i)‖ ^ 2 =
      ∑ i : Fin 3, ‖(∂_{unitVector i} (toRapid hu hc) : 𝓢(Space, CSpace)) y‖ ^ 2 := by
    intro y
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_pd_toRapid hu hc i, norm_complexifyVec]
    rfl
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_norm_sq _,
    integral_finsetSum _ fun i _ => integrable_norm_sq _]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (integral_norm_sq_fourier _).symm

theorem integral_ssp_eq {u : Space → Space} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∫ y, ‖sumSecondPartialsAt u y‖ ^ 2 = ∫ ξ, ‖𝓕 (sspS (toRapid hu hc)) ξ‖ ^ 2 := by
  have e : ∀ y, ‖sumSecondPartialsAt u y‖ ^ 2 = ‖(sspS (toRapid hu hc)) y‖ ^ 2 := by
    intro y
    rw [coe_sspS_toRapid hu hc, norm_complexifyVec]
  simp_rw [e]
  exact (integral_norm_sq_fourier _).symm

theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  rw [ae_iff]
  simp

end Internal.SupBoundTestField

open Internal.SupBoundTestField in
theorem supBound_test_field (u : Space → Space) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (x : Space) :
    ‖u x‖ ^ 2 ≤ (1 / (2 * Real.pi)) *
      Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ u y (unitVector i)‖ ^ 2) *
      Real.sqrt (∫ y, ‖sumSecondPartialsAt u y‖ ^ 2) := by
  set S := toRapid hu hc with hS
  have hx : ‖u x‖ ≤ ∫ ξ, ‖𝓕 S ξ‖ := by
    rw [← norm_complexifyVec]
    exact norm_le_integral S x
  have iG : Integrable (fun ξ : Space => 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 S ξ‖ ^ 2) := by
    have h := integrable_finsetSum (Finset.univ : Finset (Fin 3))
      fun k _ => integrable_norm_sq (𝓕 (∂_{unitVector k} S))
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact sum_norm_sq_transform_partialDeriv S ξ
  have iL : Integrable (fun ξ : Space => 16 * π ^ 4 * ‖ξ‖ ^ 4 * ‖𝓕 S ξ‖ ^ 2) :=
    (integrable_norm_sq (𝓕 (sspS S))).congr
      (Filter.Eventually.of_forall fun ξ => norm_sq_transform_sspS S ξ)
  have hI : ∫ y, ∑ i : Fin 3, ‖fderiv ℝ u y (unitVector i)‖ ^ 2 =
      ∫ ξ, 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 S ξ‖ ^ 2 := by
    rw [integral_grad_eq hu hc]
    simp_rw [sum_norm_sq_transform_partialDeriv]
    rfl
  have hJ : ∫ y, ‖sumSecondPartialsAt u y‖ ^ 2 = ∫ ξ, 16 * π ^ 4 * ‖ξ‖ ^ 4 * ‖𝓕 S ξ‖ ^ 2 := by
    rw [integral_ssp_eq hu hc]
    simp_rw [norm_sq_transform_sspS]
    rfl
  refine sq_le_of_forall_scale (norm_nonneg _)
    (integral_nonneg fun y => Finset.sum_nonneg fun i _ => by positivity)
    (integral_nonneg fun y => by positivity) ?_
  intro l hl t ht
  refine hx.trans ?_
  rw [hI, hJ]
  have ha : 0 < l * (4 * π ^ 2) := by positivity
  have hb : 0 < l⁻¹ * (16 * π ^ 4) := by positivity
  have iR := integrable_inv_radial ha hb
  have iW : Integrable (fun ξ : Space =>
      l * (4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 S ξ‖ ^ 2) + l⁻¹ * (16 * π ^ 4 * ‖ξ‖ ^ 4 * ‖𝓕 S ξ‖ ^ 2)) :=
    (iG.const_mul l).add (iL.const_mul l⁻¹)
  calc ∫ ξ, ‖𝓕 S ξ‖
      ≤ ∫ ξ, (t * (l * (4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 S ξ‖ ^ 2) +
          l⁻¹ * (16 * π ^ 4 * ‖ξ‖ ^ 4 * ‖𝓕 S ξ‖ ^ 2)) +
          t⁻¹ * (l * (4 * π ^ 2) * ‖ξ‖ ^ 2 + l⁻¹ * (16 * π ^ 4) * ‖ξ‖ ^ 4)⁻¹) / 2 := by
        refine integral_mono_ae (𝓕 S).integrable.norm
          (((iW.const_mul t).add (iR.const_mul t⁻¹)).div_const 2) ?_
        filter_upwards [ae_ne_zero] with ξ hξ
        have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
        have hw : 0 < l * (4 * π ^ 2) * ‖ξ‖ ^ 2 + l⁻¹ * (16 * π ^ 4) * ‖ξ‖ ^ 4 := by positivity
        have h := le_half_weighted (norm_nonneg (𝓕 S ξ)) hw ht
        refine h.trans (le_of_eq ?_)
        rw [mul_inv]
        ring
    _ = (t * (l * (∫ ξ, 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 S ξ‖ ^ 2) +
          (∫ ξ, 16 * π ^ 4 * ‖ξ‖ ^ 4 * ‖𝓕 S ξ‖ ^ 2) / l) + t⁻¹ * (1 / (4 * π))) / 2 := by
        rw [integral_div, integral_add (iW.const_mul t) (iR.const_mul t⁻¹), integral_const_mul,
          integral_const_mul, integral_add (iG.const_mul l) (iL.const_mul l⁻¹), integral_const_mul,
          integral_const_mul, integral_inv_radial ha hb, sqrt_radial_weight l hl]
        ring

end Breakdown
